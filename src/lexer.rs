use std::{fmt::Write, iter::Peekable, ops::Range, str::CharIndices};

use ariadne::{Color, Label};
use lasso::Spur;

use crate::{
    diagnostics,
    interners::Interners,
    source_file::{FileId, SourceLocation, SourceStorage},
    Width,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    ArgC,
    ArgV,
    Assert,
    BitAnd,
    BitNot,
    BitOr,
    Boolean(bool),
    CastBool,
    CastInt,
    CastPtr,
    ColonColon,
    Const,
    DivMod,
    Do,
    Drop,
    Dup(usize),
    DupPair,
    Elif,
    Else,
    End,
    Equal,
    GoesTo,
    Greater,
    GreaterEqual,
    Here(Spur),
    Ident,
    If,
    Include,
    Integer(u64),
    Is,
    Less,
    LessEqual,
    Load(Width),
    LoadPtr,
    Macro,
    Memory,
    Minus,
    NotEqual,
    Plus,
    Proc,
    Return,
    Rot,
    ShiftLeft,
    ShiftRight,
    SquareBracketClosed,
    SquareBracketOpen,
    Star,
    String { id: Spur, is_c_str: bool },
    Store(Width),
    StorePtr,
    Swap,
    SysCall(usize),
    While,
}

impl TokenKind {
    pub fn new_block(self) -> bool {
        match self {
            TokenKind::ArgC
            | TokenKind::ArgV
            | TokenKind::Assert
            | TokenKind::BitAnd
            | TokenKind::BitNot
            | TokenKind::BitOr
            | TokenKind::Boolean(_)
            | TokenKind::CastBool
            | TokenKind::CastInt
            | TokenKind::CastPtr
            | TokenKind::ColonColon
            | TokenKind::Const
            | TokenKind::DivMod
            | TokenKind::Do
            | TokenKind::Drop
            | TokenKind::Dup(_)
            | TokenKind::DupPair
            | TokenKind::Elif
            | TokenKind::Else
            | TokenKind::End
            | TokenKind::Equal
            | TokenKind::GoesTo
            | TokenKind::Greater
            | TokenKind::GreaterEqual
            | TokenKind::Here(_)
            | TokenKind::Ident
            | TokenKind::Include
            | TokenKind::Integer(_)
            | TokenKind::Less
            | TokenKind::LessEqual
            | TokenKind::Load(_)
            | TokenKind::LoadPtr
            | TokenKind::Macro
            | TokenKind::Memory
            | TokenKind::Minus
            | TokenKind::NotEqual
            | TokenKind::Plus
            | TokenKind::Proc
            | TokenKind::Return
            | TokenKind::Rot
            | TokenKind::ShiftLeft
            | TokenKind::ShiftRight
            | TokenKind::SquareBracketClosed
            | TokenKind::SquareBracketOpen
            | TokenKind::Star
            | TokenKind::String { .. }
            | TokenKind::Store(_)
            | TokenKind::StorePtr
            | TokenKind::Swap
            | TokenKind::SysCall(_) => false,

            TokenKind::If | TokenKind::Is | TokenKind::While => true,
        }
    }

    pub fn end_block(self) -> bool {
        self == TokenKind::End
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub lexeme: Spur,
    pub location: SourceLocation,
}

impl Token {
    fn new(
        kind: TokenKind,
        lexeme: Spur,
        file_id: FileId,
        source_range: Range<usize>,
        line: usize,
        column: usize,
    ) -> Self {
        Self {
            kind,
            lexeme,
            location: SourceLocation::new(file_id, source_range, line, column),
        }
    }
}

struct Scanner<'a> {
    chars: Peekable<CharIndices<'a>>,
    cur_token_start: usize,
    cur_token_column: usize,
    next_token_start: usize,
    file_id: FileId,
    string_buf: String,
    line: usize,
    column: usize,
}

fn end_token(c: char) -> bool {
    matches!(
        c,
        '+' | '-' | '=' | '>' | '<' | '*' | '!' | '@' | '/' | '[' | ']' | ':'
    ) || c.is_whitespace()
}

impl<'source> Scanner<'source> {
    fn advance(&mut self) -> char {
        let (idx, ch) = self.chars.next().expect("unexpected end of input");
        self.next_token_start = idx + ch.len_utf8();
        self.column += 1;
        if ch == '\n' {
            self.line += 1;
            self.column = 1;
        }
        ch
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
    }

    // We need mutable access here because we're peeking the iterator.
    #[allow(clippy::wrong_self_convention)]
    fn is_at_end(&mut self) -> bool {
        self.peek().is_none()
    }

    fn lexeme<'a>(&self, input: &'a str) -> &'a str {
        &input[self.cur_token_start..self.next_token_start]
    }

    fn lexeme_range(&self) -> Range<usize> {
        self.cur_token_start..self.next_token_start
    }

    fn consume_string_or_char_literal(
        &mut self,
        close_char: char,
        kind: &str,
        source_store: &SourceStorage,
    ) -> Result<(), ()> {
        self.string_buf.clear();

        let mut ch = '\0';
        while !self.is_at_end() {
            ch = self.advance();
            let next_ch = self.peek().unwrap_or_default();

            match (ch, next_ch) {
                ('\\', '\'') if close_char == '\'' => {
                    self.string_buf.push(next_ch);
                    self.advance();
                }
                ('\\', '"') if close_char == '"' => {
                    self.string_buf.push(next_ch);
                    self.advance();
                }
                ('\\', '\\') => {
                    self.string_buf.push(next_ch);
                    self.advance();
                }
                ('\\', 'r') => {
                    self.string_buf.push('\r');
                    self.advance();
                }
                ('\\', 'n') => {
                    self.string_buf.push('\n');
                    self.advance();
                }
                ('\\', 't') => {
                    self.string_buf.push('\t');
                    self.advance();
                }
                ('\\', '0') => {
                    self.string_buf.push('\0');
                    self.advance();
                }
                (ch, _) if ch == close_char => break,
                (ch, _) => self.string_buf.push(ch),
            }
        }

        if ch != close_char && self.is_at_end() {
            let loc = SourceLocation::new(
                self.file_id,
                self.lexeme_range(),
                self.line,
                self.cur_token_column,
            );
            diagnostics::emit_error(
                loc,
                format!("unclosed {} literal", kind),
                Some(Label::new(loc).with_color(Color::Red)),
                None,
                source_store,
            );

            return Err(());
        }

        if close_char == '\"' {
            // Make sure to always null-terminate the strings. Makes it easier to support C-strings.
            self.string_buf.push('\0');
        }

        Ok(())
    }

    fn scan_token(
        &mut self,
        input: &str,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<Option<Token>, ()> {
        let ch = self.advance();
        let next_ch = self.peek().unwrap_or_default();

        let res = match (ch, next_ch) {
            _ if ch.is_whitespace() => None,

            ('/', '/') => {
                while !matches!(self.peek(), Some('\n')) && !self.is_at_end() {
                    self.advance();
                }

                None
            }

            ('!' | '<' | '>', '=') => {
                let kind = match ch {
                    '!' => TokenKind::NotEqual,
                    '<' => TokenKind::LessEqual,
                    '>' => TokenKind::GreaterEqual,
                    _ => unreachable!(),
                };

                self.advance(); // Consume the '='

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(Token::new(
                    kind,
                    lexeme,
                    self.file_id,
                    self.lexeme_range(),
                    self.line,
                    self.cur_token_column,
                ))
            }

            ('+' | '-' | '=' | '<' | '>' | '*' | '[' | ']', _) => {
                let kind = match ch {
                    '+' => TokenKind::Plus,
                    '-' => TokenKind::Minus,
                    '*' => TokenKind::Star,
                    '=' => TokenKind::Equal,
                    '<' => TokenKind::Less,
                    '>' => TokenKind::Greater,
                    '[' => TokenKind::SquareBracketOpen,
                    ']' => TokenKind::SquareBracketClosed,
                    _ => unreachable!(),
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(Token::new(
                    kind,
                    lexeme,
                    self.file_id,
                    self.lexeme_range(),
                    self.line,
                    self.cur_token_column,
                ))
            }

            ('"', _) => {
                self.consume_string_or_char_literal('"', "string", source_store)?;

                let is_c_str = if let Some('c') = self.peek() {
                    self.advance();
                    true
                } else {
                    false
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                let literal = interner.intern_literal(&self.string_buf);

                Some(Token::new(
                    TokenKind::String {
                        id: literal,
                        is_c_str,
                    },
                    lexeme,
                    self.file_id,
                    self.lexeme_range(),
                    self.line,
                    self.cur_token_column,
                ))
            }

            ('\'', _) => {
                self.consume_string_or_char_literal('\'', "char", source_store)?;

                if self.string_buf.chars().count() != 1 {
                    let loc = SourceLocation::new(
                        self.file_id,
                        self.lexeme_range(),
                        self.line,
                        self.cur_token_column,
                    );
                    diagnostics::emit_error(
                        loc,
                        "invalid char literal",
                        Some(Label::new(loc).with_color(Color::Red)),
                        None,
                        source_store,
                    );
                    return Err(());
                }

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                let ch = self.string_buf.chars().next().unwrap();

                Some(Token::new(
                    TokenKind::Integer(ch as _),
                    lexeme,
                    self.file_id,
                    self.lexeme_range(),
                    self.line,
                    self.cur_token_column,
                ))
            }

            (':', ':') => {
                self.advance(); // Consume the second ':'
                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(Token::new(
                    TokenKind::ColonColon,
                    lexeme,
                    self.file_id,
                    self.lexeme_range(),
                    self.line,
                    self.cur_token_column,
                ))
            }

            _ => {
                self.string_buf.clear();
                self.string_buf.push(ch);
                let mut is_all_num = ch.is_ascii_digit();
                while !matches!(self.peek(), Some(c) if end_token(c)) && !self.is_at_end() {
                    let c = self.advance();
                    is_all_num &= matches!(c, '0'..='9' | '_');
                    if c.is_ascii_digit() {
                        self.string_buf.push(c);
                    }
                }

                let lexeme = self.lexeme(input);
                let kind = match lexeme {
                    "@8" => TokenKind::Load(Width::Byte),
                    "@16" => TokenKind::Load(Width::Word),
                    "@32" => TokenKind::Load(Width::Dword),
                    "@64" => TokenKind::Load(Width::Qword),
                    "@ptr" => TokenKind::LoadPtr,
                    "!8" => TokenKind::Store(Width::Byte),
                    "!16" => TokenKind::Store(Width::Word),
                    "!32" => TokenKind::Store(Width::Dword),
                    "!64" => TokenKind::Store(Width::Qword),
                    "!ptr" => TokenKind::StorePtr,
                    "and" => TokenKind::BitAnd,
                    "argc" => TokenKind::ArgC,
                    "argv" => TokenKind::ArgV,
                    "assert" => TokenKind::Assert,
                    "cast(bool)" => TokenKind::CastBool,
                    "cast(int)" => TokenKind::CastInt,
                    "cast(ptr)" => TokenKind::CastPtr,
                    "const" => TokenKind::Const,
                    "divmod" => TokenKind::DivMod,
                    "do" => TokenKind::Do,
                    "drop" => TokenKind::Drop,
                    "dup" => TokenKind::Dup(0),
                    "elif" => TokenKind::Elif,
                    "else" => TokenKind::Else,
                    "end" => TokenKind::End,
                    "false" => TokenKind::Boolean(false),
                    "here" => {
                        // These should never fail; we get the file ID from the source store, and the store
                        // has a full copy of the contents.
                        let filename = source_store.name(self.file_id);

                        self.string_buf.clear();
                        write!(
                            &mut self.string_buf,
                            "{}:{}:{}",
                            filename, self.line, self.cur_token_column
                        )
                        .unwrap();
                        let id = interner.intern_literal(&self.string_buf);
                        TokenKind::Here(id)
                    }
                    "if" => TokenKind::If,
                    "include" => TokenKind::Include,
                    "is" => TokenKind::Is,
                    "macro" => TokenKind::Macro,
                    "memory" => TokenKind::Memory,
                    "not" => TokenKind::BitNot,
                    "or" => TokenKind::BitOr,
                    "over" => TokenKind::Dup(1),
                    "proc" => TokenKind::Proc,
                    "return" => TokenKind::Return,
                    "rot" => TokenKind::Rot,
                    "shl" => TokenKind::ShiftLeft,
                    "shr" => TokenKind::ShiftRight,
                    "swap" => TokenKind::Swap,
                    "syscall1" => TokenKind::SysCall(1),
                    "syscall2" => TokenKind::SysCall(2),
                    "syscall3" => TokenKind::SysCall(3),
                    "syscall4" => TokenKind::SysCall(4),
                    "syscall5" => TokenKind::SysCall(5),
                    "syscall6" => TokenKind::SysCall(6),
                    "to" => TokenKind::GoesTo,
                    "true" => TokenKind::Boolean(true),
                    "while" => TokenKind::While,
                    _ if is_all_num => {
                        // We only put numbers in here, so it can't fail.
                        let value = self.string_buf.parse().unwrap();
                        TokenKind::Integer(value)
                    }
                    _ => TokenKind::Ident,
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(Token::new(
                    kind,
                    lexeme,
                    self.file_id,
                    self.lexeme_range(),
                    self.line,
                    self.cur_token_column,
                ))
            }
        };

        Ok(res)
    }
}

pub(crate) fn lex_file(
    contents: &str,
    file_id: FileId,
    interner: &mut Interners,
    source_store: &SourceStorage,
) -> Result<Vec<Token>, ()> {
    let mut scanner = Scanner {
        chars: contents.char_indices().peekable(),
        cur_token_start: 0,
        cur_token_column: 1,
        next_token_start: 0,
        line: 1,
        column: 1,
        file_id,
        string_buf: String::new(),
    };

    let mut ops = Vec::new();

    while scanner.peek().is_some() {
        scanner.cur_token_start = scanner.next_token_start;
        scanner.cur_token_column = scanner.column;

        match scanner.scan_token(contents, interner, source_store)? {
            Some(op) => ops.push(op),
            None => continue,
        };
    }

    Ok(ops)
}
