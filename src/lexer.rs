use std::{
    fmt::Write,
    iter::Peekable,
    ops::{Not, Range},
    str::CharIndices,
};

use ariadne::{Color, Label};
use intcast::IntCast;
use lasso::Spur;
use tracing::debug_span;

use crate::{
    diagnostics,
    interners::Interners,
    source_file::{FileId, SourceLocation, SourceStorage, Spanned, WithSpan},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    ArgC,
    ArgV,
    Assert,
    BitAnd,
    BitNot,
    BitOr,
    BitXor,
    Boolean(bool),
    Cast,
    Char(char),
    ColonColon,
    Const,
    Div,
    Do,
    Dot,
    Drop,
    Dup,
    Elif,
    Else,
    End,
    Equal,
    EmitStack,
    Exit,
    Extract { emit_struct: bool },
    Field,
    GoesTo,
    Greater,
    GreaterEqual,
    Here(Spur),
    Ident,
    If,
    Insert { emit_struct: bool },
    Integer { lexeme: Spur, is_hex: bool },
    Import,
    Is,
    IsNull,
    Less,
    LessEqual,
    Load,
    Memory,
    Minus,
    Module,
    NotEqual,
    Over,
    Pack,
    ParenthesisClosed,
    ParenthesisOpen,
    Plus,
    Proc,
    Rem,
    Return,
    Reverse,
    Rot,
    ShiftLeft,
    ShiftRight,
    SizeOf,
    SquareBracketClosed,
    SquareBracketOpen,
    Star,
    String { id: Spur, is_c_str: bool },
    Store,
    Struct,
    Swap,
    SysCall,
    Unpack,
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
            | TokenKind::BitXor
            | TokenKind::Boolean(_)
            | TokenKind::Cast
            | TokenKind::Char(_)
            | TokenKind::ColonColon
            | TokenKind::Const
            | TokenKind::Div
            | TokenKind::Do
            | TokenKind::Dot
            | TokenKind::Drop
            | TokenKind::Dup
            | TokenKind::Elif
            | TokenKind::Else
            | TokenKind::EmitStack
            | TokenKind::End
            | TokenKind::Equal
            | TokenKind::Exit
            | TokenKind::Extract { .. }
            | TokenKind::Field
            | TokenKind::GoesTo
            | TokenKind::Greater
            | TokenKind::GreaterEqual
            | TokenKind::Here(_)
            | TokenKind::Ident
            | TokenKind::Module
            | TokenKind::Insert { .. }
            | TokenKind::Integer { .. }
            | TokenKind::Import
            | TokenKind::IsNull
            | TokenKind::Less
            | TokenKind::LessEqual
            | TokenKind::Load
            | TokenKind::Memory
            | TokenKind::Minus
            | TokenKind::NotEqual
            | TokenKind::Over
            | TokenKind::Pack
            | TokenKind::ParenthesisClosed
            | TokenKind::ParenthesisOpen
            | TokenKind::Plus
            | TokenKind::Proc
            | TokenKind::Rem
            | TokenKind::Return
            | TokenKind::Reverse
            | TokenKind::Rot
            | TokenKind::ShiftLeft
            | TokenKind::ShiftRight
            | TokenKind::SizeOf
            | TokenKind::SquareBracketClosed
            | TokenKind::SquareBracketOpen
            | TokenKind::Star
            | TokenKind::String { .. }
            | TokenKind::Store
            | TokenKind::Struct
            | TokenKind::Swap
            | TokenKind::SysCall
            | TokenKind::Unpack => false,

            TokenKind::If | TokenKind::Is | TokenKind::While => true,
        }
    }

    pub fn is_matched_open(self) -> bool {
        matches!(
            self,
            TokenKind::ParenthesisOpen | TokenKind::SquareBracketOpen
        )
    }

    pub fn is_matched_close(self) -> bool {
        matches!(
            self,
            TokenKind::ParenthesisClosed | TokenKind::SquareBracketClosed
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub lexeme: Spur,
}

impl Token {
    fn new(kind: TokenKind, lexeme: Spur) -> Self {
        Self { kind, lexeme }
    }
}

struct Scanner<'a> {
    chars: Peekable<CharIndices<'a>>,
    cur_token_start: u32,
    cur_token_column: u16,
    next_token_start: u32,
    file_id: FileId,
    string_buf: String,
    line: u16,
    column: u16,
}

fn is_ident_start(c: char) -> bool {
    matches!(c, '_' | 'a'..='z' | 'A'..='Z')
}

fn is_ident_continue(c: char) -> bool {
    is_ident_start(c) || c.is_ascii_digit()
}

fn is_valid_post_number(c: char) -> bool {
    matches!(
        c,
        '+' | '-' | '*' | '=' | '<' | '>' | '/' | '(' | ')' | ']' | '!' | '@' | '%'
    ) || c.is_whitespace()
}

impl<'source> Scanner<'source> {
    fn advance(&mut self) -> char {
        let (idx, ch) = self.chars.next().expect("unexpected end of input");
        let next_token_start = idx + ch.len_utf8();
        self.next_token_start = next_token_start.to_u32().unwrap();

        self.column = self.column.checked_add(1).unwrap();
        if ch == '\n' {
            self.line = self.line.checked_add(1).unwrap();
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
        &input[self.cur_token_start.to_usize()..self.next_token_start.to_usize()]
    }

    fn lexeme_range(&self) -> Range<u32> {
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
            let loc = SourceLocation::new(self.file_id, self.lexeme_range());
            diagnostics::emit_error(
                loc,
                format!("unclosed {kind} literal"),
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

    fn consume_integer_literal(
        &mut self,
        start_char: char,
        valid_char: impl Fn(char) -> bool,
        source_store: &SourceStorage,
    ) -> Result<(), ()> {
        self.string_buf.clear();
        self.string_buf.push(start_char);
        while self.peek().is_some_and(&valid_char) && !self.is_at_end() {
            let c = self.advance();
            if c != '_' {
                self.string_buf.push(c);
            }
        }

        match self.peek() {
            Some(c) if !is_valid_post_number(c) => {
                self.advance();
                let loc = SourceLocation::new(self.file_id, self.lexeme_range());
                diagnostics::emit_error(
                    loc,
                    format!("invalid character in number: `{c}`"),
                    Some(Label::new(loc).with_color(Color::Red)),
                    None,
                    source_store,
                );

                return Err(());
            }
            _ => {}
        }

        Ok(())
    }

    fn scan_token(
        &mut self,
        input: &str,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<Option<Spanned<Token>>, ()> {
        let ch = self.advance();
        let next_ch = self.peek().unwrap_or_default();

        let res = match (ch, next_ch) {
            _ if ch.is_whitespace() => None,

            ('/', '/') => {
                while self.peek() != Some('\n') && !self.is_at_end() {
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
                Some(
                    Token::new(kind, lexeme)
                        .with_span(SourceLocation::new(self.file_id, self.lexeme_range())),
                )
            }

            (
                '+' | '-' | '=' | '<' | '>' | '*' | '/' | '%' | '[' | ']' | '(' | ')' | '@' | '!'
                | '.',
                _,
            ) => {
                let kind = match ch {
                    '+' => TokenKind::Plus,
                    '-' => TokenKind::Minus,
                    '*' => TokenKind::Star,
                    '/' => TokenKind::Div,
                    '%' => TokenKind::Rem,
                    '=' => TokenKind::Equal,
                    '<' => TokenKind::Less,
                    '>' => TokenKind::Greater,
                    '(' => TokenKind::ParenthesisOpen,
                    ')' => TokenKind::ParenthesisClosed,
                    '[' => TokenKind::SquareBracketOpen,
                    ']' => TokenKind::SquareBracketClosed,
                    '!' => TokenKind::Store,
                    '@' => TokenKind::Load,
                    '.' => TokenKind::Dot,
                    _ => unreachable!(),
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(
                    Token::new(kind, lexeme)
                        .with_span(SourceLocation::new(self.file_id, self.lexeme_range())),
                )
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

                Some(
                    Token::new(
                        TokenKind::String {
                            id: literal,
                            is_c_str,
                        },
                        lexeme,
                    )
                    .with_span(SourceLocation::new(self.file_id, self.lexeme_range())),
                )
            }

            ('\'', _) => {
                self.consume_string_or_char_literal('\'', "char", source_store)?;

                if self.string_buf.chars().count() != 1 {
                    let loc = SourceLocation::new(self.file_id, self.lexeme_range());
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

                Some(
                    Token::new(TokenKind::Char(ch), lexeme)
                        .with_span(SourceLocation::new(self.file_id, self.lexeme_range())),
                )
            }

            (':', ':') => {
                self.advance(); // Consume the second ':'
                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(
                    Token::new(TokenKind::ColonColon, lexeme)
                        .with_span(SourceLocation::new(self.file_id, self.lexeme_range())),
                )
            }

            ('0', 'x') => {
                self.advance(); // Consume the 'x'

                let next = self.peek();
                if !next.is_some_and(|c| c.is_ascii_hexdigit()) || self.is_at_end() {
                    let loc = SourceLocation::new(self.file_id, self.lexeme_range());
                    let next_char = next.unwrap();
                    diagnostics::emit_error(
                        loc,
                        format!("unexpected character in input: `{next_char}`"),
                        Some(Label::new(loc).with_color(Color::Red)),
                        None,
                        source_store,
                    );
                    return Err(());
                }

                let ch = self.advance();
                self.consume_integer_literal(
                    ch,
                    |c| c == '_' || c.is_ascii_hexdigit(),
                    source_store,
                )?;

                let stripped_id = interner.intern_literal(&self.string_buf);
                let kind = TokenKind::Integer {
                    lexeme: stripped_id,
                    is_hex: true,
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(
                    Token::new(kind, lexeme)
                        .with_span(SourceLocation::new(self.file_id, self.lexeme_range())),
                )
            }

            ('0'..='9', _) => {
                self.consume_integer_literal(ch, |c| c == '_' || c.is_ascii_digit(), source_store)?;
                let stripped_id = interner.intern_literal(&self.string_buf);
                let kind = TokenKind::Integer {
                    lexeme: stripped_id,
                    is_hex: false,
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(
                    Token::new(kind, lexeme)
                        .with_span(SourceLocation::new(self.file_id, self.lexeme_range())),
                )
            }

            (c, _) if is_ident_start(c) => {
                self.string_buf.clear();
                self.string_buf.push(ch);
                while self.peek().is_some_and(is_ident_continue) && !self.is_at_end() {
                    let c = self.advance();
                    self.string_buf.push(c);
                }

                let lexeme = self.lexeme(input);
                let kind = match lexeme {
                    "and" => TokenKind::BitAnd,
                    "argc" => TokenKind::ArgC,
                    "argv" => TokenKind::ArgV,
                    "assert" => TokenKind::Assert,
                    "cast" => TokenKind::Cast,
                    "const" => TokenKind::Const,
                    "do" => TokenKind::Do,
                    "drop" => TokenKind::Drop,
                    "dup" => TokenKind::Dup,
                    "elif" => TokenKind::Elif,
                    "else" => TokenKind::Else,
                    "end" => TokenKind::End,
                    "exit" => TokenKind::Exit,
                    "xtr" => TokenKind::Extract { emit_struct: true },
                    "xtrd" => TokenKind::Extract { emit_struct: false },
                    "false" => TokenKind::Boolean(false),
                    "field" => TokenKind::Field,
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
                    "import" => TokenKind::Import,
                    "ins" => TokenKind::Insert { emit_struct: true },
                    "insd" => TokenKind::Insert { emit_struct: false },
                    "is" => TokenKind::Is,
                    "isnull" => TokenKind::IsNull,
                    "memory" => TokenKind::Memory,
                    "module" => TokenKind::Module,
                    "not" => TokenKind::BitNot,
                    "or" => TokenKind::BitOr,
                    "over" => TokenKind::Over,
                    "pack" => TokenKind::Pack,
                    "proc" => TokenKind::Proc,
                    "return" => TokenKind::Return,
                    "rev" => TokenKind::Reverse,
                    "rot" => TokenKind::Rot,
                    "shl" => TokenKind::ShiftLeft,
                    "shr" => TokenKind::ShiftRight,
                    "sizeof" => TokenKind::SizeOf,
                    "stktrc" => TokenKind::EmitStack,
                    "struct" => TokenKind::Struct,
                    "swap" => TokenKind::Swap,
                    "syscall" => TokenKind::SysCall,
                    "unpack" => TokenKind::Unpack,
                    "to" => TokenKind::GoesTo,
                    "true" => TokenKind::Boolean(true),
                    "while" => TokenKind::While,
                    "xor" => TokenKind::BitXor,
                    _ => TokenKind::Ident,
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(
                    Token::new(kind, lexeme)
                        .with_span(SourceLocation::new(self.file_id, self.lexeme_range())),
                )
            }

            (c, _) => {
                let loc = SourceLocation::new(self.file_id, self.lexeme_range());
                diagnostics::emit_error(
                    loc,
                    format!("unexpected character in input: `{c}`"),
                    Some(Label::new(loc).with_color(Color::Red)),
                    None,
                    source_store,
                );
                return Err(());
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
) -> Result<Vec<Spanned<Token>>, ()> {
    let _span = debug_span!(stringify!(lexer::lex_file)).entered();

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
    let mut had_error = false;

    while scanner.peek().is_some() {
        scanner.cur_token_start = scanner.next_token_start;
        scanner.cur_token_column = scanner.column;

        match scanner.scan_token(contents, interner, source_store) {
            Ok(Some(op)) => ops.push(op),
            Ok(None) => continue,
            Err(_) => had_error = true,
        };
    }

    had_error.not().then_some(ops).ok_or(())
}
