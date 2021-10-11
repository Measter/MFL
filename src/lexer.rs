use std::{fmt::Write, iter::Peekable, ops::Range, str::CharIndices};

use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    files::Files,
};
use lasso::Spur;

use crate::{
    interners::Interners,
    source_file::{FileId, SourceLocation, SourceStorage},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    ArgC,
    ArgV,
    BitOr,
    BitAnd,
    CastPtr,
    DivMod,
    Do,
    Drop,
    Dup(usize),
    DupPair,
    Else,
    End,
    Equal,
    Greater,
    GreaterEqual,
    Here(Spur),
    Ident,
    If,
    Include,
    Integer(u64),
    Less,
    LessEqual,
    Load,
    Load64,
    Macro,
    Mem,
    Minus,
    NotEqual,
    Plus,
    Print,
    ShiftLeft,
    ShiftRight,
    Star,
    String(Spur),
    Store { addr_first: bool },
    Store64 { addr_first: bool },
    Swap,
    SysCall(usize),
    While,
}

impl TokenKind {
    pub fn new_block(self) -> bool {
        match self {
            TokenKind::ArgC
            | TokenKind::ArgV
            | TokenKind::BitOr
            | TokenKind::BitAnd
            | TokenKind::CastPtr
            | TokenKind::DivMod
            | TokenKind::Do
            | TokenKind::Drop
            | TokenKind::Dup(_)
            | TokenKind::DupPair
            | TokenKind::Else
            | TokenKind::End
            | TokenKind::Equal
            | TokenKind::Greater
            | TokenKind::GreaterEqual
            | TokenKind::Here(_)
            | TokenKind::Ident
            | TokenKind::Include
            | TokenKind::Integer(_)
            | TokenKind::Less
            | TokenKind::LessEqual
            | TokenKind::Load
            | TokenKind::Load64
            | TokenKind::Mem
            | TokenKind::Minus
            | TokenKind::NotEqual
            | TokenKind::Plus
            | TokenKind::Print
            | TokenKind::ShiftLeft
            | TokenKind::ShiftRight
            | TokenKind::Star
            | TokenKind::String(_)
            | TokenKind::Store { .. }
            | TokenKind::Store64 { .. }
            | TokenKind::Swap
            | TokenKind::SysCall(_) => false,

            TokenKind::If | TokenKind::While | TokenKind::Macro => true,
        }
    }

    pub fn end_block(self) -> bool {
        self == TokenKind::End
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub kind: TokenKind,
    pub lexeme: Spur,
    pub location: SourceLocation,
}

impl Token {
    fn new(kind: TokenKind, lexeme: Spur, file_id: FileId, source_range: Range<usize>) -> Self {
        Self {
            kind,
            lexeme,
            location: SourceLocation::new(file_id, source_range),
        }
    }
}

struct Scanner<'a> {
    chars: Peekable<CharIndices<'a>>,
    cur_token_start: usize,
    next_token_start: usize,
    file_id: FileId,
    string_buf: String,
}

fn end_token(c: char) -> bool {
    matches!(c, '+' | '-' | '.' | '=' | '>' | '<' | ',' | '*' | '!') || c.is_whitespace()
}

impl<'source> Scanner<'source> {
    fn advance(&mut self) -> char {
        let (idx, ch) = self.chars.next().expect("unexpected end of input");
        self.next_token_start = idx + ch.len_utf8();
        ch
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
    }

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
    ) -> Result<(), Diagnostic<FileId>> {
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
            let diag = Diagnostic::error()
                .with_message(format!("unclosed {} literal", kind))
                .with_labels(vec![Label::primary(
                    self.file_id,
                    self.cur_token_start..self.next_token_start,
                )]);
            return Err(diag);
        }

        Ok(())
    }

    fn scan_token(
        &mut self,
        input: &str,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<Option<Token>, Diagnostic<FileId>> {
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
                Some(Token::new(kind, lexeme, self.file_id, self.lexeme_range()))
            }

            ('+' | '-' | '=' | '<' | '>' | '*', _) => {
                let kind = match ch {
                    '+' => TokenKind::Plus,
                    '-' => TokenKind::Minus,
                    '*' => TokenKind::Star,
                    '=' => TokenKind::Equal,
                    '<' => TokenKind::Less,
                    '>' => TokenKind::Greater,
                    _ => unreachable!(),
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(Token::new(kind, lexeme, self.file_id, self.lexeme_range()))
            }

            ('"', _) => {
                self.consume_string_or_char_literal('"', "string")?;

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                let literal = interner.intern_literal(&self.string_buf);

                Some(Token::new(
                    TokenKind::String(literal),
                    lexeme,
                    self.file_id,
                    self.lexeme_range(),
                ))
            }

            ('\'', _) => {
                self.consume_string_or_char_literal('\'', "char")?;

                if self.string_buf.chars().count() != 1 {
                    let diag = Diagnostic::error()
                        .with_message("invalid char literal")
                        .with_labels(vec![Label::primary(self.file_id, self.lexeme_range())]);

                    return Err(diag);
                }

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                let ch = self.string_buf.chars().next().unwrap();

                Some(Token::new(
                    TokenKind::Integer(ch as _),
                    lexeme,
                    self.file_id,
                    self.lexeme_range(),
                ))
            }

            // Need to make sure we don't have a collision with the "2dup"
            // keyword
            ('0'..='9', c) if c != 'd' => {
                while !matches!(self.peek(), Some(c) if end_token(c)) && !self.is_at_end() {
                    self.advance();
                }

                let lexeme = self.lexeme(input);
                let range = self.lexeme_range();
                let value = match lexeme.parse() {
                    Ok(num) => num,
                    Err(_) => {
                        let diag = Diagnostic::error()
                            .with_message("invalid number literal")
                            .with_labels(vec![Label::primary(self.file_id, range)]);
                        return Err(diag);
                    }
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(Token::new(
                    TokenKind::Integer(value),
                    lexeme,
                    self.file_id,
                    range,
                ))
            }

            _ => {
                while !matches!(self.peek(), Some(c) if end_token(c)) && !self.is_at_end() {
                    self.advance();
                }

                let lexeme = self.lexeme(input);
                let kind = match lexeme {
                    "." => TokenKind::Store { addr_first: false },
                    "," => TokenKind::Load,
                    ".64" => TokenKind::Store64 { addr_first: false },
                    ",64" => TokenKind::Load64,
                    "@" => TokenKind::Load,
                    "!" => TokenKind::Store { addr_first: true },
                    "@64" => TokenKind::Load64,
                    "!64" => TokenKind::Store64 { addr_first: true },
                    "argc" => TokenKind::ArgC,
                    "argv" => TokenKind::ArgV,
                    "bor" => TokenKind::BitOr,
                    "cast(ptr)" => TokenKind::CastPtr,
                    "divmod" => TokenKind::DivMod,
                    "band" => TokenKind::BitAnd,
                    "do" => TokenKind::Do,
                    "drop" => TokenKind::Drop,
                    "dup" => TokenKind::Dup(0),
                    "else" => TokenKind::Else,
                    "end" => TokenKind::End,
                    "here" => {
                        // These should never fail; we get the file ID from the source store, and the store
                        // has a full copy of the contents.
                        let filename = source_store.name(self.file_id).unwrap();
                        let location = source_store
                            .location(self.file_id, self.cur_token_start)
                            .unwrap();

                        self.string_buf.clear();
                        write!(
                            &mut self.string_buf,
                            "{}:{}:{}",
                            filename, location.line_number, location.column_number
                        )
                        .unwrap();
                        let id = interner.intern_literal(&self.string_buf);
                        TokenKind::Here(id)
                    }
                    "if" => TokenKind::If,
                    "include" => TokenKind::Include,
                    "over" => TokenKind::Dup(1),
                    "print" => TokenKind::Print,
                    "shl" => TokenKind::ShiftLeft,
                    "shr" => TokenKind::ShiftRight,
                    "swap" => TokenKind::Swap,
                    "macro" => TokenKind::Macro,
                    "mem" => TokenKind::Mem,
                    "syscall1" => TokenKind::SysCall(1),
                    "syscall2" => TokenKind::SysCall(2),
                    "syscall3" => TokenKind::SysCall(3),
                    "syscall4" => TokenKind::SysCall(4),
                    "syscall5" => TokenKind::SysCall(5),
                    "syscall6" => TokenKind::SysCall(6),
                    "while" => TokenKind::While,
                    _ => TokenKind::Ident,
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(Token::new(kind, lexeme, self.file_id, self.lexeme_range()))
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
) -> Result<Vec<Token>, Diagnostic<FileId>> {
    let mut scanner = Scanner {
        chars: contents.char_indices().peekable(),
        cur_token_start: 0,
        next_token_start: 0,
        file_id,
        string_buf: String::new(),
    };

    let mut ops = Vec::new();

    while scanner.peek().is_some() {
        scanner.cur_token_start = scanner.next_token_start;

        match scanner.scan_token(contents, interner, source_store)? {
            Some(op) => ops.push(op),
            None => continue,
        };
    }

    Ok(ops)
}
