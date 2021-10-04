use std::{iter::Peekable, ops::Range, str::CharIndices};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use lasso::Spur;

use crate::{
    interners::Interners,
    source_file::{FileId, SourceLocation},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    BitOr,
    BitAnd,
    Do,
    Drop,
    Dump,
    Dup,
    DupPair,
    Else,
    End,
    Equal,
    Greater,
    Ident,
    If,
    Integer(u64),
    Less,
    Load,
    Macro,
    Mem,
    Minus,
    Plus,
    Over,
    ShiftLeft,
    ShiftRight,
    String(Spur),
    Store,
    Swap,
    SysCall(usize),
    While,
}

impl TokenKind {
    pub fn new_block(self) -> bool {
        match self {
            TokenKind::BitOr
            | TokenKind::BitAnd
            | TokenKind::Do
            | TokenKind::Drop
            | TokenKind::Dump
            | TokenKind::Dup
            | TokenKind::DupPair
            | TokenKind::Else
            | TokenKind::End
            | TokenKind::Equal
            | TokenKind::Greater
            | TokenKind::Ident
            | TokenKind::Integer(_)
            | TokenKind::Less
            | TokenKind::Load
            | TokenKind::Mem
            | TokenKind::Minus
            | TokenKind::Plus
            | TokenKind::Over
            | TokenKind::ShiftLeft
            | TokenKind::ShiftRight
            | TokenKind::String(_)
            | TokenKind::Store
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
    matches!(c, '+' | '-' | '.' | '=' | '>' | '<' | ',') || c.is_whitespace()
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

    fn lex_string<'token>(
        &mut self,
        input: &'token str,
        interner: &mut Interners,
    ) -> Result<Token, Diagnostic<FileId>> {
        self.string_buf.clear();

        while !self.is_at_end() {
            let ch = self.advance();
            let next_ch = self.peek().unwrap_or_default();

            match (ch, next_ch) {
                ('\\', '\\' | '"') => {
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
                ('"', _) => break,
                (ch, _) => self.string_buf.push(ch),
            }
        }

        if self.is_at_end() {
            let diag = Diagnostic::error()
                .with_message("unclosed string literal")
                .with_labels(vec![Label::primary(
                    self.file_id,
                    self.cur_token_start..self.next_token_start,
                )]);
            return Err(diag);
        }

        let lexeme = interner.intern_lexeme(self.lexeme(input));
        let literal = interner.intern_literal(&self.string_buf);

        Ok(Token::new(
            TokenKind::String(literal),
            lexeme,
            self.file_id,
            self.lexeme_range(),
        ))
    }

    fn scan_token(
        &mut self,
        input: &str,
        interner: &mut Interners,
    ) -> Result<Option<Token>, Diagnostic<FileId>> {
        let ch = self.advance();
        let next_ch = self.peek().unwrap_or_default();

        let res = match (ch, next_ch) {
            ('/', '/') => {
                while !matches!(self.peek(), Some('\n')) && !self.is_at_end() {
                    self.advance();
                }

                None
            }

            _ if ch.is_whitespace() => None,
            ('+' | '-' | '=' | '<' | '>' | '.' | ',', _) => {
                let kind = match ch {
                    '+' => TokenKind::Plus,
                    '-' => TokenKind::Minus,
                    '=' => TokenKind::Equal,
                    '<' => TokenKind::Less,
                    '>' => TokenKind::Greater,
                    '.' => TokenKind::Store,
                    ',' => TokenKind::Load,
                    _ => unreachable!(),
                };

                let lexeme = interner.intern_lexeme(self.lexeme(input));
                Some(Token::new(kind, lexeme, self.file_id, self.lexeme_range()))
            }

            ('"', _) => Some(self.lex_string(input, interner)?),

            // Need to make sure we don't have a collision with the "2dup"
            // keyword
            ('0'..='9', c) if c != 'd' => {
                while matches!(self.peek(), Some('0'..='9')) {
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
                    "2dup" => TokenKind::DupPair,
                    "bor" => TokenKind::BitOr,
                    "band" => TokenKind::BitAnd,
                    "do" => TokenKind::Do,
                    "drop" => TokenKind::Drop,
                    "dump" => TokenKind::Dump,
                    "dup" => TokenKind::Dup,
                    "else" => TokenKind::Else,
                    "end" => TokenKind::End,
                    "if" => TokenKind::If,
                    "over" => TokenKind::Over,
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

        match scanner.scan_token(contents, interner)? {
            Some(op) => ops.push(op),
            None => continue,
        };
    }

    Ok(ops)
}
