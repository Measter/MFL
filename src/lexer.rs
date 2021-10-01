use std::{iter::Peekable, ops::Range, str::CharIndices};

use codespan_reporting::diagnostic::Diagnostic;

use crate::source_file::{FileId, SourceLocation};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
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
    Less,
    Load,
    Mem,
    Minus,
    Plus,
    Store,
    SysCall(usize),
    While,
}

#[derive(Debug, Clone, Copy)]
pub struct Token<'a> {
    pub kind: TokenKind,
    pub lexeme: &'a str,
    pub location: SourceLocation,
}

impl<'a> Token<'a> {
    fn new(kind: TokenKind, lexeme: &'a str, file_id: FileId, source_range: Range<usize>) -> Self {
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

    fn scan_token<'token>(
        &mut self,
        input: &'token str,
    ) -> Result<Option<Token<'token>>, Diagnostic<FileId>> {
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
            ('+', _) => Some(Token::new(
                TokenKind::Plus,
                self.lexeme(input),
                self.file_id,
                self.lexeme_range(),
            )),
            ('-', _) => Some(Token::new(
                TokenKind::Minus,
                self.lexeme(input),
                self.file_id,
                self.lexeme_range(),
            )),
            ('=', _) => Some(Token::new(
                TokenKind::Equal,
                self.lexeme(input),
                self.file_id,
                self.lexeme_range(),
            )),
            ('<', _) => Some(Token::new(
                TokenKind::Less,
                self.lexeme(input),
                self.file_id,
                self.lexeme_range(),
            )),
            ('>', _) => Some(Token::new(
                TokenKind::Greater,
                self.lexeme(input),
                self.file_id,
                self.lexeme_range(),
            )),

            ('.', _) => Some(Token::new(
                TokenKind::Store,
                self.lexeme(input),
                self.file_id,
                self.lexeme_range(),
            )),
            (',', _) => Some(Token::new(
                TokenKind::Load,
                self.lexeme(input),
                self.file_id,
                self.lexeme_range(),
            )),

            _ => {
                while !matches!(self.peek(), Some(c) if end_token(c)) && !self.is_at_end() {
                    self.advance();
                }

                let lexeme = self.lexeme(input);
                let kind = match lexeme {
                    "2dup" => TokenKind::DupPair,
                    "do" => TokenKind::Do,
                    "drop" => TokenKind::Drop,
                    "dump" => TokenKind::Dump,
                    "dup" => TokenKind::Dup,
                    "else" => TokenKind::Else,
                    "end" => TokenKind::End,
                    "if" => TokenKind::If,
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

                Some(Token::new(
                    kind,
                    self.lexeme(input),
                    self.file_id,
                    self.lexeme_range(),
                ))
            }
        };

        Ok(res)
    }
}

pub(crate) fn lex_file(contents: &str, file_id: FileId) -> Result<Vec<Token>, Diagnostic<FileId>> {
    let mut scanner = Scanner {
        chars: contents.char_indices().peekable(),
        cur_token_start: 0,
        next_token_start: 0,
        file_id,
    };

    let mut ops = Vec::new();

    while scanner.peek().is_some() {
        scanner.cur_token_start = scanner.next_token_start;

        match scanner.scan_token(contents)? {
            Some(op) => ops.push(op),
            None => continue,
        };
    }

    Ok(ops)
}
