use core::panic;
use std::fmt::{Display, Write};

use intcast::IntCast;
use lasso::Spur;
use logos::{Lexer, Logos};
use stores::{
    source::{FileId, SourceLocation, Spanned, WithSpan},
    strings::StringStore,
};
use tracing::debug_span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Insert {
    pub emit_struct: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Extract {
    pub emit_struct: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntegerBase {
    Binary = 2,
    Octal = 8,
    Decimal = 10,
    Hexidecimal = 16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StringToken {
    pub id: Spur,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CharToken {
    pub id: Spur,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BracketKind {
    Brace,
    Paren,
    Square,
}

impl Display for BracketKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BracketKind::Brace => f.write_char('{'),
            BracketKind::Paren => f.write_char('('),
            BracketKind::Square => f.write_char('['),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InternalError {
    UnclosedString,
    UnclosedChar,
    #[default]
    Other,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Logos)]
#[logos(skip "[\t\n\r ]+")]
#[logos(error = InternalError)]
pub enum TokenKind {
    #[token("&")]
    Ampersand,

    #[token("array")]
    Array,

    #[token("assert")]
    Assert,

    #[token("assumeinit")]
    AssumeInit,

    #[token("and")]
    BitAnd,

    #[token("not")]
    BitNot,

    #[token("or")]
    BitOr,

    #[token("xor")]
    BitXor,

    #[token("true", |_| true)]
    #[token("false", |_| false)]
    Boolean(bool),

    #[token("}", |_| BracketKind::Brace)]
    #[token(")", |_| BracketKind::Paren)]
    #[token("]", |_| BracketKind::Square)]
    BracketClose(BracketKind),

    #[token("{", |_| BracketKind::Brace)]
    #[token("(", |_| BracketKind::Paren)]
    #[token("[", |_| BracketKind::Square)]
    BracketOpen(BracketKind),

    #[token("^")]
    Carat,

    #[token("cast")]
    Cast,

    // We fixup afterwards like we do with strings.
    #[token("\'", |l| char_literal(l))]
    Char(CharToken),

    #[token(":")]
    Colon,

    #[token("::")]
    ColonColon,

    #[regex("//[^\n]*")]
    Comment,

    #[token("cond")]
    Cond,

    #[token("const")]
    Const,

    #[token(",")]
    Comma,

    #[token("/")]
    Div,

    #[token(".")]
    Dot,

    #[token("drop")]
    Drop,

    #[token("dup")]
    Dup,

    #[token("else")]
    Else,

    #[token("enum")]
    Enum,

    #[token("=")]
    Equal,

    #[token("stktrc")]
    EmitStack,

    #[token("exit")]
    Exit,

    #[token("extern")]
    Extern,

    #[token("xtr", |_| Extract{emit_struct: true})]
    #[token("xtrd", |_| Extract{emit_struct: false})]
    Extract(Extract),

    #[regex("[0-9][0-9_]*\\.[0-9][0-9_]*([eE][-\\+]?[0-9][0-9_]*)?")]
    Float,

    #[token("to")]
    GoesTo,

    #[token(">")]
    Greater,

    #[token(">=")]
    GreaterEqual,

    #[token("#")]
    Hash,

    #[token("here")]
    Here,

    #[regex("[_a-zA-Z][_a-zA-Z0-9]*")]
    Ident,

    #[token("ins", |_| Insert{emit_struct: true})]
    #[token("insd", |_| Insert{emit_struct: false})]
    Insert(Insert),

    #[regex("0[bB][01][01_]*", |_| IntegerBase::Binary)]
    #[regex("[0-9][0-9_]*", |_| IntegerBase::Decimal)]
    #[regex("0[o][0-7][0-7_]*", |_| IntegerBase::Octal)]
    #[regex("0[xX][0-9A-Fa-f][0-9A-Fa-f_]*", |_| IntegerBase::Hexidecimal)]
    Integer(IntegerBase),

    #[token("import")]
    Import,

    #[token("isnull")]
    IsNull,

    #[token("lang")]
    LangItem,

    #[token("<")]
    Less,

    #[token("<=")]
    LessEqual,

    #[token("lib")]
    Lib,

    #[token("@")]
    Load,

    #[token("-")]
    Minus,

    #[token("module")]
    Module,

    #[token("!=")]
    NotEqual,

    #[token("over")]
    Over,

    #[token("pack")]
    Pack,

    #[token("|")]
    Pipe,

    #[token("+")]
    Plus,

    #[token("proc")]
    Proc,

    #[token("%")]
    Rem,

    #[token("return")]
    Return,

    #[token("rev")]
    Reverse,

    #[token("rot")]
    Rot,

    #[token("self")]
    SelfKw,

    #[token("shl")]
    ShiftLeft,

    #[token("shr")]
    ShiftRight,

    #[token("sizeof")]
    SizeOf,

    #[token("*")]
    Star,

    // We do a fixup later, in the consume loop
    #[token("\"", |l| str_literal(l))]
    String(StringToken),

    #[token("!")]
    Store,

    #[token("struct")]
    Struct,

    #[token("super")]
    Super,

    #[token("swap")]
    Swap,

    #[token("syscall")]
    SysCall,

    #[token("union")]
    Union,

    #[token("unpack")]
    Unpack,

    #[token("var")]
    Variable,

    #[token("while")]
    While,
}

impl TokenKind {
    pub fn kind_str(self) -> &'static str {
        match self {
            TokenKind::Ampersand => "&",
            TokenKind::Array => "array",
            TokenKind::Assert => "assert",
            TokenKind::AssumeInit => "init",
            TokenKind::BitAnd => "and",
            TokenKind::BitNot => "not",
            TokenKind::BitOr => "or",
            TokenKind::BitXor => "xor",
            TokenKind::Boolean(_) => "boolean literal",
            TokenKind::BracketClose(BracketKind::Brace) => "}",
            TokenKind::BracketClose(BracketKind::Paren) => ")",
            TokenKind::BracketClose(BracketKind::Square) => "]",
            TokenKind::BracketOpen(BracketKind::Brace) => "{",
            TokenKind::BracketOpen(BracketKind::Paren) => "(",
            TokenKind::BracketOpen(BracketKind::Square) => "[",
            TokenKind::Carat => "^",
            TokenKind::Cast => "cast",
            TokenKind::Char(_) => "character literal",
            TokenKind::Colon => ":",
            TokenKind::ColonColon => "::",
            TokenKind::Cond => "cond",
            TokenKind::Const => "const",
            TokenKind::Comment => "comment",
            TokenKind::Comma => ",",
            TokenKind::Div => "/",
            TokenKind::Dot => ".",
            TokenKind::Drop => "drop",
            TokenKind::Dup => "dup",
            TokenKind::Else => "else",
            TokenKind::Enum => "enum",
            TokenKind::Equal => "=",
            TokenKind::EmitStack => "emit",
            TokenKind::Exit => "exit",
            TokenKind::Extern => "extern",
            TokenKind::Extract(Extract { emit_struct: true }) => "xtr",
            TokenKind::Extract(Extract { emit_struct: false }) => "xtrd",
            TokenKind::Float => "float literal",
            TokenKind::GoesTo => "to",
            TokenKind::Greater => ">",
            TokenKind::GreaterEqual => ">=",
            TokenKind::Hash => "#",
            TokenKind::Here => "here",
            TokenKind::Ident => "Ident",
            TokenKind::Insert(Insert { emit_struct: true }) => "ins",
            TokenKind::Insert(Insert { emit_struct: false }) => "insd",
            TokenKind::Integer(_) => "integer literal",
            TokenKind::Import => "import",
            TokenKind::IsNull => "isnull",
            TokenKind::LangItem => "lang",
            TokenKind::Less => "<",
            TokenKind::LessEqual => "<=",
            TokenKind::Lib => "lib",
            TokenKind::Load => "@",
            TokenKind::Minus => "-",
            TokenKind::Module => "module",
            TokenKind::NotEqual => "!=",
            TokenKind::Over => "over",
            TokenKind::Pack => "pack",
            TokenKind::Pipe => "|",
            TokenKind::Plus => "+",
            TokenKind::Proc => "proc",
            TokenKind::Rem => "%",
            TokenKind::Return => "return",
            TokenKind::Reverse => "rev",
            TokenKind::Rot => "rot",
            TokenKind::SelfKw => "self",
            TokenKind::ShiftLeft => "shl",
            TokenKind::ShiftRight => "shr",
            TokenKind::SizeOf => "sizeof",
            TokenKind::Star => "*",
            TokenKind::String(_) => "string literal",
            TokenKind::Store => "!",
            TokenKind::Struct => "struct",
            TokenKind::Super => "super",
            TokenKind::Swap => "swap",
            TokenKind::SysCall => "syscall",
            TokenKind::Union => "union",
            TokenKind::Unpack => "unpack",
            TokenKind::Variable => "var",
            TokenKind::While => "while",
        }
    }

    pub fn expects_brace_group(self) -> bool {
        matches!(self, TokenKind::Cond | TokenKind::While)
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

#[derive(Debug, Clone, Copy)]
pub enum LexerError {
    UnexpectedChar(SourceLocation),
    UnclosedString(SourceLocation),
    UnclosedChar(SourceLocation),
}

fn consume_char_str_lit(s: &str, end_char: u8) -> (usize, bool) {
    let mut chars = s.bytes();
    let mut found_close = false;
    while let Some(ch) = chars.next() {
        if ch == end_char {
            found_close = true;
            break;
        }
        if ch == b'\\' {
            chars.next(); // This is an escape sequence, so just consume the next character.
        }
    }

    (s.len() - chars.len(), found_close)
}

fn str_literal(lex: &mut Lexer<TokenKind>) -> Result<StringToken, InternalError> {
    let (consumed_len, found_close) = consume_char_str_lit(lex.remainder(), b'"');
    lex.bump(consumed_len);

    if found_close {
        Ok(StringToken {
            id: Spur::default(),
        })
    } else {
        Err(InternalError::UnclosedString)
    }
}

fn char_literal(lex: &mut Lexer<TokenKind>) -> Result<CharToken, InternalError> {
    let (consumed_len, found_close) = consume_char_str_lit(lex.remainder(), b'\'');
    lex.bump(consumed_len);

    if found_close {
        Ok(CharToken {
            id: Spur::default(),
        })
    } else {
        Err(InternalError::UnclosedChar)
    }
}

pub fn lex<'a>(
    interner: &'a mut StringStore,
    contents: &'a str,
    file_id: FileId,
) -> Vec<Result<Spanned<Token>, LexerError>> {
    let _span = debug_span!("lex").entered();

    let mut tokens = Vec::new();
    let mut lexer = TokenKind::lexer(contents).spanned();

    while let Some((kind, span)) = lexer.next() {
        let span = span.start.to_u32().unwrap()..span.end.to_u32().unwrap();
        let location = SourceLocation::new(file_id, span.clone());

        let mut kind = match kind {
            Ok(k) => k,
            Err(InternalError::UnclosedString) => {
                tokens.push(Err(LexerError::UnclosedString(location)));
                continue;
            }
            Err(InternalError::UnclosedChar) => {
                tokens.push(Err(LexerError::UnclosedChar(location)));
                continue;
            }
            Err(InternalError::Other) => {
                panic!("Unexpected error in lexer: {:?}, {:?}", kind, lexer.slice());
            }
        };

        match &mut kind {
            TokenKind::String(string_token) => {
                let slice = lexer.slice();
                string_token.id = interner.intern(&slice[1..slice.len() - 1]);
            }
            TokenKind::Char(char_token) => {
                let slice = lexer.slice();
                char_token.id = interner.intern(&slice[1..slice.len() - 1]);
            }
            _ => (),
        }

        let lexeme = interner.intern(lexer.slice());
        let token = Token::new(kind, lexeme).with_span(location);

        tokens.push(Ok(token));
    }

    tokens
}
