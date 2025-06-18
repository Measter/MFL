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
pub enum Token {
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

impl Token {
    pub fn kind_str(self) -> &'static str {
        match self {
            Token::Ampersand => "&",
            Token::Array => "array",
            Token::Assert => "assert",
            Token::AssumeInit => "init",
            Token::BitAnd => "and",
            Token::BitNot => "not",
            Token::BitOr => "or",
            Token::BitXor => "xor",
            Token::Boolean(_) => "boolean literal",
            Token::BracketClose(BracketKind::Brace) => "}",
            Token::BracketClose(BracketKind::Paren) => ")",
            Token::BracketClose(BracketKind::Square) => "]",
            Token::BracketOpen(BracketKind::Brace) => "{",
            Token::BracketOpen(BracketKind::Paren) => "(",
            Token::BracketOpen(BracketKind::Square) => "[",
            Token::Carat => "^",
            Token::Cast => "cast",
            Token::Char(_) => "character literal",
            Token::Colon => ":",
            Token::ColonColon => "::",
            Token::Cond => "cond",
            Token::Const => "const",
            Token::Comment => "comment",
            Token::Comma => ",",
            Token::Div => "/",
            Token::Dot => ".",
            Token::Drop => "drop",
            Token::Dup => "dup",
            Token::Else => "else",
            Token::Enum => "enum",
            Token::Equal => "=",
            Token::EmitStack => "emit",
            Token::Exit => "exit",
            Token::Extern => "extern",
            Token::Extract(Extract { emit_struct: true }) => "xtr",
            Token::Extract(Extract { emit_struct: false }) => "xtrd",
            Token::Float => "float literal",
            Token::GoesTo => "to",
            Token::Greater => ">",
            Token::GreaterEqual => ">=",
            Token::Hash => "#",
            Token::Here => "here",
            Token::Ident => "Ident",
            Token::Insert(Insert { emit_struct: true }) => "ins",
            Token::Insert(Insert { emit_struct: false }) => "insd",
            Token::Integer(_) => "integer literal",
            Token::Import => "import",
            Token::IsNull => "isnull",
            Token::LangItem => "lang",
            Token::Less => "<",
            Token::LessEqual => "<=",
            Token::Lib => "lib",
            Token::Load => "@",
            Token::Minus => "-",
            Token::Module => "module",
            Token::NotEqual => "!=",
            Token::Over => "over",
            Token::Pack => "pack",
            Token::Pipe => "|",
            Token::Plus => "+",
            Token::Proc => "proc",
            Token::Rem => "%",
            Token::Return => "return",
            Token::Reverse => "rev",
            Token::Rot => "rot",
            Token::SelfKw => "self",
            Token::ShiftLeft => "shl",
            Token::ShiftRight => "shr",
            Token::SizeOf => "sizeof",
            Token::Star => "*",
            Token::String(_) => "string literal",
            Token::Store => "!",
            Token::Struct => "struct",
            Token::Super => "super",
            Token::Swap => "swap",
            Token::SysCall => "syscall",
            Token::Union => "union",
            Token::Unpack => "unpack",
            Token::Variable => "var",
            Token::While => "while",
        }
    }

    pub fn expects_brace_group(self) -> bool {
        matches!(self, Token::Cond | Token::While)
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

fn str_literal(lex: &mut Lexer<Token>) -> Result<StringToken, InternalError> {
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

fn char_literal(lex: &mut Lexer<Token>) -> Result<CharToken, InternalError> {
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
    let mut lexer = Token::lexer(contents).spanned();

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
            Token::String(string_token) => {
                let slice = lexer.slice();
                string_token.id = interner.intern(&slice[1..slice.len() - 1]);
            }
            Token::Char(char_token) => {
                let slice = lexer.slice();
                char_token.id = interner.intern(&slice[1..slice.len() - 1]);
            }
            _ => (),
        }

        let token = kind.with_span(location);

        tokens.push(Ok(token));
    }

    tokens
}
