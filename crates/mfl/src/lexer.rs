use ariadne::{Color, Label};
use intcast::IntCast;
use lasso::Spur;
use logos::{Lexer, Logos};
use tracing::debug_span;

use crate::{
    diagnostics,
    source_file::{FileId, SourceLocation, Spanned, WithSpan},
    Stores,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Insert {
    pub emit_struct: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Extract {
    pub emit_struct: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Integer {
    pub is_hex: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StringToken {
    pub id: Spur,
    pub is_c_str: bool,
}

fn is_newline(lex: &mut Lexer<'_, TokenKind>) {
    let ch = lex.slice().chars().next().unwrap();

    if ch == '\n' {
        lex.extras.line += 1;
        lex.extras.line_start_idx = lex.span().end;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Logos)]
#[logos(extras = Context)]
#[logos(skip "//[^\n]*")]
pub enum TokenKind {
    #[regex("[\t\n\r ]", is_newline)]
    // Never actually emitted, but we need it for the match logic.
    Whitespace,

    #[token("assert")]
    Assert,

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

    #[token("cast")]
    Cast,

    // We fixup afterwards like we do with strings.
    #[regex(r#"'([^'\\]|\\['\\rnt0])+'"#, |_| '0')]
    Char(char),

    #[token("::")]
    ColonColon,

    #[token("const")]
    Const,

    #[token("/")]
    Div,

    #[token("do")]
    Do,

    #[token(".")]
    Dot,

    #[token("drop")]
    Drop,

    #[token("dup")]
    Dup,

    #[token("elif")]
    Elif,

    #[token("else")]
    Else,

    #[token("end")]
    End,

    #[token("=")]
    Equal,

    #[token("stktrc")]
    EmitStack,

    #[token("exit")]
    Exit,

    #[token("xtr", |_| Extract{emit_struct: true})]
    #[token("xtrd", |_| Extract{emit_struct: false})]
    Extract(Extract),

    #[token("field")]
    Field,

    #[token("to")]
    GoesTo,

    #[token(">")]
    Greater,

    #[token(">=")]
    GreaterEqual,

    #[token("here", |_| Spur::default())]
    Here(Spur),

    #[regex("[_a-zA-Z][_a-zA-Z0-9]*")]
    Ident,

    #[token("if")]
    If,

    #[token("ins", |_| Insert{emit_struct: true})]
    #[token("insd", |_| Insert{emit_struct: false})]
    Insert(Insert),

    #[regex("[0-9][0-9_]*", |_| Integer{is_hex: false})]
    #[regex("0[xX][0-9A-Fa-f][0-9A-Fa-f_]*", |_| Integer{is_hex: true})]
    Integer(Integer),

    #[token("import")]
    Import,

    #[token("is")]
    Is,

    #[token("isnull")]
    IsNull,

    #[token("<")]
    Less,

    #[token("<=")]
    LessEqual,

    #[token("@")]
    Load,

    #[token("memory")]
    Memory,

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

    #[token(")")]
    ParenthesisClosed,

    #[token("(")]
    ParenthesisOpen,

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

    #[token("shl")]
    ShiftLeft,

    #[token("shr")]
    ShiftRight,

    #[token("sizeof")]
    SizeOf,

    #[token("]")]
    SquareBracketClosed,

    #[token("[")]
    SquareBracketOpen,

    #[token("*")]
    Star,

    // We do a fixup later, in the consume loop
    #[regex(r#""([^"\\]|\\["\\rnt0])*"c?"#, |_| StringToken{id: Spur::default(), is_c_str: false})]
    String(StringToken),

    #[token("!")]
    Store,

    #[token("struct")]
    Struct,

    #[token("swap")]
    Swap,

    #[token("syscall")]
    SysCall,

    #[token("union")]
    Union,

    #[token("unpack")]
    Unpack,

    #[token("while")]
    While,
}

impl TokenKind {
    pub fn is_matched_open(self) -> bool {
        matches!(
            self,
            TokenKind::ParenthesisOpen
                | TokenKind::SquareBracketOpen
                | TokenKind::If
                | TokenKind::Is
                | TokenKind::While
        )
    }

    pub fn is_matched_close(self) -> bool {
        matches!(
            self,
            TokenKind::ParenthesisClosed | TokenKind::SquareBracketClosed | TokenKind::End
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

pub struct Context {
    line: usize,
    line_start_idx: usize,
}

fn escape_string_or_char_literal(string: &str, is_string: bool) -> String {
    let mut escaped = String::with_capacity(string.len());
    let mut chars = string.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            escaped.push(ch);
            continue;
        }
        let next_ch = chars.next().unwrap();
        let real = match next_ch {
            '\'' if !is_string => '\'',
            '\"' if is_string => '\"',
            '\\' => '\\',
            'r' => '\r',
            'n' => '\n',
            't' => '\t',
            '0' => '\0',
            _ => unreachable!(),
        };
        escaped.push(real);
    }

    escaped
}

fn process_string(stores: &mut Stores, string: &str) -> (Spur, bool) {
    let (string, is_c_str) = if string.ends_with('c') {
        (&string[1..string.len() - 2], true)
    } else {
        (&string[1..string.len() - 1], false)
    };

    let mut new_string = escape_string_or_char_literal(string, true);
    // All strings are null terminated, as it makes supporting C-strings easier.
    new_string.push('\0');

    let id = stores.strings.intern(&new_string);

    (id, is_c_str)
}

pub(crate) fn lex_file(
    stores: &mut Stores,
    contents: &str,
    file_id: FileId,
) -> Result<Vec<Spanned<Token>>, ()> {
    let _span = debug_span!(stringify!(lexer::lex_file)).entered();

    let context = Context {
        line: 1,
        line_start_idx: 0,
    };

    let mut had_error = false;
    let mut ops = Vec::new();

    let mut lexer = TokenKind::lexer_with_extras(contents, context).spanned();

    while let Some((kind, span)) = lexer.next() {
        let span = span.start.to_u32().unwrap()..span.end.to_u32().unwrap();
        let location = SourceLocation::new(file_id, span.clone());

        let Ok(mut kind) = kind else {
            diagnostics::emit_error(
                stores,
                location,
                format!("unexpected character in input: `{:?}`", lexer.slice()),
                [Label::new(location).with_color(Color::Red)],
                None,
            );
            had_error = true;
            continue;
        };

        if kind == TokenKind::Whitespace {
            continue;
        }

        // We need to escape and intern the string, but we can't do that in the Logos
        // parser, so we do it here.
        match &mut kind {
            TokenKind::String(string_token) => {
                let (id, is_c_str) = process_string(stores, lexer.slice());
                string_token.is_c_str = is_c_str;
                string_token.id = id;
            }
            TokenKind::Char(ch) => {
                let literal = lexer.slice();
                let literal = &literal[1..literal.len() - 1];
                let escaped = escape_string_or_char_literal(literal, false);

                if escaped.chars().count() != 1 {
                    diagnostics::emit_error(
                        stores,
                        location,
                        "invalid char literal",
                        [Label::new(location).with_color(Color::Red)],
                        None,
                    );
                    had_error = true;
                    continue;
                }
                *ch = escaped.chars().next().unwrap();
            }
            TokenKind::Here(id) => {
                let filename = stores.source.name(file_id);
                let here_msg = format!(
                    "{filename}:{}:{}",
                    lexer.extras.line,
                    span.start - lexer.extras.line_start_idx.to_u32().unwrap()
                );
                *id = stores.strings.intern(&here_msg);
            }
            _ => (),
        }

        let lexeme = stores.strings.intern(lexer.slice());
        ops.push(Token::new(kind, lexeme).with_span(location));
    }

    if had_error {
        Err(())
    } else {
        Ok(ops)
    }
}
