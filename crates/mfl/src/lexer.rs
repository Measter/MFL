use std::fmt::{Display, Write};

use ariadne::{Color, Label};
use intcast::IntCast;
use lasso::Spur;
use logos::{Lexer, Logos};
use tracing::debug_span;

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    stores::source::{FileId, SourceLocation, Spanned, WithSpan},
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

    #[token("&")]
    Ampersand,

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

    #[token("}", |_| BracketKind::Brace)]
    #[token(")", |_| BracketKind::Paren)]
    #[token("]", |_| BracketKind::Square)]
    BracketClose(BracketKind),

    #[token("{", |_| BracketKind::Brace)]
    #[token("(", |_| BracketKind::Paren)]
    #[token("[", |_| BracketKind::Square)]
    BracketOpen(BracketKind),

    #[token("cast")]
    Cast,

    // We fixup afterwards like we do with strings.
    #[regex(r#"'([^'\\]|\\['\\rnt0])+'"#, |_| '0')]
    Char(char),

    #[token("::")]
    ColonColon,

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

    #[token("elif")]
    Elif,

    #[token("else")]
    Else,

    #[token("=")]
    Equal,

    #[token("stktrc")]
    EmitStack,

    #[token("exit")]
    Exit,

    #[token("xtr", |_| Extract{emit_struct: true})]
    #[token("xtrd", |_| Extract{emit_struct: false})]
    Extract(Extract),

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

    #[token("isnull")]
    IsNull,

    #[token("lang")]
    LangItem,

    #[token("<")]
    Less,

    #[token("<=")]
    LessEqual,

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

    #[token("*")]
    Star,

    // We do a fixup later, in the consume loop
    #[regex(r#""([^"\\]|\\["\\rnt0])*""#, |_| StringToken{id: Spur::default() })]
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

    #[token("var")]
    Variable,

    #[token("while")]
    While,
}

impl TokenKind {
    pub fn kind_str(self) -> &'static str {
        match self {
            TokenKind::Whitespace => "Whitespace",
            TokenKind::Ampersand => "&",
            TokenKind::Assert => "assert",
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
            TokenKind::Cast => "cast",
            TokenKind::Char(_) => "character literal",
            TokenKind::ColonColon => "::'",
            TokenKind::Const => "const",
            TokenKind::Comma => ",",
            TokenKind::Div => "/",
            TokenKind::Dot => ".",
            TokenKind::Drop => "drop",
            TokenKind::Dup => "dup",
            TokenKind::Elif => "elif",
            TokenKind::Else => "else",
            TokenKind::Equal => "=",
            TokenKind::EmitStack => "emit",
            TokenKind::Exit => "exit",
            TokenKind::Extract(Extract { emit_struct: true }) => "xtr",
            TokenKind::Extract(Extract { emit_struct: false }) => "xtrd",
            TokenKind::GoesTo => "to",
            TokenKind::Greater => ">",
            TokenKind::GreaterEqual => ">=",
            TokenKind::Here(_) => "here",
            TokenKind::Ident => "Ident",
            TokenKind::If => "if",
            TokenKind::Insert(Insert { emit_struct: true }) => "ins",
            TokenKind::Insert(Insert { emit_struct: false }) => "insd",
            TokenKind::Integer(_) => "integer literal",
            TokenKind::Import => "import",
            TokenKind::IsNull => "isnull",
            TokenKind::LangItem => "lang",
            TokenKind::Less => "<",
            TokenKind::LessEqual => "<=",
            TokenKind::Load => "@",
            TokenKind::Minus => "-",
            TokenKind::Module => "module",
            TokenKind::NotEqual => "!=",
            TokenKind::Over => "over",
            TokenKind::Pack => "pack",
            TokenKind::Plus => "+",
            TokenKind::Proc => "proc",
            TokenKind::Rem => "%",
            TokenKind::Return => "return",
            TokenKind::Reverse => "rev",
            TokenKind::Rot => "rot",
            TokenKind::ShiftLeft => "shl",
            TokenKind::ShiftRight => "shr",
            TokenKind::SizeOf => "sizeof",
            TokenKind::Star => "*",
            TokenKind::String(_) => "string literal",
            TokenKind::Store => "!",
            TokenKind::Struct => "struct",
            TokenKind::Swap => "swap",
            TokenKind::SysCall => "syscall",
            TokenKind::Union => "union",
            TokenKind::Unpack => "unpack",
            TokenKind::Variable => "var",
            TokenKind::While => "while",
        }
    }

    pub fn expects_brace_group(self) -> bool {
        matches!(
            self,
            TokenKind::If | TokenKind::Elif | TokenKind::Else | TokenKind::While
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

#[derive(Debug, Clone)]
pub struct TreeGroup {
    pub bracket_kind: BracketKind,
    pub open: Spanned<Token>,
    pub close: Option<Spanned<Token>>,
    pub tokens: Vec<TokenTree>,
}

impl TreeGroup {
    pub fn span(&self) -> SourceLocation {
        let last = self
            .close
            .map(|t| t.location)
            .or(self.tokens.last().map(TokenTree::span))
            .unwrap_or(self.open.location);

        self.open.location.merge(last)
    }

    pub fn last_token(&self) -> Spanned<Token> {
        self.close
            .or(self.tokens.last().map(TokenTree::last_token))
            .unwrap_or(self.open)
    }

    pub fn first_token(&self) -> Spanned<Token> {
        self.open
    }
}

#[derive(Debug, Clone)]
pub enum TokenTree {
    Single(Spanned<Token>),
    Group(TreeGroup),
}

impl TokenTree {
    pub fn span(&self) -> SourceLocation {
        match self {
            TokenTree::Single(tk) => tk.location,
            TokenTree::Group(tg) => tg.span(),
        }
    }

    pub fn last_token(&self) -> Spanned<Token> {
        match self {
            TokenTree::Single(tk) => *tk,
            TokenTree::Group(tg) => tg.last_token(),
        }
    }

    pub fn first_token(&self) -> Spanned<Token> {
        match self {
            TokenTree::Single(tk) => *tk,
            TokenTree::Group(tg) => tg.first_token(),
        }
    }

    #[inline]
    #[track_caller]
    pub fn unwrap_single(&self) -> Spanned<Token> {
        match self {
            TokenTree::Single(tk) => *tk,
            TokenTree::Group(_) => panic!("ICE: Tried to unwrap_single a Group"),
        }
    }

    #[inline]
    #[track_caller]
    pub fn unwrap_group(&self) -> &TreeGroup {
        match self {
            TokenTree::Single(_) => panic!("ICE: Tried to unwrap_group a Single"),
            TokenTree::Group(tg) => tg,
        }
    }

    pub fn expects_brace_group(&self) -> bool {
        matches!(self, TokenTree::Single(tk) if tk.inner.kind.expects_brace_group())
    }

    pub fn is_brace_group(&self) -> bool {
        matches!(self, TokenTree::Group(tg) if tg.bracket_kind == BracketKind::Brace)
    }

    pub fn kind_str(&self) -> &'static str {
        match self {
            TokenTree::Single(tk) => tk.inner.kind.kind_str(),
            TokenTree::Group(_) => "bracket group",
        }
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

fn process_string(stores: &mut Stores, string: &str) -> Spur {
    let string = &string[1..string.len() - 1];

    let mut new_string = escape_string_or_char_literal(string, true);
    // All strings are null terminated, as it makes supporting C-strings easier.
    new_string.push('\0');

    stores.strings.intern(&new_string)
}

pub(crate) fn lex_file(
    stores: &mut Stores,
    contents: &str,
    file_id: FileId,
) -> Result<Vec<TokenTree>, ()> {
    let _span = debug_span!(stringify!(lexer::lex_file)).entered();

    let context = Context {
        line: 1,
        line_start_idx: 0,
    };

    let mut had_error = ErrorSignal::new();
    let mut token_tree_group_stack = Vec::<TreeGroup>::new();
    let mut token_tree_stream = Vec::<TokenTree>::new();

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
            had_error.set();
            continue;
        };

        if kind == TokenKind::Whitespace {
            continue;
        }

        // We need to escape and intern the string, but we can't do that in the Logos
        // parser, so we do it here.
        match &mut kind {
            TokenKind::String(string_token) => {
                string_token.id = process_string(stores, lexer.slice());
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
                    had_error.set();
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
        let token = Token::new(kind, lexeme).with_span(location);

        match kind {
            TokenKind::BracketOpen(bk) => token_tree_group_stack.push(TreeGroup {
                bracket_kind: bk,
                open: token,
                close: None,
                tokens: Vec::new(),
            }),
            TokenKind::BracketClose(tk) if !token_tree_group_stack.is_empty() => {
                let last = token_tree_group_stack.last().unwrap();
                let tt_val = if last.bracket_kind == tk {
                    let mut cur_group = token_tree_group_stack.pop().unwrap();
                    cur_group.close = Some(token);
                    TokenTree::Group(cur_group)
                } else {
                    diagnostics::emit_error(
                        stores,
                        token.location,
                        "unmatched bracket",
                        [Label::new(token.location).with_color(Color::Red)],
                        None,
                    );
                    had_error.set();

                    TokenTree::Single(token)
                };

                let stream = token_tree_group_stack
                    .last_mut()
                    .map(|tg| &mut tg.tokens)
                    .unwrap_or(&mut token_tree_stream);
                stream.push(tt_val);
            }
            _ => {
                let stream = token_tree_group_stack
                    .last_mut()
                    .map(|tg| &mut tg.tokens)
                    .unwrap_or(&mut token_tree_stream);
                stream.push(TokenTree::Single(token));
            }
        }
    }

    while let Some(cur_group) = token_tree_group_stack.pop() {
        diagnostics::emit_error(
            stores,
            cur_group.open.location,
            "unclosed bracket",
            [Label::new(cur_group.open.location).with_color(Color::Red)],
            None,
        );
        had_error.set();

        let stream = token_tree_group_stack
            .last_mut()
            .map(|tg| &mut tg.tokens)
            .unwrap_or(&mut token_tree_stream);
        stream.push(TokenTree::Group(cur_group));
    }

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(token_tree_stream)
    }
}

#[allow(unused)]
fn pretty_print_tree(tree: &Vec<TokenTree>, depth: usize) {
    for tt in tree {
        match tt {
            TokenTree::Single(tk) => {
                eprintln!("{:width$}{:?}", " ", tk.inner.kind, width = depth * 4);
            }
            TokenTree::Group(tg) => {
                eprintln!(
                    "{:width$}{:?}",
                    " ",
                    TokenKind::BracketOpen(tg.bracket_kind),
                    width = depth * 4
                );
                pretty_print_tree(&tg.tokens, depth + 1);
                if let Some(ctk) = tg.close {
                    eprintln!(
                        "{:width$}{:?}",
                        " ",
                        TokenKind::BracketClose(tg.bracket_kind),
                        width = depth * 4
                    );
                }
            }
        }
    }
}
