use std::{fmt::Display, iter::Copied, ops::Not, slice::Iter, str::FromStr};

use ariadne::{Color, Label};
use num_traits::{PrimInt, Unsigned};

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{OpCode, UnresolvedIdent, UnresolvedOp, UnresolvedType},
    lexer::{Integer, Token, TokenKind},
    stores::source::{SourceLocation, Spanned, WithSpan},
    Stores,
};

pub type ParseOpResult = Result<(OpCode<UnresolvedOp>, SourceLocation), ()>;

pub(super) trait TokenIter: Iterator<Item = Spanned<Token>> + Clone {
    fn peek(&self) -> Option<Spanned<Token>> {
        self.clone().next()
    }
}
impl TokenIter for Copied<Iter<'_, Spanned<Token>>> {}

pub trait Recover<T, E> {
    fn recover(self, had_error: &mut ErrorSignal, fallback: T) -> T;
}

impl<T, E> Recover<T, E> for Result<T, E> {
    fn recover(self, had_error: &mut ErrorSignal, fallback: T) -> T {
        match self {
            Ok(kk) => kk,
            Err(_) => {
                had_error.set();
                fallback
            }
        }
    }
}

pub fn valid_type_token(t: TokenKind) -> bool {
    matches!(
        t,
        TokenKind::Ident
            | TokenKind::Integer { .. }
            | TokenKind::ColonColon
            | TokenKind::ParenthesisOpen
            | TokenKind::ParenthesisClosed
            | TokenKind::SquareBracketOpen
            | TokenKind::SquareBracketClosed
            | TokenKind::Ampersand
    )
}

pub fn expect_token(
    stores: &Stores,
    tokens: &mut impl TokenIter,
    kind_str: &str,
    expected: fn(TokenKind) -> bool,
    prev: Spanned<Token>,
) -> Result<Spanned<Token>, ()> {
    match tokens.peek() {
        Some(ident) if expected(ident.inner.kind) => tokens.next().ok_or(()),
        Some(ident) => {
            diagnostics::emit_error(
                stores,
                ident.location,
                format!(
                    "expected `{}`, found `{}`",
                    kind_str,
                    stores.strings.resolve(ident.inner.lexeme)
                ),
                Some(Label::new(ident.location).with_color(Color::Red)),
                None,
            );
            Err(())
        }
        None => {
            diagnostics::emit_error(
                stores,
                prev.location,
                "unexpected end of tokens",
                Some(Label::new(prev.location).with_color(Color::Red)),
                None,
            );
            Err(())
        }
    }
}

pub struct Delimited {
    pub open: Spanned<Token>,
    pub close: Spanned<Token>,
    pub list: Vec<Spanned<Token>>,
}

impl Delimited {
    pub fn fallback(tk: Spanned<Token>) -> Self {
        Self {
            open: tk,
            close: tk,
            list: Vec::new(),
        }
    }

    pub fn span(&self) -> SourceLocation {
        self.open.location.merge(self.close.location)
    }
}

pub struct Terminated {
    pub close: Spanned<Token>,
    pub list: Vec<Spanned<Token>>,
}

pub fn get_delimited_tokens(
    stores: &Stores,
    token_iter: &mut impl TokenIter,
    prev: Spanned<Token>,
    expected_len: Option<usize>,
    (open_delim_str, open_delim_fn): (&'static str, fn(TokenKind) -> bool),
    inner_tokens: (&'static str, fn(TokenKind) -> bool),
    close_token: (&'static str, fn(TokenKind) -> bool),
) -> Result<Delimited, ()> {
    let mut had_error = ErrorSignal::new();
    let open_token = expect_token(stores, token_iter, open_delim_str, open_delim_fn, prev)
        .recover(&mut had_error, prev);

    let terminated = get_terminated_tokens(
        stores,
        token_iter,
        open_token,
        expected_len,
        inner_tokens,
        close_token,
    )?;

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(Delimited {
            open: open_token,
            close: terminated.close,
            list: terminated.list,
        })
    }
}

pub fn get_terminated_tokens(
    stores: &Stores,
    token_iter: &mut impl TokenIter,
    open_token: Spanned<Token>,
    expected_len: Option<usize>,
    (token_str, token_fn): (&'static str, fn(TokenKind) -> bool),
    (close_delim_str, close_delim_fn): (&'static str, fn(TokenKind) -> bool),
) -> Result<Terminated, ()> {
    let mut had_error = ErrorSignal::new();
    let mut tokens = Vec::new();
    let mut depth = 0;
    let mut prev = open_token;

    // When parsing If, Elif, and While conditions, the terminating token is BraceOpen, however the
    // condition block itself can contain an If or While expression. We need to keep track of whether
    // we're expecting to stop on an OpenBrace.
    let mut expected_open_brace_count = 0;
    let close_is_open_brace = close_delim_fn(TokenKind::BraceOpen);
    loop {
        let Some(next_token) = token_iter.peek() else {
            diagnostics::emit_error(
                stores,
                prev.location,
                "unexpected end of tokens",
                Some(Label::new(prev.location).with_color(Color::Red)),
                None,
            );
            return Err(());
        };

        if close_is_open_brace && next_token.inner.kind.expects_brace() {
            expected_open_brace_count += 1;
        }

        if depth == 0 && expected_open_brace_count == 0 && close_delim_fn(next_token.inner.kind) {
            break; // The end of the list, so break the loop.
        }

        if close_is_open_brace
            && next_token.inner.kind == TokenKind::BraceOpen
            && expected_open_brace_count > 0
        {
            expected_open_brace_count -= 1;
        }

        if next_token.inner.kind.is_matched_open() {
            depth += 1;
        } else if next_token.inner.kind.is_matched_close() {
            depth -= 1;
        }

        let Ok(item_token) = expect_token(stores, token_iter, token_str, token_fn, prev) else {
            had_error.set();

            // If it's not the close token, we should consume it so we can continue.
            if !close_delim_fn(next_token.inner.kind) {
                token_iter.next();
            }

            continue;
        };
        tokens.push(item_token);
        prev = item_token;
    }

    let close_token = expect_token(stores, token_iter, close_delim_str, close_delim_fn, prev)
        .recover(&mut had_error, prev);

    if let Some(len) = expected_len {
        if len != tokens.len() {
            let range = open_token.location.merge(close_token.location);
            diagnostics::emit_error(
                stores,
                range,
                format!("expected {len} tokens, found {}", tokens.len()),
                [Label::new(range).with_color(Color::Red)],
                None,
            );
            had_error.set();
        }
    }

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(Terminated {
            close: close_token,
            list: tokens,
        })
    }
}

pub fn parse_unresolved_types(
    stores: &mut Stores,
    prev: Spanned<Token>,
    tokens: &[Spanned<Token>],
) -> Result<Vec<Spanned<UnresolvedType>>, ()> {
    let mut had_error = ErrorSignal::new();
    let mut types: Vec<Spanned<UnresolvedType>> = Vec::new();
    let mut token_iter = tokens.iter().copied();

    while token_iter.peek().is_some() {
        let Ok(ident) = expect_token(
            stores,
            &mut token_iter,
            "ident",
            |t| t == TokenKind::Ident || t == TokenKind::ColonColon,
            prev,
        ) else {
            had_error.set();
            token_iter.next(); // Consume the token so we can progress.
            continue;
        };

        let Ok((ident, last_token)) = parse_ident(stores, &mut had_error, &mut token_iter, ident)
        else {
            had_error.set();
            continue;
        };

        let mut type_span = ident.span;
        let mut parsed_type = UnresolvedType::Simple(ident);

        // This looks ugly
        while token_iter.peek().is_some_and(|t| {
            matches!(
                t.inner.kind,
                TokenKind::Ampersand | TokenKind::SquareBracketOpen
            )
        }) {
            let Some(next_token) = token_iter.peek() else {
                unreachable!()
            };

            match next_token.inner.kind {
                TokenKind::SquareBracketOpen => {
                    // Parsing an array!
                    let Ok(delim) = get_delimited_tokens(
                        stores,
                        &mut token_iter,
                        last_token,
                        Some(1),
                        ("[", |t| t == TokenKind::SquareBracketOpen),
                        ("integer", |t| matches!(t, TokenKind::Integer { .. })),
                        ("]", |t| t == TokenKind::SquareBracketClosed),
                    ) else {
                        had_error.set();
                        continue;
                    };

                    let len_token = delim.list[0];
                    let length = parse_integer_lexeme(stores, len_token)?;

                    type_span = type_span.merge(delim.close.location);
                    parsed_type = UnresolvedType::Array(Box::new(parsed_type), length);
                }
                TokenKind::Ampersand => {
                    // Parsing a pointer!
                    let Some(next) = token_iter.next() else {
                        unreachable!()
                    };

                    type_span = type_span.merge(next.location);
                    parsed_type = UnresolvedType::Pointer(Box::new(parsed_type));
                }
                _ => unreachable!(),
            }
        }

        types.push(parsed_type.with_span(type_span));
    }

    had_error.into_bool().not().then_some(types).ok_or(())
}

pub fn parse_ident(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut impl TokenIter,
    mut token: Spanned<Token>,
) -> Result<(UnresolvedIdent, Spanned<Token>), ()> {
    let mut import_span = token.location;
    let mut last_token = token;

    let (is_from_root, mut path) = if token.inner.kind == TokenKind::ColonColon {
        let ident = if token_iter.peek().is_some_and(|tk| {
            tk.inner.kind == TokenKind::Ident && tk.location.neighbour_of(token.location)
        }) {
            token_iter.next().unwrap()
        } else {
            diagnostics::emit_error(
                stores,
                token.location,
                "unexpected end of ident",
                Some(Label::new(token.location).with_color(Color::Red)),
                None,
            );
            had_error.set();
            return Err(());
        };

        last_token = ident;
        import_span = import_span.merge(ident.location);

        (true, vec![ident.map(|t| t.lexeme)])
    } else {
        (false, vec![token.map(|t| t.lexeme)])
    };

    while token_iter.peek().is_some_and(|t| {
        t.inner.kind == TokenKind::ColonColon && t.location.neighbour_of(last_token.location)
    }) {
        let colons = token_iter.next().unwrap(); // Consume the ColonColon.
        let item_id = if token_iter.peek().is_some_and(|tk| {
            tk.inner.kind == TokenKind::Ident && tk.location.neighbour_of(colons.location)
        }) {
            token_iter.next().unwrap()
        } else {
            diagnostics::emit_error(
                stores,
                colons.location,
                "unexpected end of ident",
                Some(Label::new(colons.location).with_color(Color::Red)),
                None,
            );
            had_error.set();
            return Err(());
        };

        last_token = item_id;
        import_span = import_span.merge(item_id.location);

        path.push(item_id.map(|t| t.lexeme));
    }

    let generic_params = if token_iter
        .peek()
        .is_some_and(|t| t.inner.kind == TokenKind::ParenthesisOpen)
    {
        let Ok(delim) = get_delimited_tokens(
            stores,
            token_iter,
            token,
            None,
            ("(", |t| t == TokenKind::ParenthesisOpen),
            ("Ident", valid_type_token),
            (")", |t| t == TokenKind::ParenthesisClosed),
        ) else {
            had_error.set();
            return Err(());
        };
        token.location = token.location.merge(delim.close.location);

        let span = delim.span();
        let Ok(unresolved_types) = parse_unresolved_types(stores, delim.open, &delim.list) else {
            had_error.set();
            return Err(());
        };

        if unresolved_types.is_empty() {
            diagnostics::emit_error(
                stores,
                span,
                "expected at least type, found 0",
                [Label::new(span).with_color(Color::Red)],
                None,
            );
            had_error.set();
            return Err(());
        }

        import_span = import_span.merge(delim.close.location);
        last_token = delim.close;

        Some(unresolved_types.into_iter().map(|ut| ut.inner).collect())
    } else {
        None
    };

    Ok((
        UnresolvedIdent {
            span: import_span,
            is_from_root,
            path,
            generic_params,
        },
        last_token,
    ))
}

pub fn parse_integer_lexeme<T>(stores: &Stores, int_token: Spanned<Token>) -> Result<T, ()>
where
    T: PrimInt + Unsigned + FromStr + Display,
{
    let TokenKind::Integer(Integer { is_hex }) = int_token.inner.kind else {
        panic!("ICE: called parse_integer_lexeme with a non-integer token")
    };
    let string = stores.strings.resolve(int_token.inner.lexeme);
    // Need to skip the "0x"
    let string = if is_hex { &string[2..] } else { string };

    let string: String = string.chars().filter(|&c| c != '_').collect();

    let res = if is_hex {
        T::from_str_radix(&string, 16)
    } else {
        T::from_str_radix(&string, 10)
    };
    let Ok(int) = res else {
        diagnostics::emit_error(
            stores,
            int_token.location,
            "integer out bounds",
            [Label::new(int_token.location)
                .with_color(Color::Red)
                .with_message(format!(
                    "integer must be in range {}..={}",
                    T::min_value(),
                    T::max_value()
                ))],
            None,
        );
        return Err(());
    };

    Ok(int)
}

pub fn parse_integer_param(
    stores: &Stores,
    token_iter: &mut impl TokenIter,
    token: Spanned<Token>,
) -> Result<(Spanned<u8>, SourceLocation), ()> {
    let delim = get_delimited_tokens(
        stores,
        token_iter,
        token,
        Some(1),
        ("(", |t| t == TokenKind::ParenthesisOpen),
        ("Integer", |t| matches!(t, TokenKind::Integer { .. })),
        (")", |t| t == TokenKind::ParenthesisClosed),
    )?;

    let count_token = delim.list[0];
    let count: u8 = parse_integer_lexeme(stores, count_token)?;
    Ok((count.with_span(count_token.location), delim.close.location))
}

pub fn parse_stack_def(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut impl TokenIter,
    prev_token: Spanned<Token>,
) -> Spanned<Vec<Spanned<UnresolvedType>>> {
    let stack = get_delimited_tokens(
        stores,
        token_iter,
        prev_token,
        None,
        ("[", |t| t == TokenKind::SquareBracketOpen),
        ("Ident", valid_type_token),
        ("]", |t| t == TokenKind::SquareBracketClosed),
    )
    .recover(had_error, Delimited::fallback(prev_token));
    let stack_location = stack.span();
    let unresolved_types =
        parse_unresolved_types(stores, stack.open, &stack.list).recover(had_error, Vec::new());

    unresolved_types.with_span(stack_location)
}
