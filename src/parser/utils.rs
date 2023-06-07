use std::{fmt::Display, iter::Peekable, ops::Not, str::FromStr};

use ariadne::{Color, Label};
use num::{PrimInt, Unsigned};

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{Token, TokenKind},
    opcode::UnresolvedIdent,
    source_file::{SourceLocation, SourceStorage, Spanned},
    type_store::{UnresolvedType, UnresolvedTypeTokens},
};

pub trait Recover<T, E> {
    fn recover(self, had_error: &mut bool, fallback: T) -> T;
}

impl<T, E> Recover<T, E> for Result<T, E> {
    fn recover(self, had_error: &mut bool, fallback: T) -> T {
        match self {
            Ok(kk) => kk,
            Err(_) => {
                *had_error = true;
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
    )
}

pub fn expect_token<'a>(
    tokens: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    kind_str: &str,
    mut expected: impl FnMut(TokenKind) -> bool,
    prev: Spanned<Token>,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(usize, Spanned<Token>), ()> {
    match tokens.peek() {
        Some((_, ident)) if expected(ident.inner.kind) => {
            tokens.next().map(|(a, b)| (a, *b)).ok_or(())
        }
        Some((_, ident)) => {
            diagnostics::emit_error(
                ident.location,
                format!(
                    "expected `{}`, found `{}`",
                    kind_str,
                    interner.resolve_lexeme(ident.inner.lexeme)
                ),
                Some(Label::new(ident.location).with_color(Color::Red)),
                None,
                source_store,
            );
            Err(())
        }
        None => {
            diagnostics::emit_error(
                prev.location,
                "unexpected end of tokens",
                Some(Label::new(prev.location).with_color(Color::Red)),
                None,
                source_store,
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

pub fn parse_delimited_token_list<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    prev: Spanned<Token>,
    expected_len: Option<usize>,
    (open_delim_str, open_delim_fn): (&'static str, impl FnMut(TokenKind) -> bool),
    (token_str, mut token_fn): (&'static str, impl FnMut(TokenKind) -> bool),
    (close_delim_str, mut close_delim_fn): (&'static str, impl FnMut(TokenKind) -> bool),
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<Delimited, ()> {
    let mut had_error = false;
    let (_, open_token) = expect_token(
        token_iter,
        open_delim_str,
        open_delim_fn,
        prev,
        interner,
        source_store,
    )
    .recover(&mut had_error, (0, prev));

    let mut tokens = Vec::new();

    let mut prev = open_token;
    let mut depth = 0;

    loop {
        let Some(next_token) = token_iter.peek().map(|(_, t)| **t) else {
                diagnostics::emit_error(
                    prev.location,
                    "unexpected end of tokens",
                    Some(
                        Label::new(prev.location)
                            .with_color(Color::Red)
                    ),
                    None,
                    source_store,
                );
                return Err(());
            };

        if depth == 0 && close_delim_fn(next_token.inner.kind) {
            break; // The end of the list, so break the loop.
        }

        if next_token.inner.kind.is_matched_open() {
            depth += 1;
        } else if next_token.inner.kind.is_matched_close() {
            depth -= 1;
        }

        let Ok((_, item_token)) = expect_token(
                token_iter,
                token_str,
                &mut token_fn,
                prev,
                interner,
                source_store,
            ) else {
                had_error = true;

                // If it's not the close token, we should consume it so we can continue.
                if !close_delim_fn(next_token.inner.kind) {
                    token_iter.next();
                }

                continue;
            };
        tokens.push(item_token);
        prev = item_token;
    }

    let (_, close_token) = expect_token(
        token_iter,
        close_delim_str,
        close_delim_fn,
        prev,
        interner,
        source_store,
    )
    .recover(&mut had_error, (0, prev));

    if let Some(len) = expected_len {
        if len != tokens.len() {
            let range = open_token.location.merge(close_token.location);
            diagnostics::emit_error(
                range,
                format!("expected {len} tokens, found {}", tokens.len()),
                [Label::new(range).with_color(Color::Red)],
                None,
                source_store,
            );
            had_error = true;
        }
    }

    had_error
        .not()
        .then_some(Delimited {
            open: open_token,
            list: tokens,
            close: close_token,
        })
        .ok_or(())
}

pub fn parse_unresolved_types(
    interner: &Interners,
    source_store: &SourceStorage,
    prev: Spanned<Token>,
    tokens: &[Spanned<Token>],
) -> Result<Vec<Spanned<UnresolvedTypeTokens>>, ()> {
    let mut had_error = false;
    let mut types: Vec<Spanned<UnresolvedTypeTokens>> = Vec::new();
    let mut token_iter = tokens.iter().enumerate().peekable();

    while token_iter.peek().is_some() {
        let Ok((_, ident)) = expect_token(
            &mut token_iter,
            "ident",
            |t| t == TokenKind::Ident,
            prev,
            interner,
            source_store,
        ) else {
            had_error = true;
            token_iter.next(); // Consume the token so we can progress.
            continue;
        };

        let mut type_span = ident.location;

        let mut base_path = vec![ident.map(|t| t.lexeme)];
        while token_iter
            .peek()
            .is_some_and(|(_, t)| t.inner.kind == TokenKind::ColonColon)
        {
            let (_, colon) = token_iter.next().unwrap();
            let (_, next_seg) = expect_token(
                &mut token_iter,
                "ident",
                |t| t == TokenKind::Ident,
                *colon,
                interner,
                source_store,
            )?;
            base_path.push(next_seg.map(|t| t.lexeme));
            type_span = type_span.merge(next_seg.location);
        }

        let base_type = if token_iter
            .peek()
            .is_some_and(|(_, t)| t.inner.kind == TokenKind::ParenthesisOpen)
        {
            let Ok(delim) = parse_delimited_token_list(
                &mut token_iter,
                ident,
                None,
                ("(", |t| t == TokenKind::ParenthesisOpen),
                ("Type", valid_type_token),
                (")", |t| t == TokenKind::ParenthesisClosed),
                interner,
                source_store,
            ) else {
                had_error = true;
                continue;
            };

            type_span = type_span.merge(delim.close.location);
            let diag_span = delim.span();

            let Ok(mut unresolved_types) = parse_unresolved_types(interner, source_store, delim.open, &delim.list) else {
                had_error = true;
                continue;
            };

            type_span = unresolved_types
                .iter()
                .fold(type_span, |acc, tokens| acc.merge(tokens.location));

            let lexeme = interner.resolve_lexeme(ident.inner.lexeme);
            if base_path.len() == 1 && lexeme == "ptr" {
                if unresolved_types.len() != 1 {
                    diagnostics::emit_error(
                        diag_span,
                        format!("expected 1 type, found {}", unresolved_types.len()),
                        [Label::new(diag_span).with_color(Color::Red)],
                        None,
                        source_store,
                    );
                    had_error = true;
                    continue;
                }

                UnresolvedTypeTokens::Pointer(Box::new(unresolved_types.pop().unwrap().inner))
            } else {
                UnresolvedTypeTokens::GenericInstance {
                    type_name: base_path,
                    params: unresolved_types.into_iter().map(|t| t.inner).collect(),
                }
            }
        } else {
            UnresolvedTypeTokens::Simple(base_path)
        };

        let parsed_type = if token_iter
            .peek()
            .is_some_and(|(_, t)| t.inner.kind == TokenKind::SquareBracketOpen)
        {
            // Parsing an array!
            let Ok(delim) = parse_delimited_token_list(
                &mut token_iter,
                ident,
                Some(1),
                ("[", |t| t == TokenKind::SquareBracketOpen),
                ("integer", |t| matches!( t, TokenKind::Integer{ .. })),
                ("]", |t| t == TokenKind::SquareBracketClosed),
                interner,
                source_store,
            ) else {
                had_error = true;
                continue;
            };

            let len_token = delim.list[0];
            let length = parse_integer_lexeme(len_token, interner, source_store)?;
            type_span = type_span.merge(delim.close.location);

            UnresolvedTypeTokens::Array(Box::new(base_type), length)
        } else {
            base_type
        };

        types.push(parsed_type.with_span(type_span));
    }

    had_error.not().then_some(types).ok_or(())
}

pub fn parse_ident<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    interner: &Interners,
    source_store: &SourceStorage,
    had_error: &mut bool,
    mut token: Spanned<Token>,
) -> Result<UnresolvedIdent, ()> {
    let mut path = vec![token.map(|t| t.lexeme)];

    while token_iter
        .peek()
        .is_some_and(|(_, t)| t.inner.kind == TokenKind::ColonColon)
    {
        let (_, colons) = token_iter.next().unwrap(); // Consume the ColonColon.
        let (_, item_id) = expect_token(
            token_iter,
            "ident",
            |k| k == TokenKind::Ident,
            *colons,
            interner,
            source_store,
        )?;

        path.push(item_id.map(|t| t.lexeme));
    }

    let generic_params = if token_iter
        .peek()
        .is_some_and(|(_, t)| t.inner.kind == TokenKind::ParenthesisOpen)
    {
        let Ok(delim) = parse_delimited_token_list(
            token_iter,
            token,
            None,
            ("(", |t| t == TokenKind::ParenthesisOpen),
            ("Ident", valid_type_token),
            (")", |t| t == TokenKind::ParenthesisClosed),
            interner,
            source_store,
        ) else {
            *had_error = true;
            return Err(());
        };
        token.location = token.location.merge(delim.close.location);

        let span = delim.span();
        let Ok( unresolved_types) = parse_unresolved_types(interner, source_store, delim.open, &delim.list) else {
            *had_error = true;
            return Err(());
        };

        if unresolved_types.is_empty() {
            diagnostics::emit_error(
                span,
                "expected at least type, found 0",
                [Label::new(span).with_color(Color::Red)],
                None,
                source_store,
            );
            *had_error = true;
            return Err(());
        }

        unresolved_types
            .into_iter()
            .map(|ut| UnresolvedType::Tokens(ut.inner))
            .collect()
    } else {
        Vec::new()
    };

    Ok(UnresolvedIdent {
        path,
        generic_params,
    })
}

pub fn parse_integer_lexeme<T>(
    int_token: Spanned<Token>,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<T, ()>
where
    T: PrimInt + Unsigned + FromStr + Display,
{
    let TokenKind::Integer{ lexeme, is_hex } = int_token.inner.kind else { panic!("ICE: called parse_integer_lexeme with a non-integer token") };
    let string = interner.resolve_lexeme(lexeme);
    let res = if is_hex {
        T::from_str_radix(string, 16)
    } else {
        T::from_str_radix(string, 10)
    };
    let Ok(int) = res else {
        diagnostics::emit_error(
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
            source_store,
        );
        return Err(());
    };

    Ok(int)
}
