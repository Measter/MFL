use std::{collections::VecDeque, fmt::Display, iter::Peekable, ops::Not, str::FromStr};

use ariadne::{Color, Label};
use intcast::IntCast;
use lasso::Spur;
use num::{PrimInt, Unsigned};
use smallvec::SmallVec;
use tracing::debug_span;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{Token, TokenKind},
    opcode::{Direction, If, IntKind, Op, OpCode, OpId, While},
    source_file::{SourceLocation, SourceStorage, Spanned, WithSpan},
    type_store::{
        IntWidth, Signedness, UnresolvedField, UnresolvedStruct, UnresolvedType,
        UnresolvedTypeTokens,
    },
};

use super::{ItemId, ItemKind, ItemSignatureUnresolved, ModuleQueueType, Program};

trait Recover<T, E> {
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

fn valid_type_token(t: TokenKind) -> bool {
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

fn expect_token<'a>(
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

fn parse_delimited_token_list<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    prev: Spanned<Token>,
    expected_len: Option<usize>,
    (open_delim_str, open_delim_fn): (&'static str, impl FnMut(TokenKind) -> bool),
    (token_str, mut token_fn): (&'static str, impl FnMut(TokenKind) -> bool),
    (close_delim_str, mut close_delim_fn): (&'static str, impl FnMut(TokenKind) -> bool),
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(Spanned<Token>, Vec<Spanned<Token>>, Spanned<Token>), ()> {
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
        .then_some((open_token, tokens, close_token))
        .ok_or(())
}

fn parse_unresolved_types(
    interner: &Interners,
    source_store: &SourceStorage,
    prev: Spanned<Token>,
    tokens: Vec<Spanned<Token>>,
) -> Result<Vec<(UnresolvedTypeTokens, SourceLocation)>, ()> {
    let mut had_error = false;
    let mut types: Vec<(UnresolvedTypeTokens, SourceLocation)> = Vec::new();
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

        let base_type = if matches!(token_iter.peek(), Some((_, t)) if t.inner.kind == TokenKind::ParenthesisOpen)
        {
            let Ok((open_paren, ident_tokens, close_paren)) = parse_delimited_token_list(
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

            type_span = type_span.merge(close_paren.location);

            let Ok(mut unresolved_types) = parse_unresolved_types(interner, source_store, open_paren, ident_tokens) else {
                had_error = true;
                continue;
            };

            if unresolved_types.len() != 1 {
                let span = open_paren.location.merge(close_paren.location);
                diagnostics::emit_error(
                    span,
                    format!("expected 1 type, found {}", unresolved_types.len()),
                    [Label::new(span).with_color(Color::Red)],
                    None,
                    source_store,
                );
                had_error = true;
                continue;
            }

            let (unresolved_type, span) = unresolved_types.pop().unwrap();
            type_span = type_span.merge(span);
            let lexeme = interner.resolve_lexeme(ident.inner.lexeme);
            if lexeme == "ptr" {
                UnresolvedTypeTokens::Pointer(Box::new(unresolved_type))
            } else {
                let ident = parse_ident(&mut token_iter, interner, source_store, ident)
                    .recover(&mut had_error, vec![ident.map(|t| t.lexeme)]);
                UnresolvedTypeTokens::GenericInstance {
                    type_name: ident,
                    param: Box::new(unresolved_type),
                }
            }
        } else {
            let ident = parse_ident(&mut token_iter, interner, source_store, ident)
                .recover(&mut had_error, vec![ident.map(|t| t.lexeme)]);
            UnresolvedTypeTokens::Simple(ident)
        };

        let parsed_type = if matches!(token_iter.peek(), Some((_, t)) if t.inner.kind == TokenKind::SquareBracketOpen)
        {
            // Parsing an array!
            let Ok((_, ident_tokens, close_bracket)) = parse_delimited_token_list(
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

            let len_token = ident_tokens[0];
            let length = parse_integer_lexeme(len_token, interner, source_store)?;
            type_span = type_span.merge(close_bracket.location);

            UnresolvedTypeTokens::Array(Box::new(base_type), length)
        } else {
            base_type
        };

        types.push((parsed_type, type_span));
    }

    had_error.not().then_some(types).ok_or(())
}

fn parse_integer_lexeme<T>(
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
    let int = match res {
        Ok(c) => c,
        Err(_) => {
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
        }
    };

    Ok(int)
}

fn parse_integer_op<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    is_known_negative: bool,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(OpCode, SourceLocation), ()> {
    let mut had_error = false;
    let mut overall_location = token.location;
    let literal_value: u64 = match parse_integer_lexeme(token, interner, source_store) {
        Ok(lit) => lit,
        Err(_) => {
            had_error = true;
            0
        }
    };

    if is_known_negative && literal_value.to_i64().is_none() {
        diagnostics::emit_error(
            token.location,
            "literal out of range of signed integer",
            [Label::new(token.location).with_color(Color::Red)],
            None,
            source_store,
        );
        had_error = true;
    }

    let (width, value) = if matches!(token_iter.peek(), Some((_,tk)) if tk.inner.kind == TokenKind::ParenthesisOpen)
    {
        let (_, ident_token, close_paren) = parse_delimited_token_list(
            token_iter,
            token,
            Some(1),
            ("(", |t| t == TokenKind::ParenthesisOpen),
            ("Ident", |t| t == TokenKind::Ident),
            (")", |t| t == TokenKind::ParenthesisClosed),
            interner,
            source_store,
        )?;
        let ident_token = ident_token[0];
        overall_location = overall_location.merge(close_paren.location);

        let (width, is_signed_kind) = match interner.resolve_lexeme(ident_token.inner.lexeme) {
            "u8" => (IntWidth::I8, Signedness::Unsigned),
            "s8" => (IntWidth::I8, Signedness::Signed),
            "u16" => (IntWidth::I16, Signedness::Unsigned),
            "s16" => (IntWidth::I16, Signedness::Signed),
            "u32" => (IntWidth::I32, Signedness::Unsigned),
            "s32" => (IntWidth::I32, Signedness::Signed),
            "u64" => (IntWidth::I64, Signedness::Unsigned),
            "s64" => (IntWidth::I64, Signedness::Signed),

            _ => {
                diagnostics::emit_error(
                    ident_token.location,
                    "invalid integer type",
                    [Label::new(ident_token.location)
                        .with_color(Color::Red)
                        .with_message("unknown type")],
                    None,
                    source_store,
                );
                return Err(());
            }
        };

        // The user specified an unsigned type, but gave a negative literal.
        if is_signed_kind == Signedness::Unsigned && is_known_negative {
            diagnostics::emit_error(
                ident_token.location,
                "signed integer literal with unsigned type kind",
                [Label::new(token.location).with_color(Color::Red)],
                None,
                source_store,
            );
            return Err(());
        }

        let int_value = match is_signed_kind {
            Signedness::Signed => {
                let value: i64 = literal_value as i64;
                let value = if is_known_negative { -value } else { value };

                if !width.bounds_signed().contains(&value) {
                    diagnostics::emit_error(
                        token.location,
                        "literal out of bounds",
                        [Label::new(token.location)
                            .with_color(Color::Red)
                            .with_message(format!(
                                "valid range for {} is {:?}",
                                width.name(is_signed_kind),
                                width.bounds_signed(),
                            ))],
                        None,
                        source_store,
                    );
                    return Err(());
                }
                IntKind::Signed(value)
            }
            Signedness::Unsigned => {
                if !width.bounds_unsigned().contains(&literal_value) {
                    diagnostics::emit_error(
                        token.location,
                        "literal out of bounds",
                        [Label::new(token.location)
                            .with_color(Color::Red)
                            .with_message(format!(
                                "valid range for {} is {:?}",
                                width.name(is_signed_kind),
                                width.bounds_unsigned(),
                            ))],
                        None,
                        source_store,
                    );
                    return Err(());
                }
                IntKind::Unsigned(literal_value)
            }
        };

        (width, int_value)
    } else if is_known_negative {
        let sizes = [IntWidth::I8, IntWidth::I16, IntWidth::I32, IntWidth::I64];
        let mut width = IntWidth::I64;
        let literal_value = -literal_value.to_i64().unwrap();

        for size in sizes {
            if size.bounds_signed().contains(&literal_value) {
                width = size;
                break;
            }
        }

        (width, IntKind::Signed(literal_value))
    } else {
        let sizes = [IntWidth::I8, IntWidth::I16, IntWidth::I32, IntWidth::I64];
        let mut width = IntWidth::I64;

        for size in sizes {
            if size.bounds_unsigned().contains(&literal_value) {
                width = size;
                break;
            }
        }

        (width, IntKind::Unsigned(literal_value))
    };

    // Return down here so that we consume any given parameters.
    if had_error {
        return Err(());
    }

    Ok((OpCode::PushInt { width, value }, overall_location))
}

pub fn parse_item_body(
    program: &mut Program,
    tokens: &[Spanned<Token>],
    op_id_gen: &mut impl FnMut() -> OpId,
    interner: &Interners,
    parent_id: ItemId,
    source_store: &SourceStorage,
) -> Result<Vec<Op>, ()> {
    let mut ops = Vec::new();
    let mut had_error = false;

    let mut token_iter = tokens.iter().enumerate().peekable();
    while let Some((_, token)) = token_iter.next() {
        let mut token = *token;
        let kind = match token.inner.kind {
            TokenKind::Drop
            | TokenKind::Dup
            | TokenKind::Over
            | TokenKind::Reverse
            | TokenKind::Swap
            | TokenKind::SysCall => {
                let count = if matches!(token_iter.peek(), Some((_,tk)) if tk.inner.kind == TokenKind::ParenthesisOpen)
                {
                    let Ok((_, count_token, close_paren)) = parse_delimited_token_list(
                        &mut token_iter,
                        token,
                        Some(1),
                        ("(", |t| t == TokenKind::ParenthesisOpen),
                        ("Integer", |t| matches!(t, TokenKind::Integer{ .. })),
                        (")", |t| t == TokenKind::ParenthesisClosed),
                        interner,
                        source_store,
                    ) else {
                        had_error = true;
                        continue;
                    };

                    token.location = token.location.merge(close_paren.location);

                    let count_token = count_token[0];
                    let count: u8 = parse_integer_lexeme(count_token, interner, source_store)?;
                    count.with_span(count_token.location)
                } else {
                    let default_amount = if token.inner.kind == TokenKind::Reverse {
                        2
                    } else {
                        1
                    };
                    default_amount.with_span(token.location)
                };

                match token.inner.kind {
                    TokenKind::Drop => OpCode::Drop { count },
                    TokenKind::Dup => OpCode::Dup { count },
                    TokenKind::Over => OpCode::Over { depth: count },
                    TokenKind::Reverse => OpCode::Reverse { count },
                    TokenKind::Swap => OpCode::Swap { count },
                    TokenKind::SysCall => OpCode::SysCall { arg_count: count },

                    _ => unreachable!(),
                }
            }

            TokenKind::Pack => {
                let Ok((open_paren, count_token, close_paren)) = parse_delimited_token_list(
                    &mut token_iter,
                    token,
                    None,
                    ("(", |t| t == TokenKind::ParenthesisOpen),
                    ("integer or type", valid_type_token),
                    (")", |t| t == TokenKind::ParenthesisClosed),
                    interner,
                    source_store,
                ) else {
                    had_error = true;
                    continue;
                };

                token.location = token.location.merge(close_paren.location);

                if count_token.len() == 1
                    && matches!(count_token[0].inner.kind, TokenKind::Integer { .. })
                {
                    let count_token = count_token[0];
                    let count = parse_integer_lexeme(count_token, interner, source_store)?;

                    OpCode::PackArray { count }
                } else {
                    let Ok(mut unresolved_types) = parse_unresolved_types(interner, source_store, open_paren, count_token) else {
                    had_error = true;
                    continue;
                };

                    if unresolved_types.len() != 1 {
                        let span = open_paren.location.merge(close_paren.location);
                        diagnostics::emit_error(
                            span,
                            format!("expected 1 type, found {}", unresolved_types.len()),
                            [Label::new(span).with_color(Color::Red)],
                            None,
                            source_store,
                        );
                        had_error = true;
                        continue;
                    }

                    let (unresolved_type, _) = unresolved_types.pop().unwrap();
                    OpCode::UnresolvedPackStruct {
                        unresolved_type: UnresolvedType::Tokens(unresolved_type),
                    }
                }
            }
            TokenKind::Unpack => OpCode::Unpack,
            TokenKind::Extract { .. } | TokenKind::Insert { .. } => {
                if matches!(token_iter.peek(), Some((_,tk)) if tk.inner.kind == TokenKind::ParenthesisOpen)
                {
                    let Ok((_, ident_token, close_paren)) = parse_delimited_token_list(
                        &mut token_iter,
                        token,
                        Some(1),
                        ("(", |t| t == TokenKind::ParenthesisOpen),
                        ("ident", |t| t == TokenKind::Ident),
                        (")", |t| t == TokenKind::ParenthesisClosed),
                        interner,
                        source_store,
                    ) else {
                        had_error = true;
                        continue;
                    };

                    token.location = token.location.merge(close_paren.location);

                    let ident_token = ident_token[0];
                    match token.inner.kind {
                        TokenKind::Extract { emit_struct } => OpCode::ExtractStruct {
                            emit_struct,
                            field_name: ident_token.map(|t| t.lexeme),
                        },
                        TokenKind::Insert { emit_struct } => OpCode::InsertStruct {
                            emit_struct,
                            field_name: ident_token.map(|t| t.lexeme),
                        },
                        _ => unreachable!(),
                    }
                } else {
                    match token.inner.kind {
                        TokenKind::Extract { emit_struct } => OpCode::ExtractArray {
                            emit_array: emit_struct,
                        },
                        TokenKind::Insert { emit_struct } => OpCode::InsertArray {
                            emit_array: emit_struct,
                        },
                        _ => unreachable!(),
                    }
                }
            }

            TokenKind::Rot => {
                let Ok((_, tokens, close_paren)) = parse_delimited_token_list(&mut token_iter,
                    token,
                    Some(3),
                    ("(", |t| t == TokenKind::ParenthesisOpen),
                    ("", |_| true),
                    (")", |t| t == TokenKind::ParenthesisClosed),
                    interner,
                    source_store
                )
                else {
                    had_error = true;
                    continue;
                };
                token.location = token.location.merge(close_paren.location);

                let mut local_error = false;
                let [item_count_token, direction_token, shift_count_token] = &*tokens else { unreachable!() };
                let item_count_token = *item_count_token;
                let shift_count_token = *shift_count_token;

                let item_count =
                    if !matches!(item_count_token.inner.kind, TokenKind::Integer { .. }) {
                        diagnostics::emit_error(
                            item_count_token.location,
                            format!(
                                "expected `integer`, found `{}`",
                                interner.resolve_lexeme(item_count_token.inner.lexeme)
                            ),
                            Some(Label::new(item_count_token.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        local_error = true;
                        1
                    } else {
                        parse_integer_lexeme(item_count_token, interner, source_store)?
                    };

                let shift_count =
                    if !matches!(shift_count_token.inner.kind, TokenKind::Integer { .. }) {
                        diagnostics::emit_error(
                            shift_count_token.location,
                            format!(
                                "expected `integer`, found `{}`",
                                interner.resolve_lexeme(shift_count_token.inner.lexeme)
                            ),
                            Some(Label::new(shift_count_token.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        local_error = true;
                        1
                    } else {
                        parse_integer_lexeme(shift_count_token, interner, source_store)?
                    };

                let direction = match direction_token.inner.kind {
                    TokenKind::Less => Direction::Left,
                    TokenKind::Greater => Direction::Right,
                    _ => {
                        diagnostics::emit_error(
                            direction_token.location,
                            format!(
                                "expected `<` or `>`, found `{}`",
                                interner.resolve_lexeme(direction_token.inner.lexeme)
                            ),
                            Some(Label::new(direction_token.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        local_error = true;
                        Direction::Left
                    }
                };

                if local_error {
                    had_error = true;
                    continue;
                }

                OpCode::Rot {
                    item_count: item_count.with_span(item_count_token.location),
                    direction,
                    shift_count: shift_count.with_span(shift_count_token.location),
                }
            }

            TokenKind::Cast | TokenKind::SizeOf => {
                let Ok((open_paren, ident_tokens, close_paren)) = parse_delimited_token_list(
                    &mut token_iter,
                    token,
                    None,
                    ("(", |t| t == TokenKind::ParenthesisOpen),
                    ("Ident", valid_type_token),
                    (")", |t| t == TokenKind::ParenthesisClosed),
                    interner,
                    source_store,
                ) else {
                    had_error = true;
                    continue;
                };
                token.location = token.location.merge(close_paren.location);

                let Ok(mut unresolved_types) = parse_unresolved_types(interner, source_store, open_paren, ident_tokens) else {
                    had_error = true;
                    continue;
                };

                if unresolved_types.len() != 1 {
                    let span = open_paren.location.merge(close_paren.location);
                    diagnostics::emit_error(
                        span,
                        format!("expected 1 type, found {}", unresolved_types.len()),
                        [Label::new(span).with_color(Color::Red)],
                        None,
                        source_store,
                    );
                    had_error = true;
                    continue;
                }

                let (unresolved_type, _) = unresolved_types.pop().unwrap();

                match token.inner.kind {
                    TokenKind::Cast => OpCode::UnresolvedCast {
                        unresolved_type: UnresolvedType::Tokens(unresolved_type),
                    },
                    TokenKind::SizeOf => OpCode::UnresolvedSizeOf {
                        unresolved_type: UnresolvedType::Tokens(unresolved_type),
                    },
                    _ => unreachable!(),
                }
            }

            TokenKind::Load => OpCode::Load,
            TokenKind::Store => OpCode::Store,

            TokenKind::IsNull => OpCode::IsNull,
            TokenKind::Equal => OpCode::Equal,
            TokenKind::Greater => OpCode::Greater,
            TokenKind::GreaterEqual => OpCode::GreaterEqual,
            TokenKind::Less => OpCode::Less,
            TokenKind::LessEqual => OpCode::LessEqual,
            TokenKind::NotEqual => OpCode::NotEq,

            TokenKind::Boolean(b) => OpCode::PushBool(b),
            TokenKind::Char(ch) => OpCode::PushInt {
                width: IntWidth::I8,
                value: IntKind::Unsigned((ch as u8).to_u64()),
            },
            TokenKind::Ident => {
                let Ok(ident) = parse_ident(&mut token_iter, interner, source_store, token) else {
                    had_error = true;
                    continue;
                };

                OpCode::UnresolvedIdent(ident)
            }
            TokenKind::Integer { .. } => {
                let Ok((int, location)) = parse_integer_op(&mut token_iter, token, false, interner, source_store) else {
                    had_error = true;
                    continue;
                };

                token.location = location;
                int
            }
            TokenKind::String { id, is_c_str } => OpCode::PushStr { id, is_c_str },
            TokenKind::Here(id) => OpCode::PushStr {
                id,
                is_c_str: false,
            },
            TokenKind::EmitStack => {
                let emit_labels = if matches!(token_iter.peek(), Some((_,tk)) if tk.inner.kind == TokenKind::ParenthesisOpen)
                {
                    let Ok((_, count_token, close_paren)) = parse_delimited_token_list(
                        &mut token_iter,
                        token,
                        Some(1),
                        ("(", |t| t == TokenKind::ParenthesisOpen),
                        ("bool", |t| matches!(t, TokenKind::Boolean(_))),
                        (")", |t| t == TokenKind::ParenthesisClosed),
                        interner,
                        source_store,
                    ) else {
                        had_error = true;
                        continue;
                    };

                    token.location = token.location.merge(close_paren.location);

                    let emit_token = count_token[0];
                    let TokenKind::Boolean(emit_labels) = emit_token.inner.kind else { unreachable!() };
                    emit_labels
                } else {
                    false
                };

                OpCode::EmitStack(emit_labels)
            }
            TokenKind::ArgC => OpCode::ArgC,
            TokenKind::ArgV => OpCode::ArgV,

            TokenKind::While => {
                match parse_while(
                    program,
                    &mut token_iter,
                    tokens,
                    token,
                    op_id_gen,
                    parent_id,
                    interner,
                    source_store,
                ) {
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                    Ok(code) => code,
                }
            }

            TokenKind::Assert | TokenKind::Const => {
                if parse_item(
                    program,
                    &mut token_iter,
                    tokens,
                    token,
                    interner,
                    parent_id,
                    source_store,
                )
                .is_err()
                {
                    had_error = true;
                }
                continue;
            }
            TokenKind::Memory => {
                if parse_memory(
                    program,
                    &mut token_iter,
                    token,
                    parent_id,
                    interner,
                    source_store,
                )
                .is_err()
                {
                    had_error = true;
                }
                continue;
            }
            TokenKind::Module
            | TokenKind::Macro
            | TokenKind::Proc
            | TokenKind::Field
            | TokenKind::Struct => {
                diagnostics::emit_error(
                    token.location,
                    format!("cannot use `{:?}` inside a procedure", token.inner.kind),
                    Some(
                        Label::new(token.location)
                            .with_color(Color::Red)
                            .with_message("here"),
                    ),
                    None,
                    source_store,
                );
                had_error = true;
                continue;
            }

            TokenKind::If => {
                match parse_if(
                    program,
                    &mut token_iter,
                    tokens,
                    token,
                    op_id_gen,
                    parent_id,
                    interner,
                    source_store,
                ) {
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                    Ok(code) => code,
                }
            }

            TokenKind::Minus => match token_iter.peek().copied() {
                Some((_, int_token))
                    if int_token.location.neighbour_of(token.location)
                        && matches!(int_token.inner.kind, TokenKind::Integer { .. }) =>
                {
                    token_iter.next();
                    let mut int_token = *int_token;
                    int_token.location = int_token.location.merge(token.location);
                    let Ok((int, location)) = parse_integer_op(&mut token_iter, int_token, true, interner, source_store) else {
                        had_error = true;
                        continue;
                    };

                    token.location = token.location.merge(location);
                    int
                }
                _ => OpCode::Subtract,
            },
            TokenKind::Plus => OpCode::Add,
            TokenKind::Star => OpCode::Multiply,
            TokenKind::Div => OpCode::Div,
            TokenKind::Rem => OpCode::Rem,

            TokenKind::BitAnd => OpCode::BitAnd,
            TokenKind::BitNot => OpCode::BitNot,
            TokenKind::BitOr => OpCode::BitOr,
            TokenKind::BitXor => OpCode::BitXor,
            TokenKind::ShiftLeft => OpCode::ShiftLeft,
            TokenKind::ShiftRight => OpCode::ShiftRight,

            TokenKind::Return => OpCode::Return,
            TokenKind::Exit => OpCode::Exit,

            // These are only used as part of a sub-block. If they're found anywhere else,
            // it's an error.
            TokenKind::ColonColon
            | TokenKind::GoesTo
            | TokenKind::Is
            | TokenKind::Import
            | TokenKind::Do
            | TokenKind::Elif
            | TokenKind::Else
            | TokenKind::End
            | TokenKind::ParenthesisClosed
            | TokenKind::ParenthesisOpen
            | TokenKind::SquareBracketClosed
            | TokenKind::SquareBracketOpen => {
                diagnostics::emit_error(
                    token.location,
                    format!(
                        "unexpected token `{}` in input",
                        interner.resolve_lexeme(token.inner.lexeme)
                    ),
                    Some(Label::new(token.location)),
                    None,
                    source_store,
                );

                had_error = true;
                continue;
            }
        };

        ops.push(Op::new(op_id_gen(), kind, token.map(|t| t.lexeme)));
    }

    had_error.not().then_some(ops).ok_or(())
}

fn parse_ident<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    interner: &Interners,
    source_store: &SourceStorage,
    token: Spanned<Token>,
) -> Result<Vec<Spanned<Spur>>, ()> {
    let mut path = vec![token.map(|t| t.lexeme)];

    while matches!(token_iter.peek(), Some((_, t)) if t.inner.kind == TokenKind::ColonColon) {
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

    Ok(path)
}

fn get_item_body<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    tokens: &'a [Spanned<Token>],
    keyword: Spanned<Token>,
    mut last_token: Spanned<Token>,
    target_token_type: fn(TokenKind) -> bool,
    source_store: &SourceStorage,
) -> Result<(&'a [Spanned<Token>], Spanned<Token>), ()> {
    let body_start_idx = match token_iter.peek() {
        Some((idx, _)) => *idx,
        None => {
            diagnostics::end_of_file(last_token.location, source_store);
            return Err(());
        }
    };

    // We need to keep track of block depth so we know which token is ending the block.
    // We've already consumed the token that opened the block.
    let mut block_depth = 1;
    let mut end_idx = body_start_idx;
    let mut had_error = false;

    for (idx, token) in token_iter {
        use TokenKind::*;
        #[allow(clippy::match_like_matches_macro)]
        let is_nested_err = match (keyword.inner.kind, token.inner.kind) {
            (Proc, Module | Proc | Macro) => true,
            (Memory | Const, Proc | Macro | Const | Memory | Module) => true,
            _ => false,
        };

        if is_nested_err {
            diagnostics::emit_error(
                token.location,
                format!(
                    "cannot use {:?} inside a {:?}",
                    token.inner.kind, keyword.inner.kind
                ),
                Some(Label::new(token.location).with_color(Color::Red)),
                None,
                source_store,
            );
            had_error = true;
        }

        // If the block_depth is greater than 1, it means we're in a sub-block. All sub-blocks
        // will always close with an End token, so if we are in a sub-block only look for End.
        if token.inner.kind.new_block() {
            block_depth += 1;
        } else if (block_depth > 1 && token.inner.kind == TokenKind::End)
            || (block_depth == 1 && target_token_type(token.inner.kind))
        {
            block_depth -= 1;
        }

        end_idx = idx;
        last_token = *token;

        if block_depth == 0 {
            break;
        }
    }

    if !target_token_type(last_token.inner.kind) {
        diagnostics::end_of_file(last_token.location, source_store);
        return Err(());
    }

    had_error
        .not()
        .then(|| (&tokens[body_start_idx..end_idx], last_token))
        .ok_or(())
}

fn parse_if<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    tokens: &'a [Spanned<Token>],
    keyword: Spanned<Token>,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<OpCode, ()> {
    let (condition, do_token) = get_item_body(
        token_iter,
        tokens,
        keyword,
        keyword,
        |t| matches!(t, TokenKind::Do),
        source_store,
    )?;

    let condition = parse_item_body(
        program,
        condition,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let (main_block, mut close_token) = get_item_body(
        token_iter,
        tokens,
        keyword,
        keyword,
        |t| matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif),
        source_store,
    )?;

    let then_block = parse_item_body(
        program,
        main_block,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let else_token = close_token;
    let mut elif_blocks = Vec::new();

    while close_token.inner.kind == TokenKind::Elif {
        let (elif_condition, do_token) = get_item_body(
            token_iter,
            tokens,
            keyword,
            keyword,
            |t| matches!(t, TokenKind::Do),
            source_store,
        )?;

        let elif_condition = parse_item_body(
            program,
            elif_condition,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        let (elif_block, cur_close_token) = get_item_body(
            token_iter,
            tokens,
            keyword,
            keyword,
            |t| matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif),
            source_store,
        )?;

        let elif_block = parse_item_body(
            program,
            elif_block,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        elif_blocks.push((
            close_token,
            elif_condition,
            do_token,
            elif_block,
            cur_close_token,
        ));
        close_token = cur_close_token;
    }

    let mut else_block = if close_token.inner.kind == TokenKind::Else {
        let (else_block, end_token) = get_item_body(
            token_iter,
            tokens,
            keyword,
            keyword,
            |t| matches!(t, TokenKind::End),
            source_store,
        )?;

        let else_block = parse_item_body(
            program,
            else_block,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        close_token = end_token;

        else_block
    } else {
        Vec::new()
    };

    // Normalize into an `if <cond> do <body> else <body> end` structure.
    while let Some((open_token, condition, do_token, then_block, else_token)) = elif_blocks.pop() {
        let if_op = Op::new(
            op_id_gen(),
            OpCode::If(Box::new(If {
                open_token: open_token.location,
                condition,
                is_condition_terminal: false,
                do_token: do_token.location,
                then_block,
                is_then_terminal: false,
                else_token: else_token.location,
                else_block,
                is_else_terminal: false,
                end_token: close_token.location,
            })),
            open_token.map(|t| t.lexeme),
        );

        else_block = vec![if_op];
    }

    Ok(OpCode::If(Box::new(If {
        open_token: keyword.location,
        condition,
        is_condition_terminal: false,
        do_token: do_token.location,
        then_block,
        is_then_terminal: false,
        else_token: else_token.location,
        else_block,
        is_else_terminal: false,
        end_token: close_token.location,
    })))
}

fn parse_while<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    tokens: &'a [Spanned<Token>],
    keyword: Spanned<Token>,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<OpCode, ()> {
    let (condition, do_token) = get_item_body(
        token_iter,
        tokens,
        keyword,
        keyword,
        |t| matches!(t, TokenKind::Do),
        source_store,
    )?;

    let condition = parse_item_body(
        program,
        condition,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let (body, end_token) = get_item_body(
        token_iter,
        tokens,
        keyword,
        do_token,
        |t| matches!(t, TokenKind::End),
        source_store,
    )?;

    let body_block = parse_item_body(program, body, op_id_gen, interner, parent_id, source_store)?;

    Ok(OpCode::While(Box::new(While {
        do_token: do_token.location,
        condition,
        body_block,
        end_token: end_token.location,
    })))
}

fn parse_memory<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    parent_id: ItemId,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(Spanned<Token>, ItemId), ()> {
    let mut had_error = false;
    let name_token = expect_token(
        token_iter,
        "ident",
        |k| k == TokenKind::Ident,
        keyword,
        interner,
        source_store,
    )
    .map(|(_, a)| a)
    .recover(&mut had_error, keyword);

    let (store_type_start, store_type_tokens, store_type_end) = parse_delimited_token_list(
        token_iter,
        name_token,
        None,
        ("is", |t| t == TokenKind::Is),
        ("type name", valid_type_token),
        ("end", |t| t == TokenKind::End),
        interner,
        source_store,
    )
    .recover(&mut had_error, (name_token, Vec::new(), name_token));

    let store_type_location = if store_type_tokens.is_empty() {
        store_type_start.location.merge(store_type_end.location)
    } else {
        let first = store_type_tokens.first().unwrap();
        let last = store_type_tokens.last().unwrap();
        first.location.merge(last.location)
    };

    let mut unresolved_store_type =
        parse_unresolved_types(interner, source_store, store_type_start, store_type_tokens)
            .recover(&mut had_error, Vec::new());

    if unresolved_store_type.len() != 1 {
        diagnostics::emit_error(
            store_type_location,
            format!("expected 1 type, found {}", unresolved_store_type.len()),
            [Label::new(store_type_location).with_color(Color::Red)],
            None,
            source_store,
        );
        had_error = true;
    }

    let sig = ItemSignatureUnresolved {
        exit_stack: Vec::new().with_span(name_token.location),
        entry_stack: Vec::new().with_span(name_token.location),
        memory_type: unresolved_store_type
            .pop()
            .map(|(t, _)| UnresolvedType::Tokens(t).with_span(store_type_location)),
    };

    let item_id = program.new_item(
        source_store,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        ItemKind::Memory,
        parent_id,
        sig,
    );

    if program.get_item_header(parent_id).kind() == ItemKind::Function {
        let pd = program.get_function_data_mut(parent_id);
        pd.allocs.insert(name_token.inner.lexeme, item_id);
    }

    had_error.not().then_some((name_token, item_id)).ok_or(())
}

fn parse_function_header<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    interner: &Interners,
    name: Spanned<Token>,
    parent_id: ItemId,
    source_store: &SourceStorage,
) -> Result<(Spanned<Token>, ItemId), ()> {
    let mut had_error = false;
    let (entry_stack_start, entry_tokens, entry_stack_end) = parse_delimited_token_list(
        token_iter,
        name,
        None,
        ("[", |t| t == TokenKind::SquareBracketOpen),
        ("Ident", valid_type_token),
        ("]", |t| t == TokenKind::SquareBracketClosed),
        interner,
        source_store,
    )
    .recover(&mut had_error, (name, Vec::new(), name));
    let entry_stack_location = entry_stack_start.location.merge(entry_stack_end.location);
    let unresolved_entry_types =
        parse_unresolved_types(interner, source_store, entry_stack_start, entry_tokens)
            .recover(&mut had_error, Vec::new());

    expect_token(
        token_iter,
        "to",
        |k| k == TokenKind::GoesTo,
        name,
        interner,
        source_store,
    )
    .recover(&mut had_error, (0, name));

    let (exit_stack_start, exit_tokens, exit_stack_end) = parse_delimited_token_list(
        token_iter,
        name,
        None,
        ("[", |t| t == TokenKind::SquareBracketOpen),
        ("Ident", valid_type_token),
        ("]", |t| t == TokenKind::SquareBracketClosed),
        interner,
        source_store,
    )
    .recover(&mut had_error, (name, Vec::new(), name));
    let exit_stack_location = exit_stack_start.location.merge(exit_stack_end.location);
    let unresolved_exit_types =
        parse_unresolved_types(interner, source_store, exit_stack_start, exit_tokens)
            .recover(&mut had_error, Vec::new());

    let sig = ItemSignatureUnresolved {
        exit_stack: unresolved_exit_types
            .into_iter()
            .map(|(t, s)| UnresolvedType::Tokens(t).with_span(s))
            .collect::<Vec<_>>()
            .with_span(exit_stack_location),
        entry_stack: unresolved_entry_types
            .into_iter()
            .map(|(t, s)| UnresolvedType::Tokens(t).with_span(s))
            .collect::<Vec<_>>()
            .with_span(entry_stack_location),
        memory_type: None,
    };

    let new_item = program.new_item(
        source_store,
        &mut had_error,
        name.map(|t| t.lexeme),
        ItemKind::Function,
        parent_id,
        sig,
    );

    let (_, is_token) = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        name,
        interner,
        source_store,
    )
    .recover(&mut had_error, (0, name));

    had_error.not().then_some((is_token, new_item)).ok_or(())
}

fn parse_macro_header<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    interner: &Interners,
    name: Spanned<Token>,
    parent_id: ItemId,
    source_store: &SourceStorage,
) -> Result<(Spanned<Token>, ItemId), ()> {
    let sig = ItemSignatureUnresolved {
        exit_stack: Vec::new().with_span(name.location),
        entry_stack: Vec::new().with_span(name.location),
        memory_type: None,
    };

    let mut had_error = false;
    let new_item = program.new_item(
        source_store,
        &mut had_error,
        name.map(|t| t.lexeme),
        ItemKind::Macro,
        parent_id,
        sig,
    );

    let (_, is_token) = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        name,
        interner,
        source_store,
    )
    .recover(&mut had_error, (0, name));

    had_error.not().then_some((is_token, new_item)).ok_or(())
}

fn parse_const_header<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    interner: &Interners,
    name: Spanned<Token>,
    parent_id: ItemId,
    source_store: &SourceStorage,
) -> Result<(Spanned<Token>, ItemId), ()> {
    let mut had_error = false;
    let (exit_stack_start, exit_tokens, exit_stack_end) = parse_delimited_token_list(
        token_iter,
        name,
        None,
        ("[", |t| t == TokenKind::SquareBracketOpen),
        ("Ident", valid_type_token),
        ("]", |t| t == TokenKind::SquareBracketClosed),
        interner,
        source_store,
    )
    .recover(&mut had_error, (name, Vec::new(), name));
    let exit_stack_location = exit_stack_start.location.merge(exit_stack_end.location);
    let unresolved_exit_types =
        parse_unresolved_types(interner, source_store, exit_stack_start, exit_tokens)
            .recover(&mut had_error, Vec::new());

    let sig = ItemSignatureUnresolved {
        exit_stack: unresolved_exit_types
            .into_iter()
            .map(|(t, s)| UnresolvedType::Tokens(t).with_span(s))
            .collect::<Vec<_>>()
            .with_span(exit_stack_location),
        entry_stack: Vec::new().with_span(name.location),
        memory_type: None,
    };

    let new_item = program.new_item(
        source_store,
        &mut had_error,
        name.map(|t| t.lexeme),
        ItemKind::Const,
        parent_id,
        sig,
    );

    let (_, is_token) = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        name,
        interner,
        source_store,
    )
    .recover(&mut had_error, (0, name));

    had_error.not().then_some((is_token, new_item)).ok_or(())
}

fn parse_assert_header<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    interner: &Interners,
    name: Spanned<Token>,
    parent_id: ItemId,
    source_store: &SourceStorage,
) -> Result<(Spanned<Token>, ItemId), ()> {
    let sig = ItemSignatureUnresolved {
        exit_stack: vec![UnresolvedType::Tokens(UnresolvedTypeTokens::Simple(vec![
            name.map(|t| t.lexeme)
        ]))
        .with_span(name.location)]
        .with_span(name.location),
        entry_stack: Vec::new().with_span(name.location),
        memory_type: None,
    };

    let mut had_error = false;
    let new_item = program.new_item(
        source_store,
        &mut had_error,
        name.map(|t| t.lexeme),
        ItemKind::Assert,
        parent_id,
        sig,
    );

    let (_, is_token) = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        name,
        interner,
        source_store,
    )
    .recover(&mut had_error, (0, name));

    had_error.not().then_some((is_token, new_item)).ok_or(())
}

fn parse_item<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    tokens: &'a [Spanned<Token>],
    keyword: Spanned<Token>,
    interner: &Interners,
    parent_id: ItemId,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut had_error = false;
    let name_token = expect_token(
        token_iter,
        "ident",
        |k| k == TokenKind::Ident,
        keyword,
        interner,
        source_store,
    )
    .map(|(_, a)| a)
    .recover(&mut had_error, keyword);

    let header_func = match keyword.inner.kind {
        TokenKind::Proc => parse_function_header,
        TokenKind::Macro => parse_macro_header,
        TokenKind::Const => parse_const_header,
        TokenKind::Assert => parse_assert_header,
        _ => unreachable!(),
    };

    let (is_token, item_id) = header_func(
        program,
        token_iter,
        interner,
        name_token,
        parent_id,
        source_store,
    )
    .recover(&mut had_error, (name_token, ItemId::dud()));

    let mut op_id = 0;
    let mut op_id_gen = || {
        let id = op_id;
        op_id += 1;
        OpId(id)
    };

    let (body, end_token) = get_item_body(
        &mut *token_iter,
        tokens,
        keyword,
        is_token,
        |t| matches!(t, TokenKind::End),
        source_store,
    )
    .recover(&mut had_error, (&[], is_token));

    let mut body = parse_item_body(
        program,
        body,
        &mut op_id_gen,
        interner,
        item_id,
        source_store,
    )
    .recover(&mut had_error, Vec::new());

    if item_id == ItemId::dud() {
        // We can't continue from here.
        return Err(());
    }

    let item_header = program.get_item_header_mut(item_id);

    if item_header.kind() != ItemKind::Macro {
        // Makes later logic a bit easier if we always have a prologue and epilogue.
        body.insert(
            0,
            Op {
                code: OpCode::Prologue,
                id: op_id_gen(),
                token: name_token.map(|t| t.lexeme),
                expansions: SmallVec::new(),
            },
        );

        body.push(Op {
            code: OpCode::Epilogue,
            id: op_id_gen(),
            token: end_token.map(|t| t.lexeme),
            expansions: SmallVec::new(),
        });
    }

    item_header.new_op_id = op_id;
    program.set_item_body(item_id, body);

    // stupid borrow checker...
    let _ = item_header; // Need to discard the borrow;
    let item_header = program.get_item_header(item_id);

    if let Some(prev_def) = program
        .get_visible_symbol(item_header, name_token.inner.lexeme)
        .filter(|&f| f != item_id)
    {
        let prev_item = program.get_item_header(prev_def).name();

        diagnostics::emit_error(
            name_token.location,
            "multiple definitions of symbol",
            [
                Label::new(name_token.location)
                    .with_message("defined here")
                    .with_color(Color::Red),
                Label::new(prev_item.location)
                    .with_message("also defined here")
                    .with_color(Color::Blue),
            ],
            None,
            source_store,
        );
        had_error = true;
    }

    let parent_item = program.get_item_header(parent_id);
    match (parent_item.kind(), keyword.inner.kind) {
        (ItemKind::Function, TokenKind::Const) => {
            let pd = program.get_function_data_mut(parent_id);
            pd.consts.insert(name_token.inner.lexeme, item_id);
        }
        (ItemKind::Function, TokenKind::Memory) => {
            let pd = program.get_function_data_mut(parent_id);
            pd.allocs.insert(name_token.inner.lexeme, item_id);
        }
        // The other types aren't stored in the proc
        _ => {}
    }

    if had_error {
        Err(())
    } else {
        Ok(())
    }
}

fn parse_struct<'a>(
    program: &mut Program,
    module_id: ItemId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut had_error = false;
    let name_token = expect_token(
        token_iter,
        "ident",
        |k| k == TokenKind::Ident,
        keyword,
        interner,
        source_store,
    )
    .map(|(_, a)| a)
    .recover(&mut had_error, keyword);

    let generic_params = if matches!(token_iter.peek(), Some((_, t)) if t.inner.kind == TokenKind::ParenthesisOpen)
    {
        let (_, mut generic_idents, _) = parse_delimited_token_list(
            token_iter,
            name_token,
            Some(1),
            ("`(`", |t| t == TokenKind::ParenthesisOpen),
            ("`ident`", |t| t == TokenKind::Ident),
            ("`)`", |t| t == TokenKind::ParenthesisClosed),
            interner,
            source_store,
        )
        .recover(&mut had_error, (name_token, Vec::new(), name_token));
        Some(generic_idents.pop().unwrap().map(|t| t.lexeme))
    } else {
        None
    };

    let is_token = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        keyword,
        interner,
        source_store,
    )
    .map(|(_, a)| a)
    .recover(&mut had_error, name_token);

    let mut fields = Vec::new();
    let mut prev_token = expect_token(
        token_iter,
        "field",
        |k| k == TokenKind::Field,
        keyword,
        interner,
        source_store,
    )
    .map(|(_, a)| a)
    .recover(&mut had_error, is_token);

    loop {
        let (field_name_token, type_tokens, end_token) = parse_delimited_token_list(
            token_iter,
            prev_token,
            None,
            ("ident", |t| t == TokenKind::Ident),
            ("type name", valid_type_token),
            ("end or field", |t| {
                t == TokenKind::End || t == TokenKind::Field
            }),
            interner,
            source_store,
        )
        .recover(&mut had_error, (name_token, Vec::new(), name_token));

        let last_type_token = type_tokens.last().copied().unwrap_or(end_token);
        let store_type_location = field_name_token.location.merge(last_type_token.location);
        let mut unresolved_store_type =
            parse_unresolved_types(interner, source_store, field_name_token, type_tokens)
                .recover(&mut had_error, Vec::new());

        if unresolved_store_type.len() != 1 {
            diagnostics::emit_error(
                store_type_location,
                format!("expected 1 type, found {}", unresolved_store_type.len()),
                [Label::new(store_type_location).with_color(Color::Red)],
                None,
                source_store,
            );
            had_error = true;
        }

        fields.push(UnresolvedField {
            name: field_name_token.map(|t| t.lexeme),
            kind: UnresolvedType::Tokens(unresolved_store_type.pop().unwrap().0),
        });
        prev_token = end_token;

        if end_token.inner.kind == TokenKind::End {
            break;
        }
    }

    let struct_def = UnresolvedStruct {
        name: name_token.map(|t| t.lexeme),
        fields,
        generic_params,
    };

    program.new_struct(source_store, &mut had_error, module_id, struct_def);

    if !had_error {
        Ok(())
    } else {
        Err(())
    }
}

pub(super) fn parse_module(
    program: &mut Program,
    module_id: ItemId,
    tokens: &[Spanned<Token>],
    interner: &Interners,
    include_queue: &mut VecDeque<(ModuleQueueType, Option<ItemId>)>,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let _span = debug_span!(stringify!(parser::parse_module)).entered();

    let mut had_error = false;
    let mut token_iter = tokens.iter().enumerate().peekable();

    while let Some((_, token)) = token_iter.next() {
        match token.inner.kind {
            TokenKind::Assert | TokenKind::Const | TokenKind::Macro | TokenKind::Proc => {
                if parse_item(
                    program,
                    &mut token_iter,
                    tokens,
                    *token,
                    interner,
                    module_id,
                    source_store,
                )
                .is_err()
                {
                    had_error = true;
                }
            }

            TokenKind::Memory => {
                if parse_memory(
                    program,
                    &mut token_iter,
                    *token,
                    module_id,
                    interner,
                    source_store,
                )
                .is_err()
                {
                    had_error = true;
                }
            }

            TokenKind::Import => {
                let (_, root_name) = match expect_token(
                    &mut token_iter,
                    "ident",
                    |k| k == TokenKind::Ident,
                    *token,
                    interner,
                    source_store,
                ) {
                    Ok(ident) => ident,
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                };

                let path = parse_ident(&mut token_iter, interner, source_store, root_name)
                    .recover(&mut had_error, Vec::new());

                program
                    .get_module_mut(module_id)
                    .add_unresolved_import(path);
            }

            TokenKind::Module => {
                let (_, module_ident) = match expect_token(
                    &mut token_iter,
                    "ident",
                    |k| k == TokenKind::Ident,
                    *token,
                    interner,
                    source_store,
                ) {
                    Ok(ident) => ident,
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                };

                include_queue.push_back((
                    ModuleQueueType::Include(module_ident.map(|t| t.lexeme)),
                    Some(module_id),
                ));
            }

            TokenKind::Struct => {
                if parse_struct(
                    program,
                    module_id,
                    &mut token_iter,
                    *token,
                    interner,
                    source_store,
                )
                .is_err()
                {
                    had_error = true;
                }
            }

            _ => {
                diagnostics::emit_error(
                    token.location,
                    format!("top-level can only declared `const`, `include`, `macro` `memory` or `proc`, found `{:?}`", token.inner.kind),
                    Some(Label::new(token.location).with_color(Color::Red).with_message("here")),
                    None,
                    source_store
                );

                had_error = true;
                continue;
            }
        }
    }

    had_error.not().then_some(()).ok_or(())
}
