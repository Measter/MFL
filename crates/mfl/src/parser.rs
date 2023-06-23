use std::{collections::VecDeque, iter::Peekable, ops::Not};

use ariadne::{Color, Label};
use intcast::IntCast;
use tracing::debug_span;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{Token, TokenKind},
    opcode::{Direction, If, IntKind, Op, OpCode, OpId, While},
    program::ModuleQueueType,
    source_file::{SourceLocation, SourceStorage, Spanned, WithSpan},
    type_store::{IntWidth, Signedness, UnresolvedType},
    ItemId, Program,
};

use self::utils::{
    expect_token, parse_delimited_token_list, parse_ident, parse_integer_lexeme,
    parse_unresolved_types, valid_type_token, Delimited, Recover,
};

mod items;
mod utils;

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

    let (width, value) = if token_iter
        .peek()
        .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
    {
        let delim = parse_delimited_token_list(
            token_iter,
            token,
            Some(1),
            ("(", |t| t == TokenKind::ParenthesisOpen),
            ("Ident", |t| t == TokenKind::Ident),
            (")", |t| t == TokenKind::ParenthesisClosed),
            interner,
            source_store,
        )?;
        let ident_token = delim.list[0];
        overall_location = overall_location.merge(delim.close.location);

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
                // FIXME: Need to check bounds before cast
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

pub fn parse_item_body_contents(
    program: &mut Program,
    tokens: &[Spanned<Token>],
    op_id_gen: &mut impl FnMut() -> OpId,
    interner: &mut Interners,
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
                let count = if token_iter
                    .peek()
                    .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
                {
                    let Ok(delim) = parse_delimited_token_list(
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

                    token.location = token.location.merge(delim.close.location);

                    let count_token = delim.list[0];
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
                let Ok(delim) = parse_delimited_token_list(
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

                token.location = token.location.merge(delim.close.location);

                if delim.list.len() == 1
                    && matches!(delim.list[0].inner.kind, TokenKind::Integer { .. })
                {
                    let count_token = delim.list[0];
                    let count = parse_integer_lexeme(count_token, interner, source_store)?;

                    OpCode::PackArray { count }
                } else {
                    let span = delim.span();

                    let Ok(mut unresolved_types) = parse_unresolved_types(interner, source_store, delim.open, &delim.list) else {
                        had_error = true;
                        continue;
                    };

                    if unresolved_types.len() != 1 {
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

                    let unresolved_type = unresolved_types.pop().unwrap();
                    OpCode::UnresolvedPackStruct {
                        unresolved_type: UnresolvedType::Tokens(unresolved_type.inner),
                    }
                }
            }
            TokenKind::Unpack => OpCode::Unpack,
            TokenKind::Extract { .. } | TokenKind::Insert { .. } => {
                if token_iter
                    .peek()
                    .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
                {
                    let Ok(delim) = parse_delimited_token_list(
                        &mut token_iter,
                        token,
                        None,
                        ("(", |t| t == TokenKind::ParenthesisOpen),
                        ("ident", |t| t == TokenKind::Ident || t == TokenKind::Dot),
                        (")", |t| t == TokenKind::ParenthesisClosed),
                        interner,
                        source_store,
                    ) else {
                        had_error = true;
                        continue;
                    };

                    token.location = token.location.merge(delim.close.location);
                    let mut delim_iter = delim.list.iter().enumerate().peekable();
                    let mut idents = Vec::new();

                    // We want to make sure the Dots exist, but we don't actually want them.
                    let mut local_had_error = false;
                    let mut prev_token = delim.open;
                    loop {
                        let Ok(next) = expect_token(
                            &mut delim_iter,
                            "ident",
                            |t| t == TokenKind::Ident,
                            prev_token,
                            interner,
                            source_store,
                        ) else {
                            local_had_error = true;
                            break;
                        };
                        idents.push(next.1);

                        if delim_iter
                            .peek()
                            .is_some_and(|(_, t)| t.inner.kind == TokenKind::Dot)
                        {
                            prev_token = *delim_iter.next().unwrap().1;
                            continue;
                        }
                        break;
                    }

                    if local_had_error {
                        had_error = true;
                        continue;
                    }

                    match token.inner.kind {
                        TokenKind::Extract { emit_struct } => {
                            // As we're generating multiple ops, we need a bit of manual handling.
                            let mut emit_struct = emit_struct;
                            for field_name in idents {
                                let first = OpCode::ExtractStruct {
                                    emit_struct,
                                    field_name: field_name.map(|t| t.lexeme),
                                };

                                ops.push(Op::new(op_id_gen(), first, token.map(|t| t.lexeme)));
                                emit_struct = false;
                            }

                            continue;
                        }
                        TokenKind::Insert { emit_struct } if idents.len() > 1 => {
                            // Hang on to your seat, this'll be a good one!
                            let [prev @ .., _] = idents.as_slice() else { unreachable!() };

                            for &ident in prev {
                                let xtr = OpCode::ExtractStruct {
                                    emit_struct: true,
                                    field_name: ident.map(|t| t.lexeme),
                                };
                                ops.push(Op::new(op_id_gen(), xtr, token.map(|t| t.lexeme)));
                            }

                            let rot_len = (idents.len() + 1).to_u8().unwrap();
                            let rot = OpCode::Rot {
                                item_count: rot_len.with_span(token.location),
                                direction: Direction::Left,
                                shift_count: 1.with_span(token.location),
                            };
                            ops.push(Op::new(op_id_gen(), rot, token.map(|t| t.lexeme)));

                            let [first, prev @ ..] = idents.as_slice() else { unreachable!() };
                            for ident in prev.iter().rev() {
                                let swap = OpCode::Swap {
                                    count: 1.with_span(token.location),
                                };
                                ops.push(Op::new(op_id_gen(), swap, token.map(|t| t.lexeme)));
                                let ins = OpCode::InsertStruct {
                                    emit_struct: true,
                                    field_name: ident.map(|t| t.lexeme),
                                };
                                ops.push(Op::new(op_id_gen(), ins, token.map(|t| t.lexeme)));
                            }

                            let swap = OpCode::Swap {
                                count: 1.with_span(token.location),
                            };
                            ops.push(Op::new(op_id_gen(), swap, token.map(|t| t.lexeme)));
                            let kind = OpCode::InsertStruct {
                                emit_struct,
                                field_name: first.map(|t| t.lexeme),
                            };
                            ops.push(Op::new(op_id_gen(), kind, token.map(|t| t.lexeme)));
                            continue;
                            // todo!()
                        }
                        TokenKind::Insert { emit_struct } => OpCode::InsertStruct {
                            emit_struct,
                            field_name: idents[0].map(|t| t.lexeme),
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
                let Ok(delim) = parse_delimited_token_list(&mut token_iter,
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
                token.location = token.location.merge(delim.close.location);

                let mut local_error = false;
                let [item_count_token, direction_token, shift_count_token] = &*delim.list else { unreachable!() };
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
                let Ok(delim) = parse_delimited_token_list(
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
                token.location = token.location.merge(delim.close.location);

                let span = delim.span();
                let Ok(mut unresolved_types) = parse_unresolved_types(interner, source_store, delim.open, &delim.list) else {
                    had_error = true;
                    continue;
                };

                if unresolved_types.len() != 1 {
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

                let unresolved_type = unresolved_types.pop().unwrap().inner;

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
            TokenKind::Ident | TokenKind::ColonColon => {
                let Ok((ident,_)) = parse_ident(&mut token_iter, interner, source_store, &mut had_error, token) else {
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
                let emit_labels = if token_iter
                    .peek()
                    .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
                {
                    let Ok(delim) = parse_delimited_token_list(
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

                    token.location = token.location.merge(delim.close.location);

                    let emit_token = delim.list[0];
                    let TokenKind::Boolean(emit_labels) = emit_token.inner.kind else { unreachable!() };
                    emit_labels
                } else {
                    false
                };

                OpCode::EmitStack(emit_labels)
            }

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

            TokenKind::Assert => {
                had_error |= items::parse_assert(
                    program,
                    &mut token_iter,
                    token,
                    parent_id,
                    interner,
                    source_store,
                )
                .is_err();

                continue;
            }
            TokenKind::Const => {
                if items::parse_const(
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
            TokenKind::Memory => {
                if items::parse_memory(
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
            TokenKind::Module | TokenKind::Proc | TokenKind::Field | TokenKind::Struct => {
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
            TokenKind::GoesTo
            | TokenKind::Is
            | TokenKind::Import
            | TokenKind::Do
            | TokenKind::Dot
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
            (Proc, Module | Proc) => true,
            (Memory | Const, Proc | Const | Memory | Module) => true,
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
    interner: &mut Interners,
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

    let condition = parse_item_body_contents(
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

    let then_block = parse_item_body_contents(
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

        let elif_condition = parse_item_body_contents(
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

        let elif_block = parse_item_body_contents(
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

        let else_block = parse_item_body_contents(
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
    interner: &mut Interners,
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

    let condition = parse_item_body_contents(
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

    let body_block =
        parse_item_body_contents(program, body, op_id_gen, interner, parent_id, source_store)?;

    Ok(OpCode::While(Box::new(While {
        do_token: do_token.location,
        condition,
        body_block,
        end_token: end_token.location,
    })))
}

pub(super) fn parse_file(
    program: &mut Program,
    module_id: ItemId,
    tokens: &[Spanned<Token>],
    interner: &mut Interners,
    include_queue: &mut VecDeque<(ModuleQueueType, Option<ItemId>)>,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let _span = debug_span!(stringify!(parser::parse_module)).entered();

    let mut had_error = false;
    let mut token_iter = tokens.iter().enumerate().peekable();

    while let Some((_, token)) = token_iter.next() {
        match token.inner.kind {
            TokenKind::Assert => {
                had_error |= items::parse_assert(
                    program,
                    &mut token_iter,
                    *token,
                    module_id,
                    interner,
                    source_store,
                )
                .is_err();
            }

            TokenKind::Const => {
                had_error |= items::parse_const(
                    program,
                    &mut token_iter,
                    *token,
                    module_id,
                    interner,
                    source_store,
                )
                .is_err();
            }

            TokenKind::Proc => {
                had_error |= items::parse_function(
                    program,
                    &mut token_iter,
                    *token,
                    module_id,
                    interner,
                    source_store,
                )
                .is_err();
            }

            TokenKind::Memory => {
                had_error |= items::parse_memory(
                    program,
                    &mut token_iter,
                    *token,
                    module_id,
                    interner,
                    source_store,
                )
                .is_err();
            }

            TokenKind::Import => {
                had_error |= items::parse_import(
                    program,
                    interner,
                    source_store,
                    &mut had_error,
                    &mut token_iter,
                    *token,
                    module_id,
                )
                .is_err();
            }

            TokenKind::Module => {
                had_error |= items::parse_module(
                    interner,
                    source_store,
                    include_queue,
                    &mut token_iter,
                    *token,
                    module_id,
                )
                .is_err();
            }

            TokenKind::Struct => {
                had_error |= items::parse_struct(
                    program,
                    module_id,
                    &mut token_iter,
                    *token,
                    interner,
                    source_store,
                )
                .is_err();
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
