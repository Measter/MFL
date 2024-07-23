use std::iter::Peekable;

use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;

use crate::{
    context::{Context, ItemId},
    diagnostics,
    error_signal::ErrorSignal,
    ir::{
        Arithmetic, Basic, Compare, Control, Direction, If, IfTokens, IntKind, Memory, Op, OpCode,
        OpId, Stack, TerminalBlock, UnresolvedOp, While, WhileTokens,
    },
    lexer::{Extract, Insert, StringToken, Token, TokenKind},
    source_file::{Spanned, WithSpan},
    stores::type_store::{IntWidth, Signedness},
    Stores,
};

use super::{
    parse_item_body_contents,
    utils::{
        expect_token, get_delimited_tokens, get_terminated_tokens, parse_ident,
        parse_integer_lexeme, parse_integer_param, parse_unresolved_types, valid_type_token,
        ParseOpResult,
    },
};

pub fn parse_extract_insert_array(token: Spanned<Token>) -> ParseOpResult {
    let (kind, loc) = match token.inner.kind {
        TokenKind::Extract(Extract { emit_struct }) => (
            Memory::ExtractArray {
                emit_array: emit_struct,
            },
            token.location,
        ),
        TokenKind::Insert(Insert { emit_struct }) => (
            Memory::InsertArray {
                emit_array: emit_struct,
            },
            token.location,
        ),
        _ => unreachable!(),
    };

    Ok((OpCode::Basic(Basic::Memory(kind)), loc))
}

pub fn parse_extract_insert_struct<'a>(
    stores: &mut Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    op_id_gen: &mut impl FnMut() -> OpId,
    mut token: Spanned<Token>,
) -> Result<SmallVec<[Op<UnresolvedOp>; 1]>, ()> {
    let mut ops = SmallVec::new();

    let delim = get_delimited_tokens(
        stores,
        token_iter,
        token,
        None,
        ("(", |t| t == TokenKind::ParenthesisOpen),
        ("ident", |t| t == TokenKind::Ident || t == TokenKind::Dot),
        (")", |t| t == TokenKind::ParenthesisClosed),
    )?;

    token.location = token.location.merge(delim.close.location);
    let mut delim_iter = delim.list.iter().enumerate().peekable();
    let mut idents = Vec::new();

    // We want to make sure the Dots exist, but we don't actually want them.
    let mut local_had_error = ErrorSignal::new();
    let mut prev_token = delim.open;
    loop {
        let Ok(next) = expect_token(
            stores,
            &mut delim_iter,
            "ident",
            |t| t == TokenKind::Ident,
            prev_token,
        ) else {
            local_had_error.set();
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

    if local_had_error.into_bool() {
        return Err(());
    }

    match token.inner.kind {
        TokenKind::Extract(Extract { emit_struct }) => {
            // As we're generating multiple ops, we need a bit of manual handling.
            let mut emit_struct = emit_struct;
            for field_name in idents {
                let first = OpCode::Basic(Basic::Memory(Memory::ExtractStruct {
                    emit_struct,
                    field_name: field_name.map(|t| t.lexeme),
                }));

                ops.push(Op::new(op_id_gen(), first, token.map(|t| t.lexeme)));
                emit_struct = false;
            }
        }
        TokenKind::Insert(Insert { emit_struct }) if idents.len() > 1 => {
            // Hang on to your seat, this'll be a good one!
            let [prev @ .., _] = idents.as_slice() else {
                unreachable!()
            };

            for &ident in prev {
                let xtr = OpCode::Basic(Basic::Memory(Memory::ExtractStruct {
                    emit_struct: true,
                    field_name: ident.map(|t| t.lexeme),
                }));
                ops.push(Op::new(op_id_gen(), xtr, token.map(|t| t.lexeme)));
            }

            let rot_len = (idents.len() + 1).to_u8().unwrap();
            let rot = OpCode::Basic(Basic::Stack(Stack::Rotate {
                item_count: rot_len.with_span(token.location),
                direction: Direction::Left,
                shift_count: 1.with_span(token.location),
            }));
            ops.push(Op::new(op_id_gen(), rot, token.map(|t| t.lexeme)));

            let [first, prev @ ..] = idents.as_slice() else {
                unreachable!()
            };
            for ident in prev.iter().rev() {
                let swap = OpCode::Basic(Basic::Stack(Stack::Swap {
                    count: 1.with_span(token.location),
                }));
                ops.push(Op::new(op_id_gen(), swap, token.map(|t| t.lexeme)));
                let ins = OpCode::Basic(Basic::Memory(Memory::InsertStruct {
                    emit_struct: true,
                    field_name: ident.map(|t| t.lexeme),
                }));
                ops.push(Op::new(op_id_gen(), ins, token.map(|t| t.lexeme)));
            }

            let swap = OpCode::Basic(Basic::Stack(Stack::Swap {
                count: 1.with_span(token.location),
            }));
            ops.push(Op::new(op_id_gen(), swap, token.map(|t| t.lexeme)));
            let kind = OpCode::Basic(Basic::Memory(Memory::InsertStruct {
                emit_struct,
                field_name: first.map(|t| t.lexeme),
            }));
            ops.push(Op::new(op_id_gen(), kind, token.map(|t| t.lexeme)));
        }
        TokenKind::Insert(Insert { emit_struct }) => {
            let code = OpCode::Basic(Basic::Memory(Memory::InsertStruct {
                emit_struct,
                field_name: idents[0].map(|t| t.lexeme),
            }));
            ops.push(Op::new(op_id_gen(), code, token.map(|t| t.lexeme)));
        }
        _ => unreachable!(),
    }

    Ok(ops)
}

pub fn parse_simple_op<'a>(
    stores: &mut Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
) -> ParseOpResult {
    let code = match token.inner.kind {
        TokenKind::Drop
        | TokenKind::Dup
        | TokenKind::Over
        | TokenKind::Reverse
        | TokenKind::Swap
        | TokenKind::SysCall => {
            return parse_drop_dup_over_reverse_swap_syscall(stores, token_iter, token);
        }

        TokenKind::Pack => return parse_pack(stores, token_iter, token),
        TokenKind::Unpack => OpCode::Basic(Basic::Memory(Memory::Unpack)),
        TokenKind::Rot => return parse_rot(stores, token_iter, token),

        TokenKind::Cast | TokenKind::SizeOf => return parse_cast_sizeof(stores, token_iter, token),

        TokenKind::Load => OpCode::Basic(Basic::Memory(Memory::Load)),
        TokenKind::Store => OpCode::Basic(Basic::Memory(Memory::Store)),

        TokenKind::IsNull => OpCode::Basic(Basic::Compare(Compare::IsNull)),
        TokenKind::Equal => OpCode::Basic(Basic::Compare(Compare::Equal)),
        TokenKind::Greater => OpCode::Basic(Basic::Compare(Compare::Greater)),
        TokenKind::GreaterEqual => OpCode::Basic(Basic::Compare(Compare::GreaterEqual)),
        TokenKind::Less => OpCode::Basic(Basic::Compare(Compare::Less)),
        TokenKind::LessEqual => OpCode::Basic(Basic::Compare(Compare::LessEqual)),
        TokenKind::NotEqual => OpCode::Basic(Basic::Compare(Compare::NotEq)),

        TokenKind::Boolean(b) => OpCode::Basic(Basic::PushBool(b)),
        TokenKind::Char(ch) => OpCode::Basic(Basic::PushInt {
            width: IntWidth::I8,
            value: IntKind::Unsigned((ch as u8).to_u64()),
        }),

        TokenKind::Ident | TokenKind::ColonColon => {
            return parse_ident_op(stores, token_iter, token)
        }
        TokenKind::Integer { .. } => return parse_integer_op(stores, token_iter, token, false),
        TokenKind::String(StringToken { id, is_c_str }) => {
            OpCode::Basic(Basic::PushStr { id, is_c_str })
        }
        TokenKind::Here(id) => OpCode::Basic(Basic::PushStr {
            id,
            is_c_str: false,
        }),
        TokenKind::EmitStack => return parse_emit_stack(stores, token_iter, token),

        TokenKind::Minus => return parse_minus(stores, token_iter, token),
        TokenKind::Plus => OpCode::Basic(Basic::Arithmetic(Arithmetic::Add)),
        TokenKind::Star => OpCode::Basic(Basic::Arithmetic(Arithmetic::Multiply)),
        TokenKind::Div => OpCode::Basic(Basic::Arithmetic(Arithmetic::Div)),
        TokenKind::Rem => OpCode::Basic(Basic::Arithmetic(Arithmetic::Rem)),

        TokenKind::BitAnd => OpCode::Basic(Basic::Arithmetic(Arithmetic::BitAnd)),
        TokenKind::BitNot => OpCode::Basic(Basic::Arithmetic(Arithmetic::BitNot)),
        TokenKind::BitOr => OpCode::Basic(Basic::Arithmetic(Arithmetic::BitOr)),
        TokenKind::BitXor => OpCode::Basic(Basic::Arithmetic(Arithmetic::BitXor)),
        TokenKind::ShiftLeft => OpCode::Basic(Basic::Arithmetic(Arithmetic::ShiftLeft)),
        TokenKind::ShiftRight => OpCode::Basic(Basic::Arithmetic(Arithmetic::ShiftRight)),

        TokenKind::Return => OpCode::Basic(Basic::Control(Control::Return)),
        TokenKind::Exit => OpCode::Basic(Basic::Control(Control::Exit)),

        _ => {
            panic!(
                "ICE: parse_item was given an op it can't handle: {:?}",
                token.inner.kind
            );
        }
    };

    Ok((code, token.location))
}

fn parse_ident_op<'a>(
    stores: &mut Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
) -> ParseOpResult {
    let mut local_had_error = ErrorSignal::new();

    let (ident, last_token) = parse_ident(stores, &mut local_had_error, token_iter, token)?;

    if local_had_error.into_bool() {
        return Err(());
    }

    Ok((
        OpCode::Complex(UnresolvedOp::Ident(ident)),
        token.location.merge(last_token.location),
    ))
}

fn parse_minus<'a>(
    stores: &Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
) -> ParseOpResult {
    Ok(match token_iter.peek().copied() {
        Some((_, int_token))
            if int_token.location.neighbour_of(token.location)
                && matches!(int_token.inner.kind, TokenKind::Integer { .. }) =>
        {
            token_iter.next();
            let mut int_token = *int_token;
            int_token.location = int_token.location.merge(token.location);
            parse_integer_op(stores, token_iter, int_token, true)?
        }
        _ => (
            OpCode::Basic(Basic::Arithmetic(Arithmetic::Subtract)),
            token.location,
        ),
    })
}

fn parse_emit_stack<'a>(
    stores: &Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
) -> ParseOpResult {
    let (emit_labels, loc) = if token_iter
        .peek()
        .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
    {
        let delim = get_delimited_tokens(
            stores,
            token_iter,
            token,
            Some(1),
            ("(", |t| t == TokenKind::ParenthesisOpen),
            ("bool", |t| matches!(t, TokenKind::Boolean(_))),
            (")", |t| t == TokenKind::ParenthesisClosed),
        )?;

        let emit_token = delim.list[0];
        let TokenKind::Boolean(emit_labels) = emit_token.inner.kind else {
            unreachable!()
        };

        (emit_labels, delim.close.location)
    } else {
        (false, token.location)
    };

    Ok((
        OpCode::Basic(Basic::Stack(Stack::Emit {
            show_labels: emit_labels,
        })),
        loc,
    ))
}

fn parse_cast_sizeof<'a>(
    stores: &mut Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
) -> ParseOpResult {
    let delim = get_delimited_tokens(
        stores,
        token_iter,
        token,
        None,
        ("(", |t| t == TokenKind::ParenthesisOpen),
        ("Ident", valid_type_token),
        (")", |t| t == TokenKind::ParenthesisClosed),
    )?;

    let span = delim.span();
    let mut unresolved_types = parse_unresolved_types(stores, delim.open, &delim.list)?;

    if unresolved_types.len() != 1 {
        diagnostics::emit_error(
            stores,
            span,
            format!("expected 1 type, found {}", unresolved_types.len()),
            [Label::new(span).with_color(Color::Red)],
            None,
        );
        return Err(());
    }

    let unresolved_type = unresolved_types.pop().unwrap().inner;

    let code = match token.inner.kind {
        TokenKind::Cast => UnresolvedOp::Cast {
            id: unresolved_type,
        },
        TokenKind::SizeOf => UnresolvedOp::SizeOf {
            id: unresolved_type,
        },
        _ => unreachable!(),
    };

    Ok((OpCode::Complex(code), delim.close.location))
}

fn parse_rot<'a>(
    stores: &Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
) -> ParseOpResult {
    let delim = get_delimited_tokens(
        stores,
        token_iter,
        token,
        Some(3),
        ("(", |t| t == TokenKind::ParenthesisOpen),
        ("", |_| true),
        (")", |t| t == TokenKind::ParenthesisClosed),
    )?;

    let mut local_error = false;
    let [item_count_token, direction_token, shift_count_token] = &*delim.list else {
        unreachable!()
    };
    let item_count_token = *item_count_token;
    let shift_count_token = *shift_count_token;
    let item_count = if !matches!(item_count_token.inner.kind, TokenKind::Integer { .. }) {
        diagnostics::emit_error(
            stores,
            item_count_token.location,
            format!(
                "expected `integer`, found `{}`",
                stores.strings.resolve(item_count_token.inner.lexeme)
            ),
            Some(Label::new(item_count_token.location).with_color(Color::Red)),
            None,
        );
        local_error = true;
        1
    } else {
        parse_integer_lexeme(stores, item_count_token)?
    };

    let shift_count = if !matches!(shift_count_token.inner.kind, TokenKind::Integer { .. }) {
        diagnostics::emit_error(
            stores,
            shift_count_token.location,
            format!(
                "expected `integer`, found `{}`",
                stores.strings.resolve(shift_count_token.inner.lexeme)
            ),
            Some(Label::new(shift_count_token.location).with_color(Color::Red)),
            None,
        );
        local_error = true;
        1
    } else {
        parse_integer_lexeme(stores, shift_count_token)?
    };

    let direction = match direction_token.inner.kind {
        TokenKind::Less => Direction::Left,
        TokenKind::Greater => Direction::Right,
        _ => {
            diagnostics::emit_error(
                stores,
                direction_token.location,
                format!(
                    "expected `<` or `>`, found `{}`",
                    stores.strings.resolve(direction_token.inner.lexeme)
                ),
                Some(Label::new(direction_token.location).with_color(Color::Red)),
                None,
            );
            local_error = true;
            Direction::Left
        }
    };

    if local_error {
        return Err(());
    }

    Ok((
        OpCode::Basic(Basic::Stack(Stack::Rotate {
            item_count: item_count.with_span(item_count_token.location),
            direction,
            shift_count: shift_count.with_span(shift_count_token.location),
        })),
        delim.close.location,
    ))
}

fn parse_integer_op<'a>(
    stores: &Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    is_known_negative: bool,
) -> ParseOpResult {
    let mut had_error = ErrorSignal::new();
    let mut overall_location = token.location;
    let literal_value: u64 = match parse_integer_lexeme(stores, token) {
        Ok(lit) => lit,
        Err(_) => {
            had_error.set();
            0
        }
    };

    if is_known_negative && literal_value.to_i64().is_none() {
        diagnostics::emit_error(
            stores,
            token.location,
            "literal out of range of signed integer",
            [Label::new(token.location).with_color(Color::Red)],
            None,
        );
        return Err(());
    }

    let (width, value) = if token_iter
        .peek()
        .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
    {
        let delim = get_delimited_tokens(
            stores,
            token_iter,
            token,
            Some(1),
            ("(", |t| t == TokenKind::ParenthesisOpen),
            ("Ident", |t| t == TokenKind::Ident),
            (")", |t| t == TokenKind::ParenthesisClosed),
        )?;
        let ident_token = delim.list[0];
        overall_location = overall_location.merge(delim.close.location);

        let (width, is_signed_kind) = match stores.strings.resolve(ident_token.inner.lexeme) {
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
                    stores,
                    ident_token.location,
                    "invalid integer type",
                    [Label::new(ident_token.location)
                        .with_color(Color::Red)
                        .with_message("unknown type")],
                    None,
                );
                return Err(());
            }
        };

        // The user specified an unsigned type, but gave a negative literal.
        if is_signed_kind == Signedness::Unsigned && is_known_negative {
            diagnostics::emit_error(
                stores,
                ident_token.location,
                "signed integer literal with unsigned type kind",
                [Label::new(token.location).with_color(Color::Red)],
                None,
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
                        stores,
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
                    );
                    return Err(());
                }
                IntKind::Signed(value)
            }
            Signedness::Unsigned => {
                if !width.bounds_unsigned().contains(&literal_value) {
                    diagnostics::emit_error(
                        stores,
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
    if had_error.into_bool() {
        return Err(());
    }

    Ok((
        OpCode::Basic(Basic::PushInt { width, value }),
        overall_location,
    ))
}

pub fn parse_drop_dup_over_reverse_swap_syscall<'a>(
    stores: &Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
) -> ParseOpResult {
    let (count, op_end) = if token_iter
        .peek()
        .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
    {
        parse_integer_param(stores, token_iter, token)?
    } else {
        let default_amount = if token.inner.kind == TokenKind::Reverse {
            2
        } else {
            1
        };
        (default_amount.with_span(token.location), token.location)
    };

    let opcode = match token.inner.kind {
        TokenKind::Drop => Basic::Stack(Stack::Drop { count }),
        TokenKind::Dup => Basic::Stack(Stack::Dup { count }),
        TokenKind::Over => Basic::Stack(Stack::Over { depth: count }),
        TokenKind::Reverse => Basic::Stack(Stack::Reverse { count }),
        TokenKind::Swap => Basic::Stack(Stack::Swap { count }),
        TokenKind::SysCall => Basic::Control(Control::SysCall { arg_count: count }),

        _ => unreachable!(),
    };

    Ok((OpCode::Basic(opcode), op_end))
}

pub fn parse_pack<'a>(
    stores: &mut Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
) -> ParseOpResult {
    let delim = get_delimited_tokens(
        stores,
        token_iter,
        token,
        None,
        ("(", |t| t == TokenKind::ParenthesisOpen),
        ("integer or type", valid_type_token),
        (")", |t| t == TokenKind::ParenthesisClosed),
    )?;

    if delim.list.len() == 1 && matches!(delim.list[0].inner.kind, TokenKind::Integer { .. }) {
        let count_token = delim.list[0];
        let count = parse_integer_lexeme(stores, count_token)?;

        Ok((
            OpCode::Basic(Basic::Memory(Memory::PackArray { count })),
            delim.close.location,
        ))
    } else {
        let span = delim.span();

        let mut unresolved_types = parse_unresolved_types(stores, delim.open, &delim.list)?;

        if unresolved_types.len() != 1 {
            diagnostics::emit_error(
                stores,
                span,
                format!("expected 1 type, found {}", unresolved_types.len()),
                [Label::new(span).with_color(Color::Red)],
                None,
            );
            return Err(());
        }

        let unresolved_type = unresolved_types.pop().unwrap();
        Ok((
            OpCode::Complex(UnresolvedOp::PackStruct {
                id: unresolved_type.inner,
            }),
            delim.close.location,
        ))
    }
}

pub fn parse_if<'a>(
    ctx: &mut Context,
    stores: &mut Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
) -> ParseOpResult {
    let condition_tokens = get_terminated_tokens(
        stores,
        token_iter,
        keyword,
        None,
        ("any", |_| true),
        ("do", |t| t == TokenKind::Do),
    )?;

    let condition =
        parse_item_body_contents(ctx, stores, &condition_tokens.list, op_id_gen, parent_id)?;

    let then_block_tokens = get_terminated_tokens(
        stores,
        token_iter,
        condition_tokens.close,
        None,
        ("any", |_| true),
        ("end`, `else` or `elif", |t| {
            matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif)
        }),
    )?;
    let mut close_token = then_block_tokens.close;

    let then_block =
        parse_item_body_contents(ctx, stores, &then_block_tokens.list, op_id_gen, parent_id)?;

    let else_token = close_token;
    let mut elif_blocks = Vec::new();

    while close_token.inner.kind == TokenKind::Elif {
        let elif_condition_tokens = get_terminated_tokens(
            stores,
            token_iter,
            close_token,
            None,
            ("any", |_| true),
            ("do", |t| t == TokenKind::Do),
        )?;

        let elif_condition = parse_item_body_contents(
            ctx,
            stores,
            &elif_condition_tokens.list,
            op_id_gen,
            parent_id,
        )?;

        let elif_block_tokens = get_terminated_tokens(
            stores,
            token_iter,
            elif_condition_tokens.close,
            None,
            ("any", |_| true),
            ("end`, `else`, or `elif", |t| {
                matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif)
            }),
        )?;

        let elif_block =
            parse_item_body_contents(ctx, stores, &elif_block_tokens.list, op_id_gen, parent_id)?;

        elif_blocks.push((
            close_token,
            elif_condition,
            elif_condition_tokens.close,
            elif_block,
            elif_block_tokens.close,
        ));
        close_token = elif_block_tokens.close;
    }

    let mut else_block = if close_token.inner.kind == TokenKind::Else {
        let else_block_tokens = get_terminated_tokens(
            stores,
            token_iter,
            close_token,
            None,
            ("any", |_| true),
            ("end", |t| t == TokenKind::End),
        )?;

        let else_block =
            parse_item_body_contents(ctx, stores, &else_block_tokens.list, op_id_gen, parent_id)?;

        close_token = else_block_tokens.close;

        else_block
    } else {
        Vec::new()
    };

    // Normalize into an `if <cond> do <body> else <body> end` structure.
    while let Some((open_token, condition, do_token, then_block, else_token)) = elif_blocks.pop() {
        let if_tokens = IfTokens {
            do_token: do_token.location,
            else_token: else_token.location,
            end_token: close_token.location,
        };
        let if_code = If {
            tokens: if_tokens,
            condition: TerminalBlock {
                block: condition,
                is_terminal: false,
            },
            then_block: TerminalBlock {
                block: then_block,
                is_terminal: false,
            },
            else_block: TerminalBlock {
                block: else_block,
                is_terminal: false,
            },
        };
        let if_op = Op::new(
            op_id_gen(),
            OpCode::Complex(UnresolvedOp::If(Box::new(if_code))),
            open_token.map(|t| t.lexeme),
        );

        else_block = vec![if_op];
    }

    let if_tokens = IfTokens {
        do_token: condition_tokens.close.location,
        else_token: else_token.location,
        end_token: close_token.location,
    };
    let if_code = If {
        tokens: if_tokens,
        condition: TerminalBlock {
            block: condition,
            is_terminal: false,
        },
        then_block: TerminalBlock {
            block: then_block,
            is_terminal: false,
        },
        else_block: TerminalBlock {
            block: else_block,
            is_terminal: false,
        },
    };
    Ok((
        OpCode::Complex(UnresolvedOp::If(Box::new(if_code))),
        close_token.location,
    ))
}

pub fn parse_while<'a>(
    ctx: &mut Context,
    stores: &mut Stores,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
) -> ParseOpResult {
    let condition_tokens = get_terminated_tokens(
        stores,
        token_iter,
        keyword,
        None,
        ("any", |_| true),
        ("do", |t| t == TokenKind::Do),
    )?;

    let condition =
        parse_item_body_contents(ctx, stores, &condition_tokens.list, op_id_gen, parent_id)?;

    let body_tokens = get_terminated_tokens(
        stores,
        token_iter,
        condition_tokens.close,
        None,
        ("any", |_| true),
        ("end", |t| t == TokenKind::End),
    )?;

    let body_block =
        parse_item_body_contents(ctx, stores, &body_tokens.list, op_id_gen, parent_id)?;

    let while_tokens = WhileTokens {
        do_token: condition_tokens.close.location,
        end_token: body_tokens.close.location,
    };
    let while_code = While {
        tokens: while_tokens,
        condition: TerminalBlock {
            block: condition,
            is_terminal: false,
        },
        body_block: TerminalBlock {
            block: body_block,
            is_terminal: false,
        },
    };

    Ok((
        OpCode::Complex(UnresolvedOp::While(Box::new(while_code))),
        body_tokens.close.location,
    ))
}
