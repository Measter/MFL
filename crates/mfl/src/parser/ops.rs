use std::iter::Peekable;

use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    diagnostics,
    interners::Interner,
    lexer::{Token, TokenKind},
    opcode::{Direction, If, IntKind, Op, OpCode, OpId, While},
    program::{ItemId, Program},
    source_file::{SourceStorage, Spanned, WithSpan},
    type_store::{IntWidth, Signedness, UnresolvedType},
};

use super::{
    parse_item_body_contents,
    utils::{
        get_delimited_tokens, get_terminated_tokens, parse_ident, parse_integer_lexeme,
        parse_integer_param, parse_unresolved_types, valid_type_token, ParseOpResult,
    },
};

pub fn parse_simple_op<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    interner: &Interner,
    source_store: &SourceStorage,
) -> ParseOpResult {
    let code = match token.inner.kind {
        TokenKind::Drop
        | TokenKind::Dup
        | TokenKind::Over
        | TokenKind::Reverse
        | TokenKind::Swap
        | TokenKind::SysCall => {
            return parse_drop_dup_over_reverse_swap_syscall(
                token_iter,
                token,
                interner,
                source_store,
            );
        }

        TokenKind::Pack => return parse_pack(token_iter, token, interner, source_store),
        TokenKind::Unpack => OpCode::Unpack,
        TokenKind::Rot => return parse_rot(token_iter, token, interner, source_store),

        TokenKind::Cast | TokenKind::SizeOf => {
            return parse_cast_sizeof(token_iter, token, interner, source_store)
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
            return parse_ident_op(token_iter, interner, source_store, token)
        }
        TokenKind::Integer { .. } => {
            return parse_integer_op(token_iter, token, false, interner, source_store)
        }
        TokenKind::String { id, is_c_str } => OpCode::PushStr { id, is_c_str },
        TokenKind::Here(id) => OpCode::PushStr {
            id,
            is_c_str: false,
        },
        TokenKind::EmitStack => return parse_emit_stack(token_iter, token, interner, source_store),

        TokenKind::Minus => return parse_minus(token_iter, token, interner, source_store),
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
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    interner: &Interner,
    source_store: &SourceStorage,
    token: Spanned<Token>,
) -> Result<(OpCode, crate::source_file::SourceLocation), ()> {
    let mut local_had_error = false;

    let (ident, last_token) = parse_ident(
        token_iter,
        interner,
        source_store,
        &mut local_had_error,
        token,
    )?;

    if local_had_error {
        return Err(());
    }

    Ok((
        OpCode::UnresolvedIdent(ident),
        token.location.merge(last_token.location),
    ))
}

fn parse_minus<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    interner: &Interner,
    source_store: &SourceStorage,
) -> ParseOpResult {
    Ok(match token_iter.peek().copied() {
        Some((_, int_token))
            if int_token.location.neighbour_of(token.location)
                && matches!(int_token.inner.kind, TokenKind::Integer { .. }) =>
        {
            token_iter.next();
            let mut int_token = *int_token;
            int_token.location = int_token.location.merge(token.location);
            parse_integer_op(token_iter, int_token, true, interner, source_store)?
        }
        _ => (OpCode::Subtract, token.location),
    })
}

fn parse_emit_stack<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    interner: &Interner,
    source_store: &SourceStorage,
) -> ParseOpResult {
    let (emit_labels, loc) = if token_iter
        .peek()
        .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
    {
        let delim = get_delimited_tokens(
            token_iter,
            token,
            Some(1),
            ("(", |t| t == TokenKind::ParenthesisOpen),
            ("bool", |t| matches!(t, TokenKind::Boolean(_))),
            (")", |t| t == TokenKind::ParenthesisClosed),
            interner,
            source_store,
        )?;

        let emit_token = delim.list[0];
        let TokenKind::Boolean(emit_labels) = emit_token.inner.kind else {
            unreachable!()
        };

        (emit_labels, delim.close.location)
    } else {
        (false, token.location)
    };

    Ok((OpCode::EmitStack(emit_labels), loc))
}

fn parse_cast_sizeof<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    interner: &Interner,
    source_store: &SourceStorage,
) -> ParseOpResult {
    let delim = get_delimited_tokens(
        token_iter,
        token,
        None,
        ("(", |t| t == TokenKind::ParenthesisOpen),
        ("Ident", valid_type_token),
        (")", |t| t == TokenKind::ParenthesisClosed),
        interner,
        source_store,
    )?;

    let span = delim.span();
    let mut unresolved_types =
        parse_unresolved_types(interner, source_store, delim.open, &delim.list)?;

    if unresolved_types.len() != 1 {
        diagnostics::emit_error(
            span,
            format!("expected 1 type, found {}", unresolved_types.len()),
            [Label::new(span).with_color(Color::Red)],
            None,
            source_store,
        );
        return Err(());
    }

    let unresolved_type = unresolved_types.pop().unwrap().inner;

    Ok(match token.inner.kind {
        TokenKind::Cast => (
            OpCode::UnresolvedCast {
                unresolved_type: UnresolvedType::Tokens(unresolved_type),
            },
            delim.close.location,
        ),
        TokenKind::SizeOf => (
            OpCode::UnresolvedSizeOf {
                unresolved_type: UnresolvedType::Tokens(unresolved_type),
            },
            delim.close.location,
        ),
        _ => unreachable!(),
    })
}

fn parse_rot<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    interner: &Interner,
    source_store: &SourceStorage,
) -> ParseOpResult {
    let delim = get_delimited_tokens(
        token_iter,
        token,
        Some(3),
        ("(", |t| t == TokenKind::ParenthesisOpen),
        ("", |_| true),
        (")", |t| t == TokenKind::ParenthesisClosed),
        interner,
        source_store,
    )?;

    let mut local_error = false;
    let [item_count_token, direction_token, shift_count_token] = &*delim.list else {
        unreachable!()
    };
    let item_count_token = *item_count_token;
    let shift_count_token = *shift_count_token;
    let item_count = if !matches!(item_count_token.inner.kind, TokenKind::Integer { .. }) {
        diagnostics::emit_error(
            item_count_token.location,
            format!(
                "expected `integer`, found `{}`",
                interner.resolve(item_count_token.inner.lexeme)
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

    let shift_count = if !matches!(shift_count_token.inner.kind, TokenKind::Integer { .. }) {
        diagnostics::emit_error(
            shift_count_token.location,
            format!(
                "expected `integer`, found `{}`",
                interner.resolve(shift_count_token.inner.lexeme)
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
                    interner.resolve(direction_token.inner.lexeme)
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
        return Err(());
    }

    Ok((
        OpCode::Rot {
            item_count: item_count.with_span(item_count_token.location),
            direction,
            shift_count: shift_count.with_span(shift_count_token.location),
        },
        delim.close.location,
    ))
}

fn parse_integer_op<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    is_known_negative: bool,
    interner: &Interner,
    source_store: &SourceStorage,
) -> ParseOpResult {
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
        return Err(());
    }

    let (width, value) = if token_iter
        .peek()
        .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
    {
        let delim = get_delimited_tokens(
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

        let (width, is_signed_kind) = match interner.resolve(ident_token.inner.lexeme) {
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

pub fn parse_drop_dup_over_reverse_swap_syscall<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    interner: &Interner,
    source_store: &SourceStorage,
) -> ParseOpResult {
    let (count, op_end) = if token_iter
        .peek()
        .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
    {
        parse_integer_param(token_iter, token, interner, source_store)?
    } else {
        let default_amount = if token.inner.kind == TokenKind::Reverse {
            2
        } else {
            1
        };
        (default_amount.with_span(token.location), token.location)
    };

    let opcode = match token.inner.kind {
        TokenKind::Drop => OpCode::Drop { count },
        TokenKind::Dup => OpCode::Dup { count },
        TokenKind::Over => OpCode::Over { depth: count },
        TokenKind::Reverse => OpCode::Reverse { count },
        TokenKind::Swap => OpCode::Swap { count },
        TokenKind::SysCall => OpCode::SysCall { arg_count: count },

        _ => unreachable!(),
    };

    Ok((opcode, op_end))
}

pub fn parse_pack<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    interner: &Interner,
    source_store: &SourceStorage,
) -> ParseOpResult {
    let delim = get_delimited_tokens(
        token_iter,
        token,
        None,
        ("(", |t| t == TokenKind::ParenthesisOpen),
        ("integer or type", valid_type_token),
        (")", |t| t == TokenKind::ParenthesisClosed),
        interner,
        source_store,
    )?;

    if delim.list.len() == 1 && matches!(delim.list[0].inner.kind, TokenKind::Integer { .. }) {
        let count_token = delim.list[0];
        let count = parse_integer_lexeme(count_token, interner, source_store)?;

        Ok((OpCode::PackArray { count }, delim.close.location))
    } else {
        let span = delim.span();

        let mut unresolved_types =
            parse_unresolved_types(interner, source_store, delim.open, &delim.list)?;

        if unresolved_types.len() != 1 {
            diagnostics::emit_error(
                span,
                format!("expected 1 type, found {}", unresolved_types.len()),
                [Label::new(span).with_color(Color::Red)],
                None,
                source_store,
            );
            return Err(());
        }

        let unresolved_type = unresolved_types.pop().unwrap();
        Ok((
            OpCode::UnresolvedPackStruct {
                unresolved_type: UnresolvedType::Tokens(unresolved_type.inner),
            },
            delim.close.location,
        ))
    }
}

pub fn parse_if<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
    interner: &mut Interner,
    source_store: &SourceStorage,
) -> ParseOpResult {
    let condition_tokens = get_terminated_tokens(
        token_iter,
        keyword,
        None,
        ("any", |_| true),
        ("do", |t| t == TokenKind::Do),
        interner,
        source_store,
    )?;

    let condition = parse_item_body_contents(
        program,
        &condition_tokens.list,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let then_block_tokens = get_terminated_tokens(
        token_iter,
        condition_tokens.close,
        None,
        ("any", |_| true),
        ("end`, `else` or `elif", |t| {
            matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif)
        }),
        interner,
        source_store,
    )?;
    let mut close_token = then_block_tokens.close;

    let then_block = parse_item_body_contents(
        program,
        &then_block_tokens.list,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let else_token = close_token;
    let mut elif_blocks = Vec::new();

    while close_token.inner.kind == TokenKind::Elif {
        let elif_condition_tokens = get_terminated_tokens(
            token_iter,
            close_token,
            None,
            ("any", |_| true),
            ("do", |t| t == TokenKind::Do),
            interner,
            source_store,
        )?;

        let elif_condition = parse_item_body_contents(
            program,
            &elif_condition_tokens.list,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        let elif_block_tokens = get_terminated_tokens(
            token_iter,
            elif_condition_tokens.close,
            None,
            ("any", |_| true),
            ("end`, `else`, or `elif", |t| {
                matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif)
            }),
            interner,
            source_store,
        )?;

        let elif_block = parse_item_body_contents(
            program,
            &elif_block_tokens.list,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

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
            token_iter,
            close_token,
            None,
            ("any", |_| true),
            ("end", |t| t == TokenKind::End),
            interner,
            source_store,
        )?;

        let else_block = parse_item_body_contents(
            program,
            &else_block_tokens.list,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        close_token = else_block_tokens.close;

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

    Ok((
        OpCode::If(Box::new(If {
            open_token: keyword.location,
            condition,
            is_condition_terminal: false,
            do_token: condition_tokens.close.location,
            then_block,
            is_then_terminal: false,
            else_token: else_token.location,
            else_block,
            is_else_terminal: false,
            end_token: close_token.location,
        })),
        close_token.location,
    ))
}

pub fn parse_while<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
    interner: &mut Interner,
    source_store: &SourceStorage,
) -> ParseOpResult {
    let condition_tokens = get_terminated_tokens(
        token_iter,
        keyword,
        None,
        ("any", |_| true),
        ("do", |t| t == TokenKind::Do),
        interner,
        source_store,
    )?;

    let condition = parse_item_body_contents(
        program,
        &condition_tokens.list,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let body_tokens = get_terminated_tokens(
        token_iter,
        condition_tokens.close,
        None,
        ("any", |_| true),
        ("end", |t| t == TokenKind::End),
        interner,
        source_store,
    )?;

    let body_block = parse_item_body_contents(
        program,
        &body_tokens.list,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    Ok((
        OpCode::While(Box::new(While {
            do_token: condition_tokens.close.location,
            condition,
            body_block,
            end_token: body_tokens.close.location,
        })),
        body_tokens.close.location,
    ))
}
