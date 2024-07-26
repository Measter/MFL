use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;

use crate::{
    context::{Context, ItemId},
    diagnostics,
    error_signal::ErrorSignal,
    ir::{
        Arithmetic, Basic, Compare, Control, Direction, If, IfTokens, IntKind, Memory, OpCode,
        Stack, UnresolvedOp, While, WhileTokens,
    },
    lexer::{BracketKind, Extract, Insert, StringToken, Token, TokenKind, TokenTree},
    stores::{
        ops::OpId,
        source::{SourceLocation, Spanned, WithSpan},
        types::{IntWidth, Signedness},
    },
    Stores,
};

use super::{
    parse_item_body_contents,
    utils::{
        get_terminated_tokens, parse_ident, parse_integer_lexeme, parse_integer_param,
        parse_multiple_unresolved_types, valid_type_token, ConditionMatch, ExpectedTokenMatcher,
        Matcher, ParseOpResult, TokenIter, TokenTreeOptionExt, TreeGroupResultExt,
    },
};

pub fn parse_extract_insert_array(token: Spanned<Token>) -> (OpCode<UnresolvedOp>, SourceLocation) {
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

    (OpCode::Basic(Basic::Memory(kind)), loc)
}

pub fn parse_extract_insert_struct(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    mut token: Spanned<Token>,
) -> Result<SmallVec<[OpId; 1]>, ()> {
    let mut ops = SmallVec::new();

    let delim = token_iter
        .expect_group(stores, BracketKind::Paren, token)
        .with_kinds(
            stores,
            Matcher("ident", |t: TokenKind| {
                t == TokenKind::Ident || t == TokenKind::Dot
            }),
        )?;

    token.location = token.location.merge(delim.span());
    let mut delim_iter = TokenIter::new(delim.tokens.iter());
    let mut idents = Vec::new();

    // We want to make sure the Dots exist, but we don't actually want them.
    let mut local_had_error = ErrorSignal::new();
    let mut prev_token = delim.open;
    loop {
        let Ok(next) = delim_iter.expect_single(stores, TokenKind::Ident, prev_token.location)
        else {
            local_had_error.set();
            break;
        };
        idents.push(next);

        if delim_iter.next_is_single(TokenKind::Dot) {
            prev_token = delim_iter.next().unwrap().last_token();
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

                ops.push(stores.ops.new_op(first, token.map(|t| t.lexeme)));
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
                ops.push(stores.ops.new_op(xtr, token.map(|t| t.lexeme)));
            }

            let rot_len = (idents.len() + 1).to_u8().unwrap();
            let rot = OpCode::Basic(Basic::Stack(Stack::Rotate {
                item_count: rot_len.with_span(token.location),
                direction: Direction::Left,
                shift_count: 1.with_span(token.location),
            }));
            ops.push(stores.ops.new_op(rot, token.map(|t| t.lexeme)));

            let [first, prev @ ..] = idents.as_slice() else {
                unreachable!()
            };
            for ident in prev.iter().rev() {
                let swap = OpCode::Basic(Basic::Stack(Stack::Swap {
                    count: 1.with_span(token.location),
                }));
                ops.push(stores.ops.new_op(swap, token.map(|t| t.lexeme)));
                let ins = OpCode::Basic(Basic::Memory(Memory::InsertStruct {
                    emit_struct: true,
                    field_name: ident.map(|t| t.lexeme),
                }));
                ops.push(stores.ops.new_op(ins, token.map(|t| t.lexeme)));
            }

            let swap = OpCode::Basic(Basic::Stack(Stack::Swap {
                count: 1.with_span(token.location),
            }));
            ops.push(stores.ops.new_op(swap, token.map(|t| t.lexeme)));
            let kind = OpCode::Basic(Basic::Memory(Memory::InsertStruct {
                emit_struct,
                field_name: first.map(|t| t.lexeme),
            }));
            ops.push(stores.ops.new_op(kind, token.map(|t| t.lexeme)));
        }
        TokenKind::Insert(Insert { emit_struct }) => {
            let code = OpCode::Basic(Basic::Memory(Memory::InsertStruct {
                emit_struct,
                field_name: idents[0].map(|t| t.lexeme),
            }));
            ops.push(stores.ops.new_op(code, token.map(|t| t.lexeme)));
        }
        _ => unreachable!(),
    }

    Ok(ops)
}

pub fn parse_simple_op(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
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

fn parse_ident_op(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
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

fn parse_minus(
    stores: &Stores,
    token_iter: &mut TokenIter,
    token: Spanned<Token>,
) -> ParseOpResult {
    if token_iter.next_is_single_and(
        Matcher("integer literal", |t| matches!(t, TokenKind::Integer(_))),
        |t| t.location.neighbour_of(token.location),
    ) {
        let mut int_token = token_iter.next().unwrap_single();
        int_token.location = int_token.location.merge(token.location);
        parse_integer_op(stores, token_iter, int_token, true)
    } else {
        Ok((
            OpCode::Basic(Basic::Arithmetic(Arithmetic::Subtract)),
            token.location,
        ))
    }
}

fn parse_emit_stack(
    stores: &Stores,
    token_iter: &mut TokenIter,
    token: Spanned<Token>,
) -> ParseOpResult {
    let (emit_labels, loc) = if token_iter.next_is_group(BracketKind::Paren) {
        let delim = token_iter
            .expect_group(stores, BracketKind::Paren, token)
            .with_kinds(
                stores,
                Matcher("bool literal", |t| matches!(t, TokenKind::Boolean(_))),
            )
            .with_length(stores, 1)?;

        let emit_token = delim.tokens[0].unwrap_single();
        let TokenKind::Boolean(emit_labels) = emit_token.inner.kind else {
            unreachable!()
        };

        (emit_labels, delim.last_token().location)
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

fn parse_cast_sizeof(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    token: Spanned<Token>,
) -> ParseOpResult {
    let delim = token_iter
        .expect_group(stores, BracketKind::Paren, token)
        .with_kinds(stores, Matcher("ident", valid_type_token))?;

    let span = delim.span();
    let mut unresolved_types =
        parse_multiple_unresolved_types(stores, delim.open.location, &delim.tokens)?;

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

    Ok((OpCode::Complex(code), delim.last_token().location))
}

fn parse_rot(stores: &Stores, token_iter: &mut TokenIter, token: Spanned<Token>) -> ParseOpResult {
    let delim = token_iter
        .expect_group(stores, BracketKind::Paren, token)
        .with_length(stores, 3)?;

    let mut had_error = ErrorSignal::new();
    let [item_count_token, direction_token, shift_count_token] = &*delim.tokens else {
        unreachable!()
    };

    let int_matcher = Matcher("integer literal", |t| matches!(t, TokenKind::Integer(_)));
    let item_count = if !int_matcher.is_match(item_count_token) {
        diagnostics::emit_error(
            stores,
            item_count_token.span(),
            format!(
                "expected `integer literal`, found `{}`",
                item_count_token.kind_str(),
            ),
            Some(Label::new(item_count_token.span()).with_color(Color::Red)),
            None,
        );
        had_error.set();
        1
    } else {
        parse_integer_lexeme(stores, item_count_token.unwrap_single())?
    };

    let shift_count = if !int_matcher.is_match(shift_count_token) {
        diagnostics::emit_error(
            stores,
            shift_count_token.span(),
            format!(
                "expected `integer literal`, found `{}`",
                shift_count_token.kind_str()
            ),
            Some(Label::new(shift_count_token.span()).with_color(Color::Red)),
            None,
        );
        had_error.set();
        1
    } else {
        parse_integer_lexeme(stores, shift_count_token.unwrap_single())?
    };

    let direction = if TokenKind::Less.is_match(direction_token)
        | TokenKind::Greater.is_match(direction_token)
    {
        match direction_token.unwrap_single().inner.kind {
            TokenKind::Less => Direction::Left,
            TokenKind::Greater => Direction::Right,
            _ => unreachable!(),
        }
    } else {
        diagnostics::emit_error(
            stores,
            direction_token.span(),
            format!(
                "expected `<` or `>`, found `{}`",
                direction_token.kind_str()
            ),
            Some(Label::new(direction_token.span()).with_color(Color::Red)),
            None,
        );
        had_error.set();
        Direction::Left
    };

    if had_error.into_bool() {
        return Err(());
    }

    Ok((
        OpCode::Basic(Basic::Stack(Stack::Rotate {
            item_count: item_count.with_span(item_count_token.span()),
            direction,
            shift_count: shift_count.with_span(shift_count_token.span()),
        })),
        delim.last_token().location,
    ))
}

fn parse_integer_op(
    stores: &Stores,
    token_iter: &mut TokenIter,
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

    let (width, value) = if token_iter.next_is_group(BracketKind::Paren) {
        let delim = token_iter
            .expect_group(stores, BracketKind::Paren, token)
            .with_kinds(stores, TokenKind::Ident)
            .with_length(stores, 1)?;

        let ident_token = delim.tokens[0].unwrap_single();
        overall_location = overall_location.merge(delim.last_token().location);

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

pub fn parse_drop_dup_over_reverse_swap_syscall(
    stores: &Stores,
    token_iter: &mut TokenIter,
    token: Spanned<Token>,
) -> ParseOpResult {
    let (count, op_end) = if token_iter.next_is_group(BracketKind::Paren) {
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

pub fn parse_pack(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    token: Spanned<Token>,
) -> ParseOpResult {
    let delim = token_iter
        .expect_group(stores, BracketKind::Paren, token)
        .with_kinds(
            stores,
            Matcher("integer literal` or `type", valid_type_token),
        )?;

    let int_matcher = Matcher("integer literal", |t| matches!(t, TokenKind::Integer(_)));

    if delim.tokens.len() == 1 && int_matcher.is_match(&delim.tokens[0]) {
        let count_token = delim.tokens[0].unwrap_single();
        let count = parse_integer_lexeme(stores, count_token)?;

        Ok((
            OpCode::Basic(Basic::Memory(Memory::PackArray { count })),
            delim.last_token().location,
        ))
    } else {
        let span = delim.span();

        let mut unresolved_types =
            parse_multiple_unresolved_types(stores, delim.open.location, &delim.tokens)?;

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
            delim.last_token().location,
        ))
    }
}

pub fn parse_if(
    ctx: &mut Context,
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> ParseOpResult {
    let condition_tokens = get_terminated_tokens(
        stores,
        token_iter,
        keyword,
        None,
        Matcher("any", |_: &TokenTree| true),
        ConditionMatch,
        false,
    )?;

    let condition = parse_item_body_contents(ctx, stores, &condition_tokens.list, parent_id)?;
    let condition = stores.blocks.new_block(condition);

    let then_block_tokens =
        token_iter.expect_group(stores, BracketKind::Brace, condition_tokens.close)?;
    let mut close_token = then_block_tokens.last_token();

    let then_block = parse_item_body_contents(ctx, stores, &then_block_tokens.tokens, parent_id)?;
    let then_block = stores.blocks.new_block(then_block);

    let else_token = close_token;
    let mut elif_blocks = Vec::new();

    while token_iter.next_is(TokenKind::Elif) {
        let elif_token = token_iter.next().unwrap_single();
        let elif_condition_tokens = get_terminated_tokens(
            stores,
            token_iter,
            elif_token,
            None,
            Matcher("any", |_: &TokenTree| true),
            ConditionMatch,
            false,
        )?;

        let elif_condition =
            parse_item_body_contents(ctx, stores, &elif_condition_tokens.list, parent_id)?;
        let elif_condition = stores.blocks.new_block(elif_condition);

        let elif_block_tokens =
            token_iter.expect_group(stores, BracketKind::Brace, elif_condition_tokens.close)?;

        let elif_block =
            parse_item_body_contents(ctx, stores, &elif_block_tokens.tokens, parent_id)?;
        let elif_block = stores.blocks.new_block(elif_block);

        elif_blocks.push((
            close_token,
            elif_condition,
            elif_condition_tokens.close,
            elif_block,
            elif_block_tokens.last_token(),
        ));
        close_token = elif_block_tokens.last_token();
    }

    let else_block = if token_iter.next_is(TokenKind::Else) {
        let else_token = token_iter.next().unwrap_single();
        let else_block_tokens = token_iter.expect_group(stores, BracketKind::Brace, else_token)?;
        let else_block =
            parse_item_body_contents(ctx, stores, &else_block_tokens.tokens, parent_id)?;
        close_token = else_block_tokens.last_token();
        else_block
    } else {
        Vec::new()
    };
    let mut else_block = stores.blocks.new_block(else_block);

    // Normalize into an `if <cond> do <body> else <body> end` structure.
    while let Some((open_token, condition, do_token, then_block, else_token)) = elif_blocks.pop() {
        let if_tokens = IfTokens {
            do_token: do_token.location,
            else_token: else_token.location,
            end_token: close_token.location,
        };
        let if_code = If {
            tokens: if_tokens,
            condition,
            then_block,
            else_block,
        };
        let if_op = stores.ops.new_op(
            OpCode::Basic(Basic::Control(Control::If(if_code))),
            open_token.map(|t| t.lexeme),
        );

        else_block = stores.blocks.new_block(vec![if_op]);
    }

    let if_tokens = IfTokens {
        do_token: condition_tokens.close.location,
        else_token: else_token.location,
        end_token: close_token.location,
    };
    let if_code = If {
        tokens: if_tokens,
        condition,
        then_block,
        else_block,
    };
    Ok((
        OpCode::Basic(Basic::Control(Control::If(if_code))),
        close_token.location,
    ))
}

pub fn parse_while(
    ctx: &mut Context,
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> ParseOpResult {
    let condition_tokens = get_terminated_tokens(
        stores,
        token_iter,
        keyword,
        None,
        Matcher("any", |_: &TokenTree| true),
        ConditionMatch,
        false,
    )?;

    let condition = parse_item_body_contents(ctx, stores, &condition_tokens.list, parent_id)?;
    let condition = stores.blocks.new_block(condition);

    let body_tokens =
        token_iter.expect_group(stores, BracketKind::Brace, condition_tokens.close)?;

    let body_block = parse_item_body_contents(ctx, stores, &body_tokens.tokens, parent_id)?;
    let body_block = stores.blocks.new_block(body_block);

    let while_tokens = WhileTokens {
        do_token: condition_tokens.close.location,
        end_token: body_tokens.last_token().location,
    };
    let while_code = While {
        tokens: while_tokens,
        condition,
        body_block,
    };

    Ok((
        OpCode::Basic(Basic::Control(Control::While(while_code))),
        body_tokens.last_token().location,
    ))
}
