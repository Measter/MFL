use intcast::IntCast;
use lexer::{BracketKind, Extract, Insert, StringToken, Token, TokenKind};
use smallvec::SmallVec;
use stores::{
    items::ItemId,
    source::{SourceLocation, Spanned, WithSpan},
};

use crate::{
    error_signal::ErrorSignal,
    ir::{
        Arithmetic, Basic, Compare, Cond, CondArm, Control, Direction, IdentPathRoot, Memory,
        OpCode, Stack, UnresolvedIdent, UnresolvedOp, While, WhileTokens,
    },
    lexer::TokenTree,
    parser::utils::parse_float_lexeme,
    stores::{
        diagnostics::Diagnostic,
        ops::OpId,
        types::{Float, FloatWidth, IntSignedness, IntWidth, Integer},
    },
    Stores,
};

use super::{
    matcher::{
        integer_tokens, valid_type_token, ConditionMatch, ExpectedTokenMatcher, IdentPathMatch,
        IsMatch, Matcher,
    },
    parse_item_body_contents,
    utils::{
        get_terminated_tokens, parse_ident, parse_integer_lexeme, parse_integer_param,
        parse_multiple_unresolved_types, ParseOpResult, TokenIter, TokenTreeOptionExt,
        TreeGroupResultExt,
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
    item_id: ItemId,
    mut token: Spanned<Token>,
) -> Result<SmallVec<[OpId; 1]>, ()> {
    let mut ops = SmallVec::new();

    let delim = token_iter
        .expect_group(stores, item_id, BracketKind::Paren, token)
        .with_kinds(
            stores,
            item_id,
            Matcher("ident", |t: Spanned<TokenKind>| {
                if matches!(t.inner, TokenKind::Ident | TokenKind::Dot) {
                    IsMatch::Yes
                } else {
                    IsMatch::No(t.inner.kind_str(), t.location)
                }
            }),
        )?;

    token.location = token.location.merge(delim.span());
    let mut delim_iter = TokenIter::new(delim.tokens.iter());
    let mut idents = Vec::new();

    // We want to make sure the Dots exist, but we don't actually want them.
    let mut local_had_error = ErrorSignal::new();
    let mut prev_token = delim.open;
    loop {
        let Ok(next) =
            delim_iter.expect_single(stores, item_id, TokenKind::Ident, prev_token.location)
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

    if local_had_error.into_err() {
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
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    let code = match token.inner.kind {
        TokenKind::Drop
        | TokenKind::Dup
        | TokenKind::Over
        | TokenKind::Reverse
        | TokenKind::Swap
        | TokenKind::SysCall => {
            return parse_drop_dup_over_reverse_swap_syscall(stores, token_iter, item_id, token);
        }

        TokenKind::Pack => return parse_pack(stores, token_iter, item_id, token),
        TokenKind::Unpack => OpCode::Basic(Basic::Memory(Memory::Unpack)),
        TokenKind::Rot => return parse_rot(stores, token_iter, item_id, token),

        TokenKind::Cast | TokenKind::SizeOf => {
            return parse_cast_sizeof(stores, token_iter, item_id, token)
        }

        TokenKind::Hash => OpCode::Basic(Basic::Memory(Memory::Index)),
        TokenKind::Load => OpCode::Basic(Basic::Memory(Memory::Load)),
        TokenKind::Store => OpCode::Basic(Basic::Memory(Memory::Store)),
        TokenKind::AssumeInit => return parse_assumeinit(stores, token_iter, item_id, token),

        TokenKind::IsNull => OpCode::Basic(Basic::Compare(Compare::IsNull)),
        TokenKind::Equal => OpCode::Basic(Basic::Compare(Compare::Equal)),
        TokenKind::Greater => OpCode::Basic(Basic::Compare(Compare::Greater)),
        TokenKind::GreaterEqual => OpCode::Basic(Basic::Compare(Compare::GreaterEqual)),
        TokenKind::Less => OpCode::Basic(Basic::Compare(Compare::Less)),
        TokenKind::LessEqual => OpCode::Basic(Basic::Compare(Compare::LessEqual)),
        TokenKind::NotEqual => OpCode::Basic(Basic::Compare(Compare::NotEq)),
        TokenKind::Ampersand | TokenKind::Pipe => {
            return parse_logical_and_or(stores, token_iter, item_id, token)
        }

        TokenKind::Boolean(b) => OpCode::Basic(Basic::PushBool(b)),
        TokenKind::Char(ch) => OpCode::Basic(Basic::PushInt {
            width: IntWidth::I8,
            value: Integer::Unsigned((ch as u8).to_u64()),
        }),

        TokenKind::Ident | TokenKind::ColonColon | TokenKind::SelfKw => {
            return parse_ident_op(stores, token_iter, item_id, token)
        }
        TokenKind::Integer { .. } => {
            return parse_integer_op(stores, token_iter, item_id, token, false)
        }
        TokenKind::Float => return parse_float_op(stores, token_iter, item_id, token, false),
        TokenKind::String(StringToken { id }) | TokenKind::Here(id) => {
            OpCode::Basic(Basic::PushStr { id })
        }
        TokenKind::EmitStack => return parse_emit_stack(stores, token_iter, item_id, token),

        TokenKind::Minus => return parse_minus(stores, token_iter, item_id, token),
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
        TokenKind::Exit => return parse_exit(stores, token_iter, item_id, token),

        _ => {
            panic!(
                "ICE: parse_item was given an op it can't handle: {:?}",
                token.inner.kind
            );
        }
    };

    Ok((code, token.location))
}

fn parse_exit(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    keyword: Spanned<Token>,
) -> Result<(OpCode<UnresolvedOp>, SourceLocation), ()> {
    let code = if token_iter.next_is_group(BracketKind::Paren) {
        let group = token_iter
            .expect_group(stores, item_id, BracketKind::Paren, keyword)
            .with_kinds(
                stores,
                item_id,
                Matcher("integer", |tk: Spanned<TokenKind>| {
                    if let TokenKind::Integer(_) = tk.inner {
                        IsMatch::Yes
                    } else {
                        IsMatch::No(tk.inner.kind_str(), tk.location)
                    }
                }),
            )
            .with_length(stores, item_id, 1)?;

        let code_token = group.tokens[0].unwrap_single();
        parse_integer_lexeme::<u8>(stores, item_id, code_token)?
    } else {
        0
    };

    Ok((
        OpCode::Basic(Basic::Control(Control::Exit(code))),
        keyword.location,
    ))
}

fn parse_assumeinit(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    keyword: Spanned<Token>,
) -> Result<(OpCode<UnresolvedOp>, SourceLocation), ()> {
    let group = token_iter
        .expect_group(stores, item_id, BracketKind::Paren, keyword)
        .with_kinds(stores, item_id, TokenKind::Ident)
        .with_length(stores, item_id, 1)?;

    let ident_token = group.tokens[0].unwrap_single();
    let ident = UnresolvedIdent {
        span: ident_token.location,
        path_root: IdentPathRoot::CurrentScope,
        path: vec![ident_token.map(|t| t.lexeme)],
        generic_params: Vec::new(),
    };
    Ok((
        OpCode::Complex(UnresolvedOp::AssumeInit(ident)),
        group.last_token().location,
    ))
}

fn parse_ident_op(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    let mut local_had_error = ErrorSignal::new();

    let Ok((ident, last_token)) =
        parse_ident(stores, &mut local_had_error, item_id, token_iter, token)
    else {
        local_had_error.forget();
        return Err(());
    };

    if local_had_error.into_err() {
        return Err(());
    }

    Ok((
        OpCode::Complex(UnresolvedOp::Ident(ident)),
        token.location.merge(last_token.location),
    ))
}

fn parse_minus(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    if token_iter.next_is_single_and(Matcher("integer literal", integer_tokens), |t| {
        t.location.neighbour_of(token.location)
    }) {
        let mut int_token = token_iter.next().unwrap_single();
        int_token.location = int_token.location.merge(token.location);
        parse_integer_op(stores, token_iter, item_id, int_token, true)
    } else {
        Ok((
            OpCode::Basic(Basic::Arithmetic(Arithmetic::Subtract)),
            token.location,
        ))
    }
}

fn parse_logical_and_or(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    let next = token_iter.expect_single(stores, item_id, token.inner.kind, token.location)?;
    let location = token.location.merge(next.location);

    if !next.location.neighbour_of(token.location) {
        let msg = if token.inner.kind == TokenKind::Ampersand {
            "expected `logical and`, found `& &`"
        } else {
            "expected `logical or`, found `| |`"
        };
        Diagnostic::error(location, msg).attached(stores.diags, item_id);
        return Err(());
    }

    let condition_block = if token.inner.kind == TokenKind::Ampersand {
        Vec::new()
    } else {
        let op = OpCode::Basic(Basic::Arithmetic(Arithmetic::BitNot));
        let op_id = stores
            .ops
            .new_op(op, token.inner.lexeme.with_span(location));
        vec![op_id]
    };

    let then_block = parse_item_body_contents(stores, token_iter, item_id)?;
    let op = OpCode::Basic(Basic::Control(Control::Cond(Cond {
        token: location,
        arms: vec![CondArm {
            condition: stores.blocks.new_block(condition_block),
            open: location,
            block: stores.blocks.new_block(then_block),
            close: location,
        }],
        implicit_else: true,
        else_block: stores.blocks.new_block(Vec::new()),
        else_close: location,
    })));

    Ok((op, location))
}

fn parse_emit_stack(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    let (emit_labels, loc) = if token_iter.next_is_group(BracketKind::Paren) {
        let delim = token_iter
            .expect_group(stores, item_id, BracketKind::Paren, token)
            .with_kinds(
                stores,
                item_id,
                Matcher("bool literal", |t: Spanned<TokenKind>| {
                    if let TokenKind::Boolean(_) = t.inner {
                        IsMatch::Yes
                    } else {
                        IsMatch::No(t.inner.kind_str(), t.location)
                    }
                }),
            )
            .with_length(stores, item_id, 1)?;

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
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    let delim = token_iter
        .expect_group(stores, item_id, BracketKind::Paren, token)
        .with_kinds(stores, item_id, Matcher("ident", valid_type_token))?;

    let span = delim.span();
    let mut unresolved_types =
        parse_multiple_unresolved_types(stores, item_id, delim.open.location, &delim.tokens)?;

    if unresolved_types.len() != 1 {
        Diagnostic::error(
            span,
            format!("expected 1 type, found {}", unresolved_types.len()),
        )
        .attached(stores.diags, item_id);
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

fn parse_rot(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    let delim = token_iter
        .expect_group(stores, item_id, BracketKind::Paren, token)
        .with_length(stores, item_id, 3)?;

    let mut had_error = ErrorSignal::new();
    let [item_count_token, direction_token, shift_count_token] = &*delim.tokens else {
        unreachable!()
    };

    let int_matcher = Matcher("integer literal", integer_tokens);
    let item_count = if int_matcher.is_match(item_count_token).no() {
        Diagnostic::error(
            item_count_token.span(),
            format!(
                "expected `integer literal`, found `{}`",
                item_count_token.kind_str(),
            ),
        )
        .attached(stores.diags, item_id);
        had_error.set();
        1
    } else {
        parse_integer_lexeme(stores, item_id, item_count_token.unwrap_single())?
    };

    let shift_count = if int_matcher.is_match(shift_count_token).no() {
        Diagnostic::error(
            shift_count_token.span(),
            format!(
                "expected `integer literal`, found `{}`",
                shift_count_token.kind_str()
            ),
        )
        .attached(stores.diags, item_id);
        had_error.set();
        1
    } else {
        parse_integer_lexeme(stores, item_id, shift_count_token.unwrap_single())?
    };

    let direction = if TokenKind::Less.is_match(direction_token).yes()
        | TokenKind::Greater.is_match(direction_token).yes()
    {
        match direction_token.unwrap_single().inner.kind {
            TokenKind::Less => Direction::Left,
            TokenKind::Greater => Direction::Right,
            _ => unreachable!(),
        }
    } else {
        Diagnostic::error(
            direction_token.span(),
            format!(
                "expected `<` or `>`, found `{}`",
                direction_token.kind_str()
            ),
        )
        .attached(stores.diags, item_id);
        had_error.set();
        Direction::Left
    };

    if had_error.into_err() {
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
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
    is_known_negative: bool,
) -> ParseOpResult {
    let mut had_error = ErrorSignal::new();
    let mut overall_location = token.location;
    let literal_value: u64 = match parse_integer_lexeme(stores, item_id, token) {
        Ok(lit) => lit,
        Err(_) => {
            had_error.set();
            0
        }
    };

    if is_known_negative && literal_value.to_i64().is_none() {
        Diagnostic::error(token.location, "literal out of range of signed integer")
            .attached(stores.diags, item_id);
        return Err(());
    }

    let (width, value) = if token_iter.next_is_group(BracketKind::Paren) {
        let delim = token_iter
            .expect_group(stores, item_id, BracketKind::Paren, token)
            .with_kinds(stores, item_id, TokenKind::Ident)
            .with_length(stores, item_id, 1)?;

        let ident_token = delim.tokens[0].unwrap_single();
        overall_location = overall_location.merge(delim.last_token().location);

        let (width, is_signed_kind) = match stores.strings.resolve(ident_token.inner.lexeme) {
            "u8" => (IntWidth::I8, IntSignedness::Unsigned),
            "s8" => (IntWidth::I8, IntSignedness::Signed),
            "u16" => (IntWidth::I16, IntSignedness::Unsigned),
            "s16" => (IntWidth::I16, IntSignedness::Signed),
            "u32" => (IntWidth::I32, IntSignedness::Unsigned),
            "s32" => (IntWidth::I32, IntSignedness::Signed),
            "u64" => (IntWidth::I64, IntSignedness::Unsigned),
            "s64" => (IntWidth::I64, IntSignedness::Signed),

            _ => {
                Diagnostic::error(ident_token.location, "invalid integer type")
                    .attached(stores.diags, item_id);
                return Err(());
            }
        };

        // The user specified an unsigned type, but gave a negative literal.
        if is_signed_kind == IntSignedness::Unsigned && is_known_negative {
            Diagnostic::error(
                ident_token.location,
                "signed integer literal with unsigned type kind",
            )
            .attached(stores.diags, item_id);
            return Err(());
        }

        let int_value = match is_signed_kind {
            IntSignedness::Signed => {
                // FIXME: Need to check bounds before cast
                let value: i64 = literal_value as i64;
                let value = if is_known_negative { -value } else { value };

                if !width.bounds_signed().contains(&value) {
                    Diagnostic::error(token.location, "literal out of bounds")
                        .primary_label_message(format!(
                            "valid range for {} is {:?}",
                            width.name(is_signed_kind),
                            width.bounds_signed(),
                        ))
                        .attached(stores.diags, item_id);
                    return Err(());
                }
                Integer::Signed(value)
            }
            IntSignedness::Unsigned => {
                if !width.bounds_unsigned().contains(&literal_value) {
                    Diagnostic::error(token.location, "Literal out of bounds")
                        .primary_label_message(format!(
                            "valid range for {} is {:?}",
                            width.name(is_signed_kind),
                            width.bounds_unsigned(),
                        ))
                        .attached(stores.diags, item_id);
                    return Err(());
                }
                Integer::Unsigned(literal_value)
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

        (width, Integer::Signed(literal_value))
    } else {
        let sizes = [IntWidth::I8, IntWidth::I16, IntWidth::I32, IntWidth::I64];
        let mut width = IntWidth::I64;

        for size in sizes {
            if size.bounds_unsigned().contains(&literal_value) {
                width = size;
                break;
            }
        }

        (width, Integer::Unsigned(literal_value))
    };

    // Return down here so that we consume any given parameters.
    if had_error.into_err() {
        return Err(());
    }

    Ok((
        OpCode::Basic(Basic::PushInt { width, value }),
        overall_location,
    ))
}

fn parse_float_op(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
    is_known_negative: bool,
) -> ParseOpResult {
    let mut had_error = ErrorSignal::new();
    let mut overall_location = token.location;
    let literal_value: f64 = match parse_float_lexeme(stores, item_id, token) {
        Ok(lit) => lit,
        Err(_) => {
            had_error.set();
            0.0
        }
    };

    let value = if is_known_negative {
        -literal_value
    } else {
        literal_value
    };

    let width = if token_iter.next_is_group(BracketKind::Paren) {
        let delim = token_iter
            .expect_group(stores, item_id, BracketKind::Paren, token)
            .with_kinds(stores, item_id, TokenKind::Ident)
            .with_length(stores, item_id, 1)?;

        let ident_token = delim.tokens[0].unwrap_single();
        overall_location = overall_location.merge(delim.last_token().location);

        match stores.strings.resolve(ident_token.inner.lexeme) {
            "f32" => FloatWidth::F32,
            "f64" => FloatWidth::F64,

            _ => {
                Diagnostic::error(ident_token.location, "invalid float type")
                    .attached(stores.diags, item_id);
                return Err(());
            }
        }
    } else if FloatWidth::F32.bounds().contains(&value) {
        FloatWidth::F32
    } else {
        FloatWidth::F64
    };

    if !width.bounds().contains(&value) {
        Diagnostic::error(token.location, "literal out of bounds")
            .primary_label_message(format!(
                "valid range for {} is {:?}",
                width.name(),
                width.bounds(),
            ))
            .attached(stores.diags, item_id);
        return Err(());
    }

    // Return down here so that we consume any given parameters.
    if had_error.into_err() {
        return Err(());
    }

    Ok((
        OpCode::Basic(Basic::PushFloat {
            width,
            value: Float(value),
        }),
        overall_location,
    ))
}

pub fn parse_drop_dup_over_reverse_swap_syscall(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    let (count, op_end) = if token_iter.next_is_group(BracketKind::Paren) {
        parse_integer_param(stores, token_iter, item_id, token)?
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
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    let delim = token_iter
        .expect_group(stores, item_id, BracketKind::Paren, token)
        .with_kinds(stores, item_id, Matcher("integer literal", integer_tokens))
        .with_length(stores, item_id, 1)?;

    let count_token = delim.tokens[0].unwrap_single();
    let count = parse_integer_lexeme(stores, item_id, count_token)?;

    Ok((
        OpCode::Basic(Basic::Memory(Memory::PackArray { count })),
        delim.last_token().location,
    ))
}

pub fn parse_cond(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> ParseOpResult {
    let arm_tokens = token_iter.expect_group(stores, item_id, BracketKind::Brace, keyword)?;

    let mut arm_token_iter = TokenIter::new(arm_tokens.tokens.iter());
    let mut close_token = arm_tokens.first_token();
    let mut arms = Vec::new();
    let mut else_block_ops = Vec::new();
    let mut else_close = close_token.location;
    let mut had_else_block = false;

    while arm_token_iter.peek().is_some() {
        if arm_token_iter.next_is(TokenKind::Else) {
            let else_token = arm_token_iter.next().unwrap_single();
            let else_block =
                arm_token_iter.expect_group(stores, item_id, BracketKind::Brace, else_token)?;
            close_token = else_block.last_token();
            else_block_ops = parse_item_body_contents(
                stores,
                &mut TokenIter::new(else_block.tokens.iter()),
                parent_id,
            )?;
            else_close = else_block.last_token().location;
            had_else_block = true;

            break;
        }

        let condition_tokens = get_terminated_tokens(
            stores,
            &mut arm_token_iter,
            item_id,
            close_token,
            None,
            Matcher("any", |_: &TokenTree| IsMatch::Yes),
            ConditionMatch,
            false,
        )?;
        let condition = parse_item_body_contents(
            stores,
            &mut TokenIter::new(condition_tokens.list.iter()),
            parent_id,
        )?;
        let condition = stores.blocks.new_block(condition);

        let then_block_tokens = arm_token_iter.expect_group(
            stores,
            item_id,
            BracketKind::Brace,
            condition_tokens.close,
        )?;
        close_token = then_block_tokens.last_token();

        let then_block = parse_item_body_contents(
            stores,
            &mut TokenIter::new(then_block_tokens.tokens.iter()),
            parent_id,
        )?;
        let then_block = stores.blocks.new_block(then_block);

        arms.push(CondArm {
            condition,
            open: then_block_tokens.open.location,
            block: then_block,
            close: then_block_tokens.last_token().location,
        })
    }

    if had_else_block && arm_token_iter.peek().is_some() {
        let first_loc = arm_token_iter.next().unwrap().first_token();
        let mut last_loc = first_loc;
        while let Some(next) = arm_token_iter.next() {
            last_loc = next.last_token();
        }

        let location = first_loc.location.merge(last_loc.location);

        Diagnostic::error(location, "`else` must be the last arm in a cond")
            .primary_label_message("here")
            .attached(stores.diags, item_id);
        return Err(());
    }

    let else_block = stores.blocks.new_block(else_block_ops);

    let cond_code = Cond {
        token: keyword.location,
        arms,
        implicit_else: !had_else_block,
        else_block,
        else_close,
    };

    Ok((
        OpCode::Basic(Basic::Control(Control::Cond(cond_code))),
        close_token.location,
    ))
}

pub fn parse_while(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> ParseOpResult {
    let condition_tokens = get_terminated_tokens(
        stores,
        token_iter,
        item_id,
        keyword,
        None,
        Matcher("any", |_: &TokenTree| IsMatch::Yes),
        ConditionMatch,
        false,
    )?;

    let condition = parse_item_body_contents(
        stores,
        &mut TokenIter::new(condition_tokens.list.iter()),
        parent_id,
    )?;
    let condition = stores.blocks.new_block(condition);

    let body_tokens =
        token_iter.expect_group(stores, item_id, BracketKind::Brace, condition_tokens.close)?;

    let body_block = parse_item_body_contents(
        stores,
        &mut TokenIter::new(body_tokens.tokens.iter()),
        parent_id,
    )?;
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

pub fn parse_field_access(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    let ident = token_iter.expect_single(stores, item_id, TokenKind::Ident, token.location)?;

    Ok((
        OpCode::Basic(Basic::Memory(Memory::FieldAccess {
            field_name: ident.map(|t| t.lexeme),
        })),
        ident.location,
    ))
}

pub fn parse_function_pointer(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
) -> ParseOpResult {
    let mut had_error = ErrorSignal::new();
    let first_ident = token_iter.expect_single(stores, item_id, IdentPathMatch, token.location)?;
    let (ident, span) = parse_ident(stores, &mut had_error, item_id, token_iter, first_ident)?;

    if had_error.into_err() {
        Err(())
    } else {
        Ok((
            OpCode::Complex(UnresolvedOp::FunctionPointer(ident)),
            token.location.merge(span.location),
        ))
    }
}
