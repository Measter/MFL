use std::{cell::Cell, fmt::Display, iter::Peekable, ops::Not, str::FromStr};

use ariadne::{Color, Label};
use intcast::IntCast;
use lasso::Spur;
use num_traits::{PrimInt, Unsigned};
use smallvec::SmallVec;
use tracing::debug_span;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{Token, TokenKind},
    opcode::{Direction, If, IntKind, Op, OpCode, OpId, UnresolvedType, While},
    source_file::SourceStorage,
};

use super::{
    type_store::{IntWidth, Signedness},
    ItemId, ItemKind, ItemSignatureUnresolved, ModuleId, Program,
};

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

fn expect_token<'a>(
    tokens: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    kind_str: &str,
    mut expected: impl FnMut(TokenKind) -> bool,
    prev: Token,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(usize, Token), ()> {
    match tokens.peek() {
        Some((_, ident)) if expected(ident.kind) => tokens.next().map(|(a, b)| (a, *b)).ok_or(()),
        Some((_, ident)) => {
            diagnostics::emit_error(
                ident.location,
                format!(
                    "expected `{}`, found `{}`",
                    kind_str,
                    interner.resolve_lexeme(ident.lexeme)
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
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    prev: Token,
    expected_len: Option<usize>,
    (open_delim_str, open_delim_fn): (&'static str, impl FnMut(TokenKind) -> bool),
    (token_str, mut token_fn): (&'static str, impl FnMut(TokenKind) -> bool),
    (close_delim_str, mut close_delim_fn): (&'static str, impl FnMut(TokenKind) -> bool),
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(Token, Vec<Token>, Token), ()> {
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

        if close_delim_fn(next_token.kind) {
            break; // The end of the list, so break the loop.
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
                if !close_delim_fn(next_token.kind) {
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
    prev: Token,
    tokens: Vec<Token>,
) -> Result<Vec<UnresolvedType>, ()> {
    let mut had_error = false;
    let mut types = Vec::new();
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
            continue;
        };

        let lexeme = interner.resolve_lexeme(ident.lexeme);
        if lexeme != "ptr" {
            types.push(UnresolvedType::NonPointer(ident));
            continue;
        }

        let paren_depth = Cell::new(0);
        let Ok((open_paren, ident_tokens, close_paren)) = parse_delimited_token_list(
            &mut token_iter,
            ident,
            None,
            ("(", |t| t == TokenKind::ParenthesisOpen),
            ("Ident", |t| {
                if t == TokenKind::Ident {
                    return true;
                }
                if t == TokenKind::ParenthesisOpen {
                    paren_depth.set(paren_depth.get() + 1);
                    return true;
                }
                if paren_depth.get() > 0 && t == TokenKind::ParenthesisClosed {
                    paren_depth.set(paren_depth.get() - 1);
                    return true;
                }

                false
            }),
            (")", |t| paren_depth.get() == 0 && t == TokenKind::ParenthesisClosed),
            interner,
            source_store,
        ) else {
            had_error = true;
            continue;
        };

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

        let unresolved_type = unresolved_types.pop().unwrap();
        types.push(UnresolvedType::Pointer(
            ident.location.merge(close_paren.location),
            Box::new(unresolved_type),
        ));
    }

    had_error.not().then_some(types).ok_or(())
}

fn parse_integer_lexeme<T>(
    int_token: Token,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<T, ()>
where
    T: PrimInt + Unsigned + FromStr + Display,
{
    let TokenKind::Integer(count) = int_token.kind else { panic!("ICE: called parse_integer_lexeme with a non-integer token") };
    let int = match interner.resolve_literal(count).parse() {
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
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    token: Token,
    stripped_spur: Spur,
    is_known_negative: bool,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<OpCode, ()> {
    let (kind_token, signedness_kind) = if matches!(token_iter.peek(), Some((_,tk)) if tk.kind == TokenKind::ParenthesisOpen)
    {
        let (_, ident_token, _) = parse_delimited_token_list(
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

        let is_signed_kind = match interner.resolve_lexeme(ident_token.lexeme) {
            "u8" | "u16" | "u32" | "u64" => Signedness::Unsigned,
            "s8" | "s16" | "s32" | "s64" => Signedness::Signed,

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
        (Some(ident_token), is_signed_kind)
    } else {
        (None, Signedness::Signed)
    };

    if signedness_kind == Signedness::Unsigned && is_known_negative {
        let kind_token = kind_token.unwrap();
        diagnostics::emit_error(
            kind_token.location,
            "signed integer literal with unsigned type kind",
            [Label::new(token.location).with_color(Color::Red)],
            None,
            source_store,
        );
        return Err(());
    }

    let width = match kind_token {
        Some(token) => match interner.resolve_lexeme(token.lexeme) {
            "u8" | "s8" => IntWidth::I8,
            "u16" | "s16" => IntWidth::I16,
            "u32" | "s32" => IntWidth::I32,
            "u64" | "s64" => IntWidth::I64,
            _ => unreachable!(),
        },
        None => IntWidth::I32,
    };

    let value = match signedness_kind {
        Signedness::Signed => {
            let value: i64 = interner.resolve_literal(stripped_spur).parse().unwrap();
            let value = if is_known_negative { -value } else { value };

            if !width.bounds_signed().contains(&value) {
                diagnostics::emit_error(
                    token.location,
                    "literal out of bounds",
                    [Label::new(token.location)
                        .with_color(Color::Red)
                        .with_message(format!(
                            "valid range for {} is {:?}",
                            width.name(signedness_kind),
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
            let value: u64 = interner.resolve_literal(stripped_spur).parse().unwrap();
            if !width.bounds_unsigned().contains(&value) {
                diagnostics::emit_error(
                    token.location,
                    "literal out of bounds",
                    [Label::new(token.location)
                        .with_color(Color::Red)
                        .with_message(format!(
                            "valid range for {} is {:?}",
                            width.name(signedness_kind),
                            width.bounds_unsigned(),
                        ))],
                    None,
                    source_store,
                );
                return Err(());
            }
            IntKind::Unsigned(value)
        }
    };

    Ok(OpCode::PushInt { width, value })
}

pub fn parse_item_body(
    program: &mut Program,
    module_id: ModuleId,
    tokens: &[Token],
    op_id_gen: &mut impl FnMut() -> OpId,
    interner: &Interners,
    parent: Option<ItemId>,
    source_store: &SourceStorage,
) -> Result<Vec<Op>, ()> {
    let mut ops = Vec::new();
    let mut had_error = false;

    let mut token_iter = tokens.iter().enumerate().peekable();
    while let Some((_, token)) = token_iter.next() {
        let kind = match token.kind {
            TokenKind::Drop
            | TokenKind::Dup
            | TokenKind::Over
            | TokenKind::Swap
            | TokenKind::SysCall => {
                let (count, count_token) = if matches!(token_iter.peek(), Some((_,tk)) if tk.kind == TokenKind::ParenthesisOpen)
                {
                    let Ok((_, count_token, _)) = parse_delimited_token_list(
                        &mut token_iter,
                        *token,
                        Some(1),
                        ("(", |t| t == TokenKind::ParenthesisOpen),
                        ("Integer", |t| matches!(t, TokenKind::Integer(_))),
                        (")", |t| t == TokenKind::ParenthesisClosed),
                        interner,
                        source_store,
                    ) else {
                        had_error = true;
                        continue;
                    };

                    let count_token = count_token[0];
                    let count = parse_integer_lexeme(count_token, interner, source_store)?;
                    (count, count_token)
                } else {
                    (1, *token)
                };

                match token.kind {
                    TokenKind::Drop => OpCode::Drop { count, count_token },
                    TokenKind::Dup => OpCode::Dup { count, count_token },
                    TokenKind::Over => OpCode::Over {
                        depth: count,
                        depth_token: count_token,
                    },
                    TokenKind::Swap => OpCode::Swap { count, count_token },
                    TokenKind::SysCall => OpCode::SysCall {
                        arg_count: count,
                        arg_count_token: count_token,
                    },

                    _ => unreachable!(),
                }
            }
            TokenKind::Rot => {
                let Ok((_, tokens, _)) = parse_delimited_token_list(&mut token_iter,
                    *token,
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

                let mut local_error = false;
                let [item_count_token, direction_token, shift_count_token] = &*tokens else { unreachable!() };
                let item_count_token = *item_count_token;
                let shift_count_token = *shift_count_token;

                let item_count = if !matches!(item_count_token.kind, TokenKind::Integer(_)) {
                    diagnostics::emit_error(
                        item_count_token.location,
                        format!(
                            "expected `integer`, found `{}`",
                            interner.resolve_lexeme(item_count_token.lexeme)
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

                let shift_count = if !matches!(shift_count_token.kind, TokenKind::Integer(_)) {
                    diagnostics::emit_error(
                        shift_count_token.location,
                        format!(
                            "expected `integer`, found `{}`",
                            interner.resolve_lexeme(shift_count_token.lexeme)
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

                let direction = match direction_token.kind {
                    TokenKind::Less => Direction::Left,
                    TokenKind::Greater => Direction::Right,
                    _ => {
                        diagnostics::emit_error(
                            direction_token.location,
                            format!(
                                "expected `<` or `>`, found `{}`",
                                interner.resolve_lexeme(direction_token.lexeme)
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
                    item_count,
                    direction,
                    shift_count,
                    item_count_token,
                    shift_count_token,
                }
            }

            TokenKind::Cast => {
                // God, it's hideous!
                let paren_depth = Cell::new(0);
                let Ok((open_paren, ident_tokens, close_paren)) = parse_delimited_token_list(
                    &mut token_iter,
                    *token,
                    None,
                    ("(", |t| t == TokenKind::ParenthesisOpen),
                    ("Ident", |t| {
                        if t == TokenKind::Ident {
                            return true;
                        }
                        if t == TokenKind::ParenthesisOpen {
                            paren_depth.set(paren_depth.get() + 1);
                            return true;
                        }
                        if paren_depth.get() > 0 && t == TokenKind::ParenthesisClosed {
                            paren_depth.set(paren_depth.get() - 1);
                            return true;
                        }

                        false
                    }),
                    (")", |t| paren_depth.get() == 0 && t == TokenKind::ParenthesisClosed),
                    interner,
                    source_store,
                ) else {
                    had_error = true;
                    continue;
                };
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

                let unresolved_type = unresolved_types.pop().unwrap();

                OpCode::UnresolvedCast { unresolved_type }
            }

            TokenKind::Load => OpCode::Load,
            TokenKind::Store => OpCode::Store,

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
                let (module, item_token) = if matches!(token_iter.peek(), Some((_, t)) if t.kind == TokenKind::ColonColon)
                {
                    let (_, colons) = token_iter.next().unwrap(); // Consume the ColonColon.
                    let expected = expect_token(
                        &mut token_iter,
                        "ident",
                        |k| k == TokenKind::Ident,
                        *colons,
                        interner,
                        source_store,
                    )
                    .ok()
                    .map(|(_, t)| t);

                    let item_id = if let Some(t) = expected {
                        t
                    } else {
                        had_error = true;
                        continue;
                    };

                    (Some(*token), item_id)
                } else {
                    (None, *token)
                };

                OpCode::UnresolvedIdent {
                    module,
                    item: item_token,
                }
            }
            TokenKind::Integer(id) => {
                let Ok(int) = parse_integer_op(&mut token_iter, *token, id, false, interner, source_store) else {
                    had_error = true;
                    continue;
                };

                int
            }
            TokenKind::String { id, is_c_str } => OpCode::PushStr { id, is_c_str },
            TokenKind::Here(id) => OpCode::PushStr {
                id,
                is_c_str: false,
            },
            TokenKind::ArgC => OpCode::ArgC,
            TokenKind::ArgV => OpCode::ArgV,

            TokenKind::While => {
                match parse_while(
                    program,
                    module_id,
                    &mut token_iter,
                    tokens,
                    *token,
                    op_id_gen,
                    parent,
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

            TokenKind::Assert | TokenKind::Const | TokenKind::Memory => {
                if parse_item(
                    program,
                    module_id,
                    &mut token_iter,
                    tokens,
                    *token,
                    interner,
                    parent,
                    source_store,
                )
                .is_err()
                {
                    had_error = true;
                }
                continue;
            }
            TokenKind::Include | TokenKind::Macro | TokenKind::Proc => {
                diagnostics::emit_error(
                    token.location,
                    format!("cannot use `{:?}` inside a procedure", token.kind),
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
                    module_id,
                    &mut token_iter,
                    tokens,
                    *token,
                    op_id_gen,
                    parent,
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
                        && matches!(int_token.kind, TokenKind::Integer(_)) =>
                {
                    token_iter.next();
                    let mut int_token = *int_token;
                    int_token.location = int_token.location.merge(token.location);
                    let TokenKind::Integer(id) = int_token.kind else { unreachable!() };
                    let Ok(int) = parse_integer_op(&mut token_iter, int_token, id, true, interner, source_store) else {
                        had_error = true;
                        continue;
                    };

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
            TokenKind::ShiftLeft => OpCode::ShiftLeft,
            TokenKind::ShiftRight => OpCode::ShiftRight,

            TokenKind::Return => OpCode::Return,

            // These are only used as part of a sub-block. If they're found anywhere else,
            // it's an error.
            TokenKind::ColonColon
            | TokenKind::GoesTo
            | TokenKind::Is
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
                        interner.resolve_lexeme(token.lexeme)
                    ),
                    Some(Label::new(token.location)),
                    None,
                    source_store,
                );

                had_error = true;
                continue;
            }
        };

        ops.push(Op::new(op_id_gen(), kind, *token));
    }

    had_error.not().then_some(ops).ok_or(())
}

fn get_item_body<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    mut last_token: Token,
    target_token_type: fn(TokenKind) -> bool,
    source_store: &SourceStorage,
) -> Result<(&'a [Token], Token), ()> {
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
        let is_nested_err = match (keyword.kind, token.kind) {
            (Proc, Include | Proc | Macro) => true,
            (Memory | Const, Proc | Macro | Const | Memory | Include) => true,
            _ => false,
        };

        if is_nested_err {
            diagnostics::emit_error(
                token.location,
                format!("cannot use {:?} inside a {:?}", token.kind, keyword.kind),
                Some(Label::new(token.location).with_color(Color::Red)),
                None,
                source_store,
            );
            had_error = true;
        }

        // If the block_depth is greater than 1, it means we're in a sub-block. All sub-blocks
        // will always close with an End token, so if we are in a sub-block only look for End.
        if token.kind.new_block() {
            block_depth += 1;
        } else if (block_depth > 1 && token.kind == TokenKind::End)
            || (block_depth == 1 && target_token_type(token.kind))
        {
            block_depth -= 1;
        }

        end_idx = idx;
        last_token = *token;

        if block_depth == 0 {
            break;
        }
    }

    if !target_token_type(last_token.kind) {
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
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent: Option<ItemId>,
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
        module_id,
        condition,
        op_id_gen,
        interner,
        parent,
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
        module_id,
        main_block,
        op_id_gen,
        interner,
        parent,
        source_store,
    )?;

    let else_token = close_token;
    let mut elif_blocks = Vec::new();

    while close_token.kind == TokenKind::Elif {
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
            module_id,
            elif_condition,
            op_id_gen,
            interner,
            parent,
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
            module_id,
            elif_block,
            op_id_gen,
            interner,
            parent,
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

    let mut else_block = if close_token.kind == TokenKind::Else {
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
            module_id,
            else_block,
            op_id_gen,
            interner,
            parent,
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
                open_token,
                condition,
                do_token,
                then_block,
                else_token,
                else_block,
                end_token: close_token,
            })),
            open_token,
        );

        else_block = vec![if_op];
    }

    Ok(OpCode::If(Box::new(If {
        open_token: keyword,
        condition,
        do_token,
        then_block,
        else_token,
        else_block,
        end_token: close_token,
    })))
}

fn parse_while<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent: Option<ItemId>,
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
        module_id,
        condition,
        op_id_gen,
        interner,
        parent,
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

    let body_block = parse_item_body(
        program,
        module_id,
        body,
        op_id_gen,
        interner,
        parent,
        source_store,
    )?;

    Ok(OpCode::While(Box::new(While {
        do_token,
        condition,
        body_block,
        end_token,
    })))
}

fn parse_function_header<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: Option<ItemId>,
    source_store: &SourceStorage,
) -> Result<(Token, ItemId), ()> {
    let mut had_error = false;
    let (entry_stack_start, entry_tokens, entry_stack_end) = parse_delimited_token_list(
        token_iter,
        name,
        None,
        ("[", |t| t == TokenKind::SquareBracketOpen),
        ("Ident", |t| {
            matches!(
                t,
                TokenKind::Ident | TokenKind::ParenthesisOpen | TokenKind::ParenthesisClosed
            )
        }),
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
        ("Ident", |t| {
            matches!(
                t,
                TokenKind::Ident | TokenKind::ParenthesisOpen | TokenKind::ParenthesisClosed
            )
        }),
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
        exit_stack: unresolved_exit_types,
        exit_stack_location,
        entry_stack: unresolved_entry_types,
        entry_stack_location,
        memory_type: None,
        memory_type_location: name.location,
    };

    let new_item = program.new_item(name, module_id, ItemKind::Function, parent, sig);

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

fn parse_memory_header<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: Option<ItemId>,
    source_store: &SourceStorage,
) -> Result<(Token, ItemId), ()> {
    let mut had_error = false;
    let (store_type_start, store_type_tokens, store_type_end) = parse_delimited_token_list(
        token_iter,
        name,
        None,
        ("[", |t| t == TokenKind::SquareBracketOpen),
        ("Ident", |t| {
            matches!(
                t,
                TokenKind::Ident | TokenKind::ParenthesisOpen | TokenKind::ParenthesisClosed
            )
        }),
        ("]", |t| t == TokenKind::SquareBracketClosed),
        interner,
        source_store,
    )
    .recover(&mut had_error, (name, Vec::new(), name));
    let store_type_location = store_type_start.location.merge(store_type_end.location);
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
        exit_stack: Vec::new(),
        exit_stack_location: name.location,
        entry_stack: Vec::new(),
        entry_stack_location: name.location,
        memory_type: unresolved_store_type.pop(),
        memory_type_location: store_type_location,
    };

    let new_item = program.new_item(name, module_id, ItemKind::Memory, parent, sig);

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
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: Option<ItemId>,
    source_store: &SourceStorage,
) -> Result<(Token, ItemId), ()> {
    let sig = ItemSignatureUnresolved {
        exit_stack: Vec::new(),
        exit_stack_location: name.location,
        entry_stack: Vec::new(),
        entry_stack_location: name.location,
        memory_type: None,
        memory_type_location: name.location,
    };

    let new_item = program.new_item(name, module_id, ItemKind::Macro, parent, sig);

    let mut had_error = false;
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
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: Option<ItemId>,
    source_store: &SourceStorage,
) -> Result<(Token, ItemId), ()> {
    let mut had_error = false;
    let (exit_stack_start, exit_tokens, exit_stack_end) = parse_delimited_token_list(
        token_iter,
        name,
        None,
        ("[", |t| t == TokenKind::SquareBracketOpen),
        ("Ident", |t| {
            matches!(
                t,
                TokenKind::Ident | TokenKind::ParenthesisOpen | TokenKind::ParenthesisClosed
            )
        }),
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
        exit_stack: unresolved_exit_types,
        exit_stack_location,
        entry_stack: Vec::new(),
        entry_stack_location: name.location,
        memory_type: None,
        memory_type_location: name.location,
    };

    let new_item = program.new_item(name, module_id, ItemKind::Const, parent, sig);

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
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: Option<ItemId>,
    source_store: &SourceStorage,
) -> Result<(Token, ItemId), ()> {
    let sig = ItemSignatureUnresolved {
        exit_stack: vec![UnresolvedType::NonPointer(name)],
        exit_stack_location: name.location,
        entry_stack: Vec::new(),
        entry_stack_location: name.location,
        memory_type: None,
        memory_type_location: name.location,
    };

    let new_item = program.new_item(name, module_id, ItemKind::Assert, parent, sig);

    let mut had_error = false;
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
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    interner: &Interners,
    parent: Option<ItemId>,
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

    let header_func = match keyword.kind {
        TokenKind::Proc => parse_function_header,
        TokenKind::Memory => parse_memory_header,
        TokenKind::Macro => parse_macro_header,
        TokenKind::Const => parse_const_header,
        TokenKind::Assert => parse_assert_header,
        _ => unreachable!(),
    };

    let (is_token, item_id) = header_func(
        program,
        module_id,
        token_iter,
        interner,
        name_token,
        parent,
        source_store,
    )
    .recover(&mut had_error, (name_token, ItemId::dud()));

    let (body, end_token) = get_item_body(
        &mut *token_iter,
        tokens,
        keyword,
        is_token,
        |t| matches!(t, TokenKind::End),
        source_store,
    )
    .recover(&mut had_error, (&[], is_token));

    let mut op_id = 0;
    let mut op_id_gen = || {
        let id = op_id;
        op_id += 1;
        OpId(id)
    };

    let mut body = parse_item_body(
        program,
        module_id,
        body,
        &mut op_id_gen,
        interner,
        Some(item_id),
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
                token: name_token,
                expansions: SmallVec::new(),
            },
        );

        body.push(Op {
            code: OpCode::Epilogue,
            id: op_id_gen(),
            token: end_token,
            expansions: SmallVec::new(),
        });
    }

    item_header.new_op_id = op_id;
    program.set_item_body(item_id, body);

    // stupid borrow checker...
    let _ = item_header; // Need to discard the borrow;
    let item_header = program.get_item_header(item_id);

    if let Some(prev_def) = program
        .get_visible_symbol(item_header, name_token.lexeme)
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

    if let Some(parent_id) = parent {
        let parent_item = program.get_item_header(parent_id);
        match (parent_item.kind(), keyword.kind) {
            (ItemKind::Function, TokenKind::Const) => {
                let pd = program.get_function_data_mut(parent_id);
                pd.consts.insert(name_token.lexeme, item_id);
            }
            (ItemKind::Function, TokenKind::Memory) => {
                let pd = program.get_function_data_mut(parent_id);
                pd.allocs.insert(name_token.lexeme, item_id);
            }
            // The other types aren't stored in the proc
            _ => {}
        }
    }

    if had_error {
        Err(())
    } else {
        Ok(())
    }
}

pub(super) fn parse_module(
    program: &mut Program,
    module_id: ModuleId,
    tokens: &[Token],
    interner: &Interners,
    include_queue: &mut Vec<Token>,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let _span = debug_span!(stringify!(parser::parse_module)).entered();

    let mut had_error = false;
    let mut token_iter = tokens.iter().enumerate().peekable();

    while let Some((_, token)) = token_iter.next() {
        match token.kind {
            TokenKind::Assert
            | TokenKind::Const
            | TokenKind::Macro
            | TokenKind::Memory
            | TokenKind::Proc => {
                if parse_item(
                    program,
                    module_id,
                    &mut token_iter,
                    tokens,
                    *token,
                    interner,
                    None,
                    source_store,
                )
                .is_err()
                {
                    had_error = true;
                }
            }

            TokenKind::Include => {
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

                include_queue.push(module_ident);
            }

            _ => {
                diagnostics::emit_error(
                    token.location,
                    format!("top-level can only declared `const`, `include`, `macro` `memory` or `proc`, found `{:?}`", token.kind),
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
