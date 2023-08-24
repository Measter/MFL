use std::{collections::VecDeque, ops::Not};

use ariadne::{Color, Label};
use intcast::IntCast;
use tracing::debug_span;

use crate::{
    diagnostics,
    interners::Interner,
    lexer::{Token, TokenKind},
    opcode::{Direction, Op, OpCode, OpId},
    program::ModuleQueueType,
    source_file::{SourceLocation, SourceStorage, Spanned, WithSpan},
    ItemId, Program,
};

use self::{
    ops::parse_simple_op,
    utils::{expect_token, get_delimited_tokens, Delimited, Recover},
};

mod items;
mod ops;
mod utils;

pub fn parse_item_body_contents(
    program: &mut Program,
    tokens: &[Spanned<Token>],
    op_id_gen: &mut impl FnMut() -> OpId,
    interner: &mut Interner,
    parent_id: ItemId,
    source_store: &SourceStorage,
) -> Result<Vec<Op>, ()> {
    let mut ops = Vec::new();
    let mut had_error = false;

    let mut token_iter = tokens.iter().enumerate().peekable();
    while let Some((_, token)) = token_iter.next() {
        let mut token = *token;
        let (kind, op_end) = match token.inner.kind {
            TokenKind::Extract { .. } | TokenKind::Insert { .. } => {
                if token_iter
                    .peek()
                    .is_some_and(|(_, tk)| tk.inner.kind == TokenKind::ParenthesisOpen)
                {
                    let delim = get_delimited_tokens(
                        &mut token_iter,
                        token,
                        None,
                        ("(", |t| t == TokenKind::ParenthesisOpen),
                        ("ident", |t| t == TokenKind::Ident || t == TokenKind::Dot),
                        (")", |t| t == TokenKind::ParenthesisClosed),
                        interner,
                        source_store,
                    )?;

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
                        return Err(());
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
                            let [prev @ .., _] = idents.as_slice() else {
                                unreachable!()
                            };

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

                            let [first, prev @ ..] = idents.as_slice() else {
                                unreachable!()
                            };
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
                        TokenKind::Insert { emit_struct } => (
                            OpCode::InsertStruct {
                                emit_struct,
                                field_name: idents[0].map(|t| t.lexeme),
                            },
                            token.location,
                        ),
                        _ => unreachable!(),
                    }
                } else {
                    match token.inner.kind {
                        TokenKind::Extract { emit_struct } => (
                            OpCode::ExtractArray {
                                emit_array: emit_struct,
                            },
                            token.location,
                        ),
                        TokenKind::Insert { emit_struct } => (
                            OpCode::InsertArray {
                                emit_array: emit_struct,
                            },
                            token.location,
                        ),
                        _ => unreachable!(),
                    }
                }
            }
            TokenKind::While => {
                let Ok(code) = ops::parse_while(
                    program,
                    &mut token_iter,
                    token,
                    op_id_gen,
                    parent_id,
                    interner,
                    source_store,
                ) else {
                    had_error = true;
                    continue;
                };
                code
            }
            TokenKind::If => {
                let Ok(code) = ops::parse_if(
                    program,
                    &mut token_iter,
                    token,
                    op_id_gen,
                    parent_id,
                    interner,
                    source_store,
                ) else {
                    had_error = true;
                    continue;
                };
                code
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

            // These are only used as sub-part of some syntax, not standalone. If they're found anywhere else,
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
                        interner.resolve(token.inner.lexeme)
                    ),
                    Some(Label::new(token.location)),
                    None,
                    source_store,
                );

                return Err(());
            }

            _ => parse_simple_op(&mut token_iter, token, interner, source_store)?,
        };

        let token = token.inner.lexeme.with_span(token.location.merge(op_end));
        ops.push(Op::new(op_id_gen(), kind, token));
    }

    had_error.not().then_some(ops).ok_or(())
}

pub(super) fn parse_file(
    program: &mut Program,
    module_id: ItemId,
    tokens: &[Spanned<Token>],
    interner: &mut Interner,
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

            TokenKind::Extract { .. }
            | TokenKind::Insert { .. }
            | TokenKind::If
            | TokenKind::While => {
                emit_top_level_op_error(token.location, token.inner.kind, source_store);
                had_error = true;
                continue;
            }

            // These are only used as sub-part of some syntax, not standalone. If they're found anywhere else,
            // it's an error.
            TokenKind::GoesTo
            | TokenKind::Is
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
                        interner.resolve(token.inner.lexeme)
                    ),
                    Some(Label::new(token.location)),
                    None,
                    source_store,
                );

                had_error = true;
                continue;
            }

            // These are invalid in top level position, but we should properly parse them anyway.
            _ => {
                let location = if let Ok((_, loc)) =
                    parse_simple_op(&mut token_iter, *token, interner, source_store)
                {
                    token.location.merge(loc)
                } else {
                    token.location
                };
                emit_top_level_op_error(location, token.inner.kind, source_store);

                had_error = true;
                continue;
            }
        }
    }

    had_error.not().then_some(()).ok_or(())
}

fn emit_top_level_op_error(
    location: SourceLocation,
    kind: TokenKind,
    source_store: &SourceStorage,
) {
    diagnostics::emit_error(
        location,
        format!("top-level can only declared `assert` `const` `import` `memory` `module` `proc` or `struct`, found `{:?}`", kind),
        Some(Label::new(location).with_color(Color::Red)),
        None,
        source_store
    );
}
