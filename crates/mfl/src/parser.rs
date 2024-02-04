use std::{collections::VecDeque, ops::Not};

use ariadne::{Color, Label};
use tracing::debug_span;

use crate::{
    context::Context,
    diagnostics,
    ir::{Op, OpId, UnresolvedOp},
    lexer::{Token, TokenKind},
    program::ModuleQueueType,
    source_file::{SourceLocation, Spanned, WithSpan},
    ItemId, Stores,
};

use self::{
    ops::{parse_extract_insert_array, parse_extract_insert_struct, parse_simple_op},
    utils::{expect_token, get_delimited_tokens, Delimited, Recover},
};

mod items;
mod ops;
mod utils;

pub fn parse_item_body_contents(
    ctx: &mut Context,
    stores: &mut Stores,
    tokens: &[Spanned<Token>],
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
) -> Result<Vec<Op<UnresolvedOp>>, ()> {
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
                    let new_ops =
                        parse_extract_insert_struct(stores, &mut token_iter, op_id_gen, token)?;
                    ops.extend(new_ops);
                    continue;
                } else {
                    parse_extract_insert_array(stores, &mut token_iter, token)?
                }
            }
            TokenKind::While => {
                let Ok(code) =
                    ops::parse_while(ctx, stores, &mut token_iter, token, op_id_gen, parent_id)
                else {
                    had_error = true;
                    continue;
                };
                code
            }
            TokenKind::If => {
                let Ok(code) =
                    ops::parse_if(ctx, stores, &mut token_iter, token, op_id_gen, parent_id)
                else {
                    had_error = true;
                    continue;
                };
                code
            }

            TokenKind::Assert => {
                had_error |=
                    items::parse_assert(ctx, stores, &mut token_iter, token, parent_id).is_err();

                continue;
            }
            TokenKind::Const => {
                if items::parse_const(ctx, stores, &mut token_iter, token, parent_id).is_err() {
                    had_error = true;
                }
                continue;
            }
            TokenKind::Memory => {
                if items::parse_memory(ctx, stores, &mut token_iter, token, parent_id).is_err() {
                    had_error = true;
                }
                continue;
            }
            TokenKind::Module
            | TokenKind::Proc
            | TokenKind::Field
            | TokenKind::Struct
            | TokenKind::Union => {
                diagnostics::emit_error(
                    stores,
                    token.location,
                    format!("cannot use `{:?}` inside a procedure", token.inner.kind),
                    Some(
                        Label::new(token.location)
                            .with_color(Color::Red)
                            .with_message("here"),
                    ),
                    None,
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
                    stores,
                    token.location,
                    format!(
                        "unexpected token `{}` in input",
                        stores.strings.resolve(token.inner.lexeme)
                    ),
                    Some(Label::new(token.location)),
                    None,
                );

                return Err(());
            }

            _ => parse_simple_op(stores, &mut token_iter, token)?,
        };

        let token = token.inner.lexeme.with_span(token.location.merge(op_end));
        ops.push(Op::new(op_id_gen(), kind, token));
    }

    had_error.not().then_some(ops).ok_or(())
}

pub(super) fn parse_file(
    ctx: &mut Context,
    stores: &mut Stores,
    module_id: ItemId,
    tokens: &[Spanned<Token>],
    include_queue: &mut VecDeque<(ModuleQueueType, Option<ItemId>)>,
) -> Result<(), ()> {
    let _span = debug_span!(stringify!(parser::parse_module)).entered();

    let mut had_error = false;
    let mut token_iter = tokens.iter().enumerate().peekable();

    while let Some((_, token)) = token_iter.next() {
        match token.inner.kind {
            TokenKind::Assert => {
                had_error |=
                    items::parse_assert(ctx, stores, &mut token_iter, *token, module_id).is_err();
            }

            TokenKind::Const => {
                had_error |=
                    items::parse_const(ctx, stores, &mut token_iter, *token, module_id).is_err();
            }

            TokenKind::Proc => {
                had_error |=
                    items::parse_function(ctx, stores, &mut token_iter, *token, module_id).is_err();
            }

            TokenKind::Memory => {
                had_error |=
                    items::parse_memory(ctx, stores, &mut token_iter, *token, module_id).is_err();
            }

            TokenKind::Import => {
                had_error |= items::parse_import(
                    ctx,
                    stores,
                    &mut had_error,
                    &mut token_iter,
                    *token,
                    module_id,
                )
                .is_err();
            }

            TokenKind::Module => {
                had_error |=
                    items::parse_module(stores, &mut token_iter, include_queue, *token, module_id)
                        .is_err();
            }

            TokenKind::Struct | TokenKind::Union => {
                had_error |=
                    items::parse_struct_or_union(ctx, stores, &mut token_iter, module_id, *token)
                        .is_err();
            }

            TokenKind::Extract { .. }
            | TokenKind::Insert { .. }
            | TokenKind::If
            | TokenKind::While => {
                emit_top_level_op_error(stores, token.location, token.inner.kind);
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
                    stores,
                    token.location,
                    format!(
                        "unexpected token `{}` in input",
                        stores.strings.resolve(token.inner.lexeme)
                    ),
                    Some(Label::new(token.location)),
                    None,
                );

                had_error = true;
                continue;
            }

            // These are invalid in top level position, but we should properly parse them anyway.
            _ => {
                let location =
                    if let Ok((_, loc)) = parse_simple_op(stores, &mut token_iter, *token) {
                        token.location.merge(loc)
                    } else {
                        token.location
                    };
                emit_top_level_op_error(stores, location, token.inner.kind);

                had_error = true;
                continue;
            }
        }
    }

    had_error.not().then_some(()).ok_or(())
}

fn emit_top_level_op_error(stores: &Stores, location: SourceLocation, kind: TokenKind) {
    diagnostics::emit_error(
        stores,
        location,
        format!("top-level can only declared `assert` `const` `import` `memory` `module` `proc` or `struct`, found `{:?}`", kind),
        Some(Label::new(location).with_color(Color::Red)),
        None,
    );
}
