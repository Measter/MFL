use std::{collections::VecDeque, ops::Not};

use ariadne::{Color, Label};
use tracing::debug_span;
use utils::TokenIter;

use crate::{
    context::Context,
    diagnostics,
    error_signal::ErrorSignal,
    lexer::{BracketKind, TokenKind, TokenTree},
    program::ModuleQueueType,
    stores::{
        ops::OpId,
        source::{SourceLocation, WithSpan},
    },
    ItemId, Stores,
};

use self::{
    ops::{parse_extract_insert_array, parse_extract_insert_struct, parse_simple_op},
    utils::Recover,
};

mod items;
mod ops;
mod utils;

pub fn parse_item_body_contents(
    ctx: &mut Context,
    stores: &mut Stores,
    tokens: &[TokenTree],
    parent_id: ItemId,
) -> Result<Vec<OpId>, ()> {
    let mut ops = Vec::new();
    let mut had_error = ErrorSignal::new();

    let mut token_iter = TokenIter::new(tokens.iter());
    while let Some(tree_item) = token_iter.next() {
        match tree_item {
            TokenTree::Single(token) => {
                let (kind, op_end) = match token.inner.kind {
                    TokenKind::Extract { .. } | TokenKind::Insert { .. } => {
                        // if token_iter
                        //     .peek()
                        //     .is_some_and(|tk| tk.inner.kind == TokenKind::ParenthesisOpen)
                        if token_iter.next_is_group(BracketKind::Paren) {
                            let new_ops =
                                parse_extract_insert_struct(stores, &mut token_iter, *token)?;
                            ops.extend(new_ops);
                            continue;
                        }
                        parse_extract_insert_array(*token)
                    }
                    TokenKind::While => {
                        let Ok(code) =
                            ops::parse_while(ctx, stores, &mut token_iter, *token, parent_id)
                        else {
                            had_error.set();
                            continue;
                        };
                        code
                    }
                    TokenKind::If => {
                        let Ok(code) =
                            ops::parse_if(ctx, stores, &mut token_iter, *token, parent_id)
                        else {
                            had_error.set();
                            continue;
                        };
                        code
                    }

                    TokenKind::Assert => {
                        if items::parse_assert(ctx, stores, &mut token_iter, *token, parent_id)
                            .is_err()
                        {
                            had_error.set();
                        }

                        continue;
                    }
                    TokenKind::Const => {
                        if items::parse_const(ctx, stores, &mut token_iter, *token, parent_id)
                            .is_err()
                        {
                            had_error.set();
                        }
                        continue;
                    }
                    TokenKind::Memory => {
                        if items::parse_memory(ctx, stores, &mut token_iter, *token, parent_id)
                            .is_err()
                        {
                            had_error.set();
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
                        had_error.set();
                        continue;
                    }

                    // These are only used as sub-part of some syntax, not standalone. If they're found anywhere else,
                    // it's an error.
                    TokenKind::GoesTo
                    | TokenKind::Import
                    | TokenKind::Dot
                    | TokenKind::Elif
                    | TokenKind::Else
                    | TokenKind::BracketClose(_)
                    | TokenKind::BracketOpen(_) => {
                        diagnostics::emit_error(
                            stores,
                            token.location,
                            format!(
                                "unexpected token `{}` in input",
                                stores.strings.resolve(token.inner.lexeme)
                            ),
                            Some(Label::new(token.location).with_color(Color::Red)),
                            None,
                        );

                        return Err(());
                    }

                    _ => parse_simple_op(stores, &mut token_iter, *token)?,
                };

                let token = token.inner.lexeme.with_span(token.location.merge(op_end));
                ops.push(stores.ops.new_op(kind, token));
            }
            TokenTree::Group(tg) => {
                diagnostics::emit_error(
                    stores,
                    tg.span(),
                    "unexpected bracket group in input",
                    Some(Label::new(tg.span()).with_color(Color::Red)),
                    None,
                );

                had_error.set();
                continue;
            }
        };
    }

    had_error.into_bool().not().then_some(ops).ok_or(())
}

pub(super) fn parse_file(
    ctx: &mut Context,
    stores: &mut Stores,
    module_id: ItemId,
    tokens: &[TokenTree],
    include_queue: &mut VecDeque<(ModuleQueueType, Option<ItemId>)>,
) -> Result<(), ()> {
    let _span = debug_span!(stringify!(parser::parse_module)).entered();

    let mut had_error = ErrorSignal::new();
    let mut token_iter = TokenIter::new(tokens.iter());

    while let Some(tree_item) = token_iter.next() {
        match tree_item {
            TokenTree::Single(token) => {
                match token.inner.kind {
                    TokenKind::Assert => {
                        if items::parse_assert(ctx, stores, &mut token_iter, *token, module_id)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    TokenKind::Const => {
                        if items::parse_const(ctx, stores, &mut token_iter, *token, module_id)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    TokenKind::Proc => {
                        if items::parse_function(ctx, stores, &mut token_iter, *token, module_id)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    TokenKind::Memory => {
                        if items::parse_memory(ctx, stores, &mut token_iter, *token, module_id)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    TokenKind::Import => {
                        let res = items::parse_import(
                            ctx,
                            stores,
                            &mut had_error,
                            &mut token_iter,
                            *token,
                            module_id,
                        )
                        .is_err();

                        if res {
                            had_error.set();
                        }
                    }

                    TokenKind::Module => {
                        if items::parse_module(
                            stores,
                            &mut token_iter,
                            include_queue,
                            *token,
                            module_id,
                        )
                        .is_err()
                        {
                            had_error.set();
                        }
                    }

                    TokenKind::Struct | TokenKind::Union => {
                        if items::parse_struct_or_union(
                            ctx,
                            stores,
                            &mut token_iter,
                            module_id,
                            *token,
                        )
                        .is_err()
                        {
                            had_error.set();
                        }
                    }

                    TokenKind::Extract { .. }
                    | TokenKind::Insert { .. }
                    | TokenKind::If
                    | TokenKind::While => {
                        emit_top_level_op_error(stores, token.location, token.inner.kind);
                        had_error.set();
                        continue;
                    }

                    // These are only used as sub-part of some syntax, not standalone. If they're found anywhere else,
                    // it's an error.
                    TokenKind::GoesTo
                    | TokenKind::Dot
                    | TokenKind::Elif
                    | TokenKind::Else
                    | TokenKind::BracketOpen(_)
                    | TokenKind::BracketClose(_) => {
                        diagnostics::emit_error(
                            stores,
                            token.location,
                            format!(
                                "unexpected token `{}` in input",
                                stores.strings.resolve(token.inner.lexeme)
                            ),
                            Some(Label::new(token.location).with_color(Color::Red)),
                            None,
                        );

                        had_error.set();
                        continue;
                    }

                    // These are invalid in top level position, but we should properly parse them anyway.
                    _ => {
                        let location = if let Ok((_, loc)) =
                            parse_simple_op(stores, &mut token_iter, *token)
                        {
                            token.location.merge(loc)
                        } else {
                            token.location
                        };
                        emit_top_level_op_error(stores, location, token.inner.kind);

                        had_error.set();
                        continue;
                    }
                }
            }
            TokenTree::Group(tg) => {
                diagnostics::emit_error(
                    stores,
                    tg.span(),
                    "unexpected bracket group in input",
                    Some(Label::new(tg.span()).with_color(Color::Red)),
                    None,
                );

                had_error.set();
                continue;
            }
        }
    }

    had_error.into_bool().not().then_some(()).ok_or(())
}

fn emit_top_level_op_error(stores: &Stores, location: SourceLocation, kind: TokenKind) {
    diagnostics::emit_error(
        stores,
        location,
        format!("top-level can only declared `assert` `const` `import` `memory` `module` `proc` or `struct`, found `{}`", kind.kind_str()),
        Some(Label::new(location).with_color(Color::Red)),
        None,
    );
}
