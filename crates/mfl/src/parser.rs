use std::{collections::VecDeque, ops::Not};

use lexer::{BracketKind, TokenKind};
use stores::source::WithSpan;
use tracing::debug_span;
use utils::{TokenIter, TokenTreeOptionExt};

use crate::{
    error_signal::ErrorSignal,
    lexer::TokenTree,
    program::ModuleQueueType,
    stores::{diagnostics::Diagnostic, ops::OpId},
    ItemId, Stores,
};

use self::{
    ops::{parse_extract_insert_array, parse_extract_insert_struct, parse_simple_op},
    utils::Recover,
};

mod items;
mod matcher;
mod ops;
mod utils;

fn parse_item_body_contents(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    parent_id: ItemId,
) -> Result<Vec<OpId>, ()> {
    let mut ops = Vec::new();
    let mut had_error = ErrorSignal::new();

    while let Some(tree_item) = token_iter.next() {
        match tree_item {
            TokenTree::Single(token) => {
                let (kind, op_end) = match token.inner.kind {
                    TokenKind::Extract { .. } | TokenKind::Insert { .. } => {
                        if token_iter.next_is_group(BracketKind::Paren) {
                            let Ok(new_ops) =
                                parse_extract_insert_struct(stores, token_iter, parent_id, *token)
                            else {
                                had_error.set();
                                continue;
                            };
                            ops.extend(new_ops);
                            continue;
                        }
                        parse_extract_insert_array(*token)
                    }
                    TokenKind::While => {
                        let Ok(code) =
                            ops::parse_while(stores, token_iter, parent_id, *token, parent_id)
                        else {
                            had_error.set();
                            continue;
                        };
                        code
                    }
                    TokenKind::Cond => {
                        let Ok(code) =
                            ops::parse_cond(stores, token_iter, parent_id, *token, parent_id)
                        else {
                            had_error.set();
                            continue;
                        };
                        code
                    }

                    TokenKind::Assert => {
                        if items::parse_assert(stores, token_iter, *token, parent_id).is_err() {
                            had_error.set();
                        }

                        continue;
                    }
                    TokenKind::Const => {
                        if items::parse_const(stores, token_iter, *token, parent_id).is_err() {
                            had_error.set();
                        }
                        continue;
                    }
                    TokenKind::Variable => {
                        if items::parse_variable(stores, token_iter, *token, parent_id).is_err() {
                            had_error.set();
                        }
                        continue;
                    }
                    TokenKind::Module | TokenKind::Proc | TokenKind::Struct | TokenKind::Union => {
                        Diagnostic::error(
                            token.location,
                            format!("cannot use `{:?}` inside a procedure", token.inner.kind),
                        )
                        .primary_label_message("here")
                        .attached(stores.diags, parent_id);

                        had_error.set();
                        continue;
                    }
                    TokenKind::Dot => {
                        let Ok(op) = ops::parse_field_access(stores, token_iter, parent_id, *token)
                        else {
                            had_error.set();
                            continue;
                        };
                        op
                    }
                    TokenKind::Colon => {
                        let Ok(op) = ops::parse_method_call(stores, token_iter, parent_id, *token)
                        else {
                            had_error.set();
                            continue;
                        };
                        op
                    }
                    TokenKind::Carat => {
                        let Ok(op) =
                            ops::parse_function_pointer(stores, token_iter, parent_id, *token)
                        else {
                            had_error.set();
                            continue;
                        };
                        op
                    }
                    // These are only used as sub-part of some syntax, not standalone. If they're found anywhere else,
                    // it's an error.
                    TokenKind::GoesTo
                    | TokenKind::Import
                    | TokenKind::Else
                    | TokenKind::BracketClose(_)
                    | TokenKind::BracketOpen(_) => {
                        Diagnostic::error(
                            token.location,
                            format!(
                                "unexpected token `{}` in input",
                                token.inner.kind.kind_str()
                            ),
                        )
                        .attached(stores.diags, parent_id);
                        had_error.set();
                        continue;
                    }

                    _ => {
                        let Ok(op) = parse_simple_op(stores, token_iter, parent_id, *token) else {
                            had_error.set();
                            continue;
                        };
                        op
                    }
                };

                let token = token.inner.lexeme.with_span(token.location.merge(op_end));
                ops.push(stores.ops.new_op(kind, token));
            }
            TokenTree::Group(tg) => {
                Diagnostic::error(tg.span(), "unexpected bracket group in input")
                    .primary_label_message("here")
                    .attached(stores.diags, parent_id);

                had_error.set();
                continue;
            }
        };
    }

    had_error.into_err().not().then_some(ops).ok_or(())
}

pub(super) fn parse_module(
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
                        if items::parse_assert(stores, &mut token_iter, *token, module_id).is_err()
                        {
                            had_error.set();
                        }
                    }

                    TokenKind::Const => {
                        if items::parse_const(stores, &mut token_iter, *token, module_id).is_err() {
                            had_error.set();
                        }
                    }

                    TokenKind::Proc => {
                        if items::parse_function(stores, &mut token_iter, *token, module_id)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    TokenKind::Variable => {
                        if items::parse_variable(stores, &mut token_iter, *token, module_id)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    TokenKind::Import => {
                        let res = items::parse_import(
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
                        let module_ident = token_iter.expect_single(
                            stores,
                            module_id,
                            TokenKind::Ident,
                            token.location,
                        )?;

                        if token_iter.next_is_group(BracketKind::Brace) {
                            let new_module_id = stores.items.new_module(
                                stores.sigs,
                                module_ident.map(|t| t.lexeme),
                                Some(module_id),
                                false,
                            );

                            let sub_tokens = token_iter.next().unwrap_group();

                            if parse_module(
                                stores,
                                new_module_id,
                                &sub_tokens.tokens,
                                include_queue,
                            )
                            .is_err()
                            {
                                had_error.set();
                            }
                        } else {
                            include_queue.push_back((
                                ModuleQueueType::Include(module_ident.map(|t| t.lexeme)),
                                Some(module_id),
                            ));
                        }
                    }

                    TokenKind::Struct | TokenKind::Union => {
                        if items::parse_struct_or_union(stores, &mut token_iter, module_id, *token)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    TokenKind::Enum => {
                        if items::parse_enum(stores, &mut token_iter, module_id, *token).is_err() {
                            had_error.set();
                        }
                    }

                    TokenKind::Extract { .. }
                    | TokenKind::Insert { .. }
                    | TokenKind::Cond
                    | TokenKind::While => {
                        Diagnostic::bad_top_level_op(
                            stores.diags,
                            module_id,
                            token.location,
                            token.inner.kind,
                        );
                        had_error.set();
                        continue;
                    }

                    TokenKind::Dot => {
                        if ops::parse_field_access(stores, &mut token_iter, module_id, *token)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    // These are only used as sub-part of some syntax, not standalone. If they're found anywhere else,
                    // it's an error.
                    TokenKind::GoesTo
                    | TokenKind::Else
                    | TokenKind::BracketOpen(_)
                    | TokenKind::BracketClose(_) => {
                        Diagnostic::error(
                            token.location,
                            format!(
                                "unexpected token `{}` in input",
                                token.inner.kind.kind_str()
                            ),
                        )
                        .attached(stores.diags, module_id);

                        had_error.set();
                        continue;
                    }

                    // These are invalid in top level position, but we should properly parse them anyway.
                    _ => {
                        let location = if let Ok((_, loc)) =
                            parse_simple_op(stores, &mut token_iter, module_id, *token)
                        {
                            token.location.merge(loc)
                        } else {
                            token.location
                        };
                        Diagnostic::bad_top_level_op(
                            stores.diags,
                            module_id,
                            location,
                            token.inner.kind,
                        );

                        had_error.set();
                        continue;
                    }
                }
            }
            TokenTree::Group(tg) => {
                Diagnostic::error(tg.span(), "unexpected bracket group in input")
                    .primary_label_message("here")
                    .attached(stores.diags, module_id);

                had_error.set();
                continue;
            }
        }
    }

    had_error.into_err().not().then_some(()).ok_or(())
}
