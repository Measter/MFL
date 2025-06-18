use std::{collections::VecDeque, ops::Not};

use lexer::{BracketKind, Token};
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
                let (kind, op_end) = match token.inner {
                    Token::Extract { .. } | Token::Insert { .. } => {
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
                    Token::While => {
                        let Ok(code) =
                            ops::parse_while(stores, token_iter, parent_id, *token, parent_id)
                        else {
                            had_error.set();
                            continue;
                        };
                        code
                    }
                    Token::Cond => {
                        let Ok(code) =
                            ops::parse_cond(stores, token_iter, parent_id, *token, parent_id)
                        else {
                            had_error.set();
                            continue;
                        };
                        code
                    }

                    Token::Assert => {
                        if items::parse_assert(stores, token_iter, *token, parent_id).is_err() {
                            had_error.set();
                        }

                        continue;
                    }
                    Token::Const => {
                        if items::parse_const(stores, token_iter, *token, parent_id).is_err() {
                            had_error.set();
                        }
                        continue;
                    }
                    Token::Variable => {
                        if items::parse_variable(stores, token_iter, *token, parent_id).is_err() {
                            had_error.set();
                        }
                        continue;
                    }
                    Token::Module | Token::Proc | Token::Struct | Token::Union => {
                        Diagnostic::error(
                            token.location,
                            format!("cannot use `{:?}` inside a procedure", token.inner),
                        )
                        .primary_label_message("here")
                        .attached(stores.diags, parent_id);

                        had_error.set();
                        continue;
                    }
                    Token::Dot => {
                        let Ok(op) = ops::parse_field_access(stores, token_iter, parent_id, *token)
                        else {
                            had_error.set();
                            continue;
                        };
                        op
                    }
                    Token::Colon => {
                        let Ok(op) = ops::parse_method_call(stores, token_iter, parent_id, *token)
                        else {
                            had_error.set();
                            continue;
                        };
                        op
                    }
                    Token::Carat => {
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
                    Token::GoesTo
                    | Token::Import
                    | Token::Else
                    | Token::BracketClose(_)
                    | Token::BracketOpen(_) => {
                        Diagnostic::error(
                            token.location,
                            format!("unexpected token `{}` in input", token.inner.kind_str()),
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

                ops.push(stores.ops.new_op(kind, token.location.merge(op_end)));
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
                match token.inner {
                    Token::Assert => {
                        if items::parse_assert(stores, &mut token_iter, *token, module_id).is_err()
                        {
                            had_error.set();
                        }
                    }

                    Token::Const => {
                        if items::parse_const(stores, &mut token_iter, *token, module_id).is_err() {
                            had_error.set();
                        }
                    }

                    Token::Proc => {
                        if items::parse_function(stores, &mut token_iter, *token, module_id)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    Token::Variable => {
                        if items::parse_variable(stores, &mut token_iter, *token, module_id)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    Token::Import => {
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

                    Token::Module => {
                        let module_ident = token_iter.expect_single(
                            stores,
                            module_id,
                            Token::Ident,
                            token.location,
                        )?;

                        let module_lexeme = stores.get_lexeme(module_ident.location);

                        if token_iter.next_is_group(BracketKind::Brace) {
                            let new_module_id = stores.items.new_module(
                                stores.sigs,
                                module_lexeme,
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
                                ModuleQueueType::Include(module_lexeme),
                                Some(module_id),
                            ));
                        }
                    }

                    Token::Struct | Token::Union => {
                        if items::parse_struct_or_union(stores, &mut token_iter, module_id, *token)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    Token::Enum => {
                        if items::parse_enum(stores, &mut token_iter, module_id, *token).is_err() {
                            had_error.set();
                        }
                    }

                    Token::Extract { .. } | Token::Insert { .. } | Token::Cond | Token::While => {
                        Diagnostic::bad_top_level_op(
                            stores.diags,
                            module_id,
                            token.location,
                            token.inner,
                        );
                        had_error.set();
                        continue;
                    }

                    Token::Dot => {
                        if ops::parse_field_access(stores, &mut token_iter, module_id, *token)
                            .is_err()
                        {
                            had_error.set();
                        }
                    }

                    // These are only used as sub-part of some syntax, not standalone. If they're found anywhere else,
                    // it's an error.
                    Token::GoesTo
                    | Token::Else
                    | Token::BracketOpen(_)
                    | Token::BracketClose(_) => {
                        Diagnostic::error(
                            token.location,
                            format!("unexpected token `{}` in input", token.inner.kind_str()),
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
                            token.inner,
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
