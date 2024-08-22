use std::{collections::VecDeque, ops::Not};

use ariadne::{Color, Label};
use lexer::{BracketKind, TokenKind};
use stores::source::{SourceLocation, WithSpan};
use tracing::debug_span;
use utils::TokenIter;

use crate::{
    diagnostics, error_signal::ErrorSignal, lexer::TokenTree, program::ModuleQueueType,
    stores::ops::OpId, ItemId, Stores,
};

use self::{
    ops::{parse_extract_insert_array, parse_extract_insert_struct, parse_simple_op},
    utils::Recover,
};

mod items;
mod matcher;
mod ops;
mod utils;

pub fn parse_item_body_contents(
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
                        if token_iter.next_is_group(BracketKind::Paren) {
                            let Ok(new_ops) =
                                parse_extract_insert_struct(stores, &mut token_iter, *token)
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
                        let Ok(code) = ops::parse_while(stores, &mut token_iter, *token, parent_id)
                        else {
                            had_error.set();
                            continue;
                        };
                        code
                    }
                    TokenKind::If => {
                        let Ok(code) = ops::parse_if(stores, &mut token_iter, *token, parent_id)
                        else {
                            had_error.set();
                            continue;
                        };
                        code
                    }

                    TokenKind::Assert => {
                        if items::parse_assert(stores, &mut token_iter, *token, parent_id).is_err()
                        {
                            had_error.set();
                        }

                        continue;
                    }
                    TokenKind::Const => {
                        if items::parse_const(stores, &mut token_iter, *token, parent_id).is_err() {
                            had_error.set();
                        }
                        continue;
                    }
                    TokenKind::Variable => {
                        if items::parse_variable(stores, &mut token_iter, *token, parent_id)
                            .is_err()
                        {
                            had_error.set();
                        }
                        continue;
                    }
                    TokenKind::Module | TokenKind::Proc | TokenKind::Struct | TokenKind::Union => {
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
                    TokenKind::Dot => {
                        let Ok(op) = ops::parse_field_access(stores, &mut token_iter, *token)
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
                        diagnostics::emit_error(
                            stores,
                            token.location,
                            format!(
                                "unexpected token `{}` in input",
                                token.inner.kind.kind_str()
                            ),
                            Some(Label::new(token.location).with_color(Color::Red)),
                            None,
                        );
                        had_error.set();
                        continue;
                    }

                    _ => {
                        let Ok(op) = parse_simple_op(stores, &mut token_iter, *token) else {
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
                        if items::parse_struct_or_union(stores, &mut token_iter, module_id, *token)
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

                    TokenKind::Dot => {
                        if ops::parse_field_access(stores, &mut token_iter, *token).is_err() {
                            had_error.set();
                        }
                    }

                    // These are only used as sub-part of some syntax, not standalone. If they're found anywhere else,
                    // it's an error.
                    TokenKind::GoesTo
                    | TokenKind::Else
                    | TokenKind::BracketOpen(_)
                    | TokenKind::BracketClose(_) => {
                        diagnostics::emit_error(
                            stores,
                            token.location,
                            format!(
                                "unexpected token `{}` in input",
                                token.inner.kind.kind_str()
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
        format!("top-level can only declared `assert` `const` `import` `var` `module` `proc` or `struct`, found `{}`", kind.kind_str()),
        Some(Label::new(location).with_color(Color::Red)),
        None,
    );
}
