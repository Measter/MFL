use std::collections::VecDeque;

use ariadne::{Color, Label};
use flagset::FlagSet;

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{Basic, Control, OpCode, StructDef, StructDefField},
    lexer::{BracketKind, Token, TokenKind, TokenTree, TreeGroup},
    program::ModuleQueueType,
    stores::{
        item::{ItemAttribute, ItemId, LangItem},
        ops::OpId,
        source::Spanned,
    },
    Stores,
};

use super::{
    parse_item_body_contents,
    utils::{
        get_terminated_tokens, parse_ident, parse_multiple_unresolved_types, parse_stack_def,
        valid_type_token, Matcher, Terminated, TokenIter, TreeGroupResultExt,
    },
    Recover,
};

struct ParsedAttributes {
    attributes: FlagSet<ItemAttribute>,
    lang_item: Option<LangItem>,
    last_token: Spanned<Token>,
}
impl ParsedAttributes {
    fn fallback(prev_token: Spanned<Token>) -> Self {
        Self {
            attributes: FlagSet::default(),
            lang_item: None,
            last_token: prev_token,
        }
    }
}

fn try_get_attributes(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    prev_token: Spanned<Token>,
) -> Result<ParsedAttributes, ()> {
    if !token_iter.next_is_group(BracketKind::Paren) {
        return Ok(ParsedAttributes {
            attributes: FlagSet::default(),
            lang_item: None,
            last_token: prev_token,
        });
    }

    let mut had_error = ErrorSignal::new();
    let fallback = TreeGroup::fallback(BracketKind::Paren, prev_token);
    let attribute_group = token_iter
        .expect_group(stores, BracketKind::Paren, prev_token)
        .with_kinds(
            stores,
            Matcher("attribute", |t: &TokenTree| match t {
                TokenTree::Single(tk) => matches!(
                    tk.inner.kind,
                    TokenKind::Extern | TokenKind::Ident | TokenKind::LangItem
                ),
                TokenTree::Group(g) => g.bracket_kind == BracketKind::Paren,
            }),
        )
        .recover(&mut had_error, &fallback);

    let mut attributes = FlagSet::default();
    let mut lang_item = None;

    let mut token_iter = TokenIter::new(attribute_group.tokens.iter());
    let mut prev_token = attribute_group.first_token();
    while let Some(token) = token_iter.next() {
        match token {
            TokenTree::Single(tk) => match tk.inner.kind {
                TokenKind::Extern => {
                    if attributes.contains(ItemAttribute::Extern) {
                        diagnostics::emit_warning(
                            stores,
                            tk.location,
                            "item already extern",
                            [Label::new(tk.location).with_color(Color::Red)],
                            None,
                        );
                    }

                    attributes |= ItemAttribute::Extern;
                    prev_token = *tk;
                }
                TokenKind::Ident => {
                    diagnostics::emit_error(
                        stores,
                        tk.location,
                        "unknown attribute",
                        [Label::new(tk.location).with_color(Color::Red)],
                        None,
                    );
                    had_error.set();
                }
                TokenKind::LangItem => {
                    let Ok(group) = token_iter
                        .expect_group(stores, BracketKind::Paren, prev_token)
                        .with_kinds(stores, TokenKind::Ident)
                        .with_length(stores, 1)
                    else {
                        // expect call already handled error.
                        continue;
                    };

                    let item_token = group.tokens[0].unwrap_single();
                    prev_token = group.last_token();

                    if let Some(prev_lang_item) = lang_item.replace(item_token.map(|t| t.lexeme)) {
                        diagnostics::emit_error(
                            stores,
                            item_token.location,
                            "multiple lang item attributes",
                            [
                                Label::new(item_token.location).with_color(Color::Red),
                                Label::new(prev_lang_item.location)
                                    .with_color(Color::Cyan)
                                    .with_message("previously set here"),
                            ],
                            None,
                        );
                        had_error.set();
                    }
                }
                _ => unreachable!(),
            },
            TokenTree::Group(tg) => {
                diagnostics::emit_error(
                    stores,
                    tg.span(),
                    "expected attribute, found bracket group",
                    [Label::new(tg.span()).with_color(Color::Red)],
                    None,
                );
                had_error.set()
            }
        }
    }

    let lang_item = lang_item.and_then(|li| {
        let string = stores.strings.resolve(li.inner);
        let Ok(lang_item) = LangItem::from_str(string) else {
            diagnostics::emit_error(
                stores,
                li.location,
                format!("Unknown lang item `{string}`"),
                [Label::new(li.location).with_color(Color::Red)],
                None,
            );
            had_error.set();
            return None;
        };
        Some(lang_item)
    });

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(ParsedAttributes {
            attributes,
            lang_item,
            last_token: attribute_group.last_token(),
        })
    }
}

fn parse_item_body(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut TokenIter,
    name_token: Spanned<Token>,
    parent_id: ItemId,
) -> Vec<OpId> {
    let fallback = TreeGroup::fallback(BracketKind::Brace, name_token);
    let delim = token_iter
        .expect_group(stores, BracketKind::Brace, name_token)
        .recover(had_error, &fallback);

    let mut body =
        parse_item_body_contents(stores, &delim.tokens, parent_id).recover(had_error, Vec::new());

    // Makes later logic easier if we always have a prologue and epilogue.
    body.insert(
        0,
        stores.ops.new_op(
            OpCode::Basic(Basic::Control(Control::Prologue)),
            delim.open.map(|t| t.lexeme),
        ),
    );
    body.push(stores.ops.new_op(
        OpCode::Basic(Basic::Control(Control::Epilogue)),
        delim.last_token().map(|t| t.lexeme),
    ));

    body
}

pub fn parse_function(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let attributes = try_get_attributes(stores, token_iter, keyword)
        .recover(&mut had_error, ParsedAttributes::fallback(keyword));

    let name_token = token_iter
        .expect_single(stores, TokenKind::Ident, attributes.last_token.location)
        .recover(&mut had_error, attributes.last_token);

    let fallback = TreeGroup::fallback(BracketKind::Paren, name_token);
    let generic_params = if token_iter.next_is_group(BracketKind::Paren) {
        token_iter
            .expect_group(stores, BracketKind::Paren, name_token)
            .with_kinds(stores, TokenKind::Ident)
            .recover(&mut had_error, &fallback)
    } else {
        &fallback
    };

    let entry_stack = parse_stack_def(stores, &mut had_error, token_iter, name_token);
    let entry_stack = entry_stack.map(|st| st.into_iter().collect());

    token_iter
        .expect_single(stores, TokenKind::GoesTo, name_token.location)
        .recover(&mut had_error, name_token);

    let exit_stack = parse_stack_def(stores, &mut had_error, token_iter, name_token);
    let exit_stack = exit_stack.map(|st| st.into_iter().collect());

    let has_body = token_iter.next_is_group(BracketKind::Brace);

    if !has_body {
        let (_, prev_def) = stores.items.new_function_decl(
            stores.sigs,
            &mut had_error,
            name_token.map(|t| t.lexeme),
            parent_id,
            attributes.attributes,
            entry_stack,
            exit_stack,
        );
        diagnostics::handle_symbol_redef_error(stores, &mut had_error, prev_def);
    } else {
        let (item_id, prev_def) = if generic_params.tokens.is_empty() {
            stores.items.new_function(
                stores.sigs,
                &mut had_error,
                name_token.map(|t| t.lexeme),
                parent_id,
                attributes.attributes,
                entry_stack,
                exit_stack,
            )
        } else {
            stores.items.new_generic_function(
                stores.sigs,
                &mut had_error,
                name_token.map(|t| t.lexeme),
                parent_id,
                attributes.attributes,
                entry_stack,
                exit_stack,
                generic_params
                    .tokens
                    .iter()
                    .map(|t| t.unwrap_single().map(|t| t.lexeme))
                    .collect(),
            )
        };

        diagnostics::handle_symbol_redef_error(stores, &mut had_error, prev_def);

        if let Some(lang_item_id) = attributes.lang_item {
            stores.items.set_lang_item(lang_item_id, item_id);
        }

        let body = parse_item_body(stores, &mut had_error, token_iter, name_token, item_id);
        let body_block_id = stores.blocks.new_block(body);
        stores.items.set_item_body(item_id, body_block_id);
    }

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_assert(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let name_token = token_iter
        .expect_single(stores, TokenKind::Ident, keyword.location)
        .recover(&mut had_error, keyword);

    let (item_id, prev_def) = stores.items.new_assert(
        stores.sigs,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
    );
    diagnostics::handle_symbol_redef_error(stores, &mut had_error, prev_def);

    let body = parse_item_body(stores, &mut had_error, token_iter, name_token, item_id);
    let body_block_id = stores.blocks.new_block(body);
    stores.items.set_item_body(item_id, body_block_id);

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_const(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();
    let name_token = token_iter
        .expect_single(stores, TokenKind::Ident, keyword.location)
        .recover(&mut had_error, keyword);

    let exit_stack = parse_stack_def(stores, &mut had_error, token_iter, name_token);
    let exit_stack = exit_stack.map(|st| st.into_iter().collect());

    let (item_id, prev_def) = stores.items.new_const(
        stores.sigs,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
        exit_stack,
    );
    diagnostics::handle_symbol_redef_error(stores, &mut had_error, prev_def);

    let body = parse_item_body(stores, &mut had_error, token_iter, name_token, item_id);
    let body_block_id = stores.blocks.new_block(body);
    stores.items.set_item_body(item_id, body_block_id);

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_variable(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let attributes = try_get_attributes(stores, token_iter, keyword)
        .recover(&mut had_error, ParsedAttributes::fallback(keyword));

    let name_token = token_iter
        .expect_single(stores, TokenKind::Ident, attributes.last_token.location)
        .recover(&mut had_error, attributes.last_token);

    let fallback = TreeGroup::fallback(BracketKind::Brace, name_token);
    let store_type = token_iter
        .expect_group(stores, BracketKind::Brace, name_token)
        .with_kinds(stores, Matcher("type", valid_type_token))
        .recover(&mut had_error, &fallback);

    let store_type_location = if store_type.tokens.is_empty() {
        store_type.span()
    } else {
        let first = store_type.tokens.first().unwrap();
        let last = store_type.tokens.last().unwrap();
        first.span().merge(last.span())
    };

    let mut unresolved_store_type =
        parse_multiple_unresolved_types(stores, store_type.open.location, &store_type.tokens)
            .recover(&mut had_error, Vec::new());

    if unresolved_store_type.len() != 1 {
        diagnostics::emit_error(
            stores,
            store_type_location,
            format!("expected 1 type, found {}", unresolved_store_type.len()),
            [Label::new(store_type_location).with_color(Color::Red)],
            None,
        );
        had_error.set();
    }

    let variable_type = unresolved_store_type.pop().unwrap();

    let (_, prev_def) = stores.items.new_variable(
        stores.sigs,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
        attributes.attributes,
        variable_type,
    );
    diagnostics::handle_symbol_redef_error(stores, &mut had_error, prev_def);

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_struct_or_union(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    module_id: ItemId,
    keyword: Spanned<Token>,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let attributes = try_get_attributes(stores, token_iter, keyword)
        .recover(&mut had_error, ParsedAttributes::fallback(keyword));

    let name_token = token_iter
        .expect_single(stores, TokenKind::Ident, attributes.last_token.location)
        .recover(&mut had_error, attributes.last_token);

    let fallback = TreeGroup::fallback(BracketKind::Paren, name_token);
    let generic_params = if token_iter.next_is_group(BracketKind::Paren) {
        let generic_idents = token_iter
            .expect_group(stores, BracketKind::Paren, name_token)
            .with_kinds(stores, TokenKind::Ident)
            .recover(&mut had_error, &fallback);

        generic_idents
            .tokens
            .iter()
            .map(|st| st.unwrap_single().map(|t| t.lexeme))
            .collect()
    } else {
        Vec::new()
    };

    let fallback = TreeGroup::fallback(BracketKind::Brace, name_token);
    let struct_body = token_iter
        .expect_group(stores, BracketKind::Brace, name_token)
        .recover(&mut had_error, &fallback);

    let mut field_iter = TokenIter::new(struct_body.tokens.iter());
    let mut fields = Vec::new();
    let mut prev_token = struct_body.first_token();

    while field_iter.next_is(TokenKind::Ident) {
        let name_token = field_iter
            .expect_single(stores, TokenKind::Ident, prev_token.location)
            .recover(&mut had_error, prev_token);

        let delim = get_terminated_tokens(
            stores,
            &mut field_iter,
            name_token,
            None,
            Matcher("type", valid_type_token),
            TokenKind::Comma,
            true,
        )
        .recover(
            &mut had_error,
            Terminated {
                close: name_token,
                list: Vec::new(),
            },
        );

        let store_type_location = delim
            .list
            .first()
            .zip(delim.list.last())
            .map(|(f, l)| f.first_token().location.merge(l.last_token().location))
            .unwrap_or(name_token.location);

        let mut unresolved_store_type =
            parse_multiple_unresolved_types(stores, name_token.location, &delim.list)
                .recover(&mut had_error, Vec::new());

        if unresolved_store_type.len() != 1 {
            diagnostics::emit_error(
                stores,
                store_type_location,
                "expected type",
                [Label::new(store_type_location).with_color(Color::Red)],
                None,
            );
            had_error.set();
        }

        fields.push(StructDefField {
            name: name_token.map(|t| t.lexeme),
            kind: unresolved_store_type.pop().unwrap(),
        });
        prev_token = delim.close;
    }

    // TODO: handle remaining tokens in field iter.

    let struct_def = StructDef {
        name: name_token.map(|t| t.lexeme),
        fields,
        generic_params,
        is_union: keyword.inner.kind == TokenKind::Union,
    };

    let (item_id, prev_def) = stores.items.new_struct(
        stores.sigs,
        &mut had_error,
        module_id,
        struct_def,
        attributes.attributes,
    );

    diagnostics::handle_symbol_redef_error(stores, &mut had_error, prev_def);

    if let Some(lang_item_id) = attributes.lang_item {
        stores.items.set_lang_item(lang_item_id, item_id);
    }

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_module(
    stores: &Stores,
    token_iter: &mut TokenIter,
    include_queue: &mut VecDeque<(ModuleQueueType, Option<ItemId>)>,
    token: Spanned<Token>,
    module_id: ItemId,
) -> Result<(), ()> {
    let module_ident = token_iter.expect_single(stores, TokenKind::Ident, token.location)?;

    include_queue.push_back((
        ModuleQueueType::Include(module_ident.map(|t| t.lexeme)),
        Some(module_id),
    ));

    Ok(())
}

pub fn parse_import(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut TokenIter,
    token: Spanned<Token>,
    module_id: ItemId,
) -> Result<(), ()> {
    let root_name = token_iter.expect_single(
        stores,
        Matcher("ident", |t| {
            t == TokenKind::Ident || t == TokenKind::ColonColon
        }),
        token.location,
    )?;

    let Ok((path, _)) = parse_ident(stores, had_error, token_iter, root_name) else {
        had_error.set();
        return Ok(());
    };

    stores
        .sigs
        .urir
        .get_scope_mut(module_id)
        .add_unresolved_import(path);

    Ok(())
}
