use std::collections::VecDeque;

use ariadne::{Color, Label};
use lasso::Spur;

use crate::{
    context::{Context, ItemId},
    diagnostics,
    error_signal::ErrorSignal,
    ir::{Basic, Control, OpCode, StructDef, StructDefField},
    lexer::{BracketKind, Token, TokenKind, TreeGroup},
    program::ModuleQueueType,
    stores::{ops::OpId, source::Spanned},
    Stores,
};

use super::{
    parse_item_body_contents,
    utils::{
        get_terminated_tokens, parse_ident, parse_multiple_unresolved_types, parse_stack_def,
        valid_type_token, Matcher, Terminated, TokenIter, TokenTreeOptionExt, TreeGroupResultExt,
    },
    Recover,
};

fn try_get_lang_item(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
) -> Result<Option<Spanned<Spur>>, ()> {
    if !token_iter.next_is(TokenKind::LangItem) {
        return Ok(None);
    }
    // Consume the lang item.
    let lang_token = token_iter.next().unwrap_single();
    let delim = token_iter
        .expect_group(stores, BracketKind::Paren, lang_token)
        .with_kinds(stores, TokenKind::Ident)
        .with_length(stores, 1)?;

    let ident_name = delim.tokens[0].unwrap_single();

    Ok(Some(ident_name.map(|t| t.lexeme)))
}

fn parse_item_body(
    ctx: &mut Context,
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

    let mut body = parse_item_body_contents(ctx, stores, &delim.tokens, parent_id)
        .recover(had_error, Vec::new());

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
    ctx: &mut Context,
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let lang_item = try_get_lang_item(stores, token_iter).recover(&mut had_error, None);

    let name_token = token_iter
        .expect_single(stores, TokenKind::Ident, keyword.location)
        .recover(&mut had_error, keyword);

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

    let item_id = if generic_params.tokens.is_empty() {
        ctx.new_function(
            stores,
            &mut had_error,
            name_token.map(|t| t.lexeme),
            parent_id,
            entry_stack,
            exit_stack,
        )
    } else {
        ctx.new_generic_function(
            stores,
            &mut had_error,
            name_token.map(|t| t.lexeme),
            parent_id,
            entry_stack,
            exit_stack,
            generic_params
                .tokens
                .iter()
                .map(|t| t.unwrap_single().map(|t| t.lexeme))
                .collect(),
        )
    };

    if let Some(lang_item_id) = lang_item {
        ctx.set_lang_item(stores, &mut had_error, lang_item_id, item_id);
    }

    let body = parse_item_body(ctx, stores, &mut had_error, token_iter, name_token, item_id);
    let body_block_id = stores.blocks.new_block(body);
    ctx.set_item_body(item_id, body_block_id);

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_assert(
    ctx: &mut Context,
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();
    let name_token = token_iter
        .expect_single(stores, TokenKind::Ident, keyword.location)
        .recover(&mut had_error, keyword);

    let item_id = ctx.new_assert(
        stores,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
    );

    let body = parse_item_body(ctx, stores, &mut had_error, token_iter, name_token, item_id);
    let body_block_id = stores.blocks.new_block(body);
    ctx.set_item_body(item_id, body_block_id);

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_const(
    ctx: &mut Context,
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

    let item_id = ctx.new_const(
        stores,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
        exit_stack,
    );

    let body = parse_item_body(ctx, stores, &mut had_error, token_iter, name_token, item_id);
    let body_block_id = stores.blocks.new_block(body);
    ctx.set_item_body(item_id, body_block_id);

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_memory(
    ctx: &mut Context,
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    keyword: Spanned<Token>,
    parent_id: ItemId,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();
    let name_token = token_iter
        .expect_single(stores, TokenKind::Ident, keyword.location)
        .recover(&mut had_error, keyword);

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

    let memory_type = unresolved_store_type.pop().unwrap();

    ctx.new_memory(
        stores,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
        memory_type,
    );

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_struct_or_union(
    ctx: &mut Context,
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    module_id: ItemId,
    keyword: Spanned<Token>,
) -> Result<(), ()> {
    let mut had_error = ErrorSignal::new();

    let lang_item = try_get_lang_item(stores, token_iter).recover(&mut had_error, None);

    let name_token = token_iter
        .expect_single(stores, TokenKind::Ident, keyword.location)
        .recover(&mut had_error, keyword);

    let fallback = TreeGroup::fallback(BracketKind::Paren, name_token);
    let generic_params = if token_iter.next_is_group(BracketKind::Paren) {
        let generic_idents = token_iter
            .expect_group(stores, BracketKind::Paren, name_token)
            .with_kinds(stores, TokenKind::Ident)
            .recover(&mut had_error, &fallback);

        Some(
            generic_idents
                .tokens
                .iter()
                .map(|st| st.unwrap_single().map(|t| t.lexeme))
                .collect(),
        )
    } else {
        None
    };

    let fallback = TreeGroup::fallback(BracketKind::Brace, name_token);
    let struct_body = token_iter
        .expect_group(stores, BracketKind::Brace, name_token)
        .recover(&mut had_error, &fallback);

    let mut field_iter = TokenIter::new(struct_body.tokens.iter());
    let mut fields = Vec::new();
    let mut prev_token = struct_body.first_token();

    while field_iter.next_is(TokenKind::Field) {
        let field_token = field_iter
            .expect_single(stores, TokenKind::Field, prev_token.location)
            .recover(&mut had_error, prev_token);

        let name_token = field_iter
            .expect_single(stores, TokenKind::Ident, field_token.location)
            .recover(&mut had_error, field_token);

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
            kind: unresolved_store_type.pop().unwrap().inner,
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

    let item_id = ctx.new_struct(stores, &mut had_error, module_id, struct_def);
    if let Some(lang_item_id) = lang_item {
        ctx.set_lang_item(stores, &mut had_error, lang_item_id, item_id);
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
    ctx: &mut Context,
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

    ctx.urir_mut()
        .get_scope_mut(module_id)
        .add_unresolved_import(path);

    Ok(())
}
