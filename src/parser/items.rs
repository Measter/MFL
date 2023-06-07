use std::{collections::VecDeque, iter::Peekable, ops::Not};

use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{Token, TokenKind},
    program::{ItemId, ItemKind, ModuleQueueType, Program},
    source_file::{SourceStorage, Spanned, WithSpan},
    type_store::{UnresolvedField, UnresolvedStruct, UnresolvedType},
};

use super::{
    expect_token, parse_delimited_token_list,
    utils::{parse_ident, parse_unresolved_types, valid_type_token},
    Delimited, Recover,
};

pub fn parse_memory<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    parent_id: ItemId,
    interner: &Interners,
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

    let store_type = parse_delimited_token_list(
        token_iter,
        name_token,
        None,
        ("is", |t| t == TokenKind::Is),
        ("type name", valid_type_token),
        ("end", |t| t == TokenKind::End),
        interner,
        source_store,
    )
    .recover(&mut had_error, Delimited::fallback(name_token));

    let store_type_location = if store_type.list.is_empty() {
        store_type.span()
    } else {
        let first = store_type.list.first().unwrap();
        let last = store_type.list.last().unwrap();
        first.location.merge(last.location)
    };

    let mut unresolved_store_type =
        parse_unresolved_types(interner, source_store, store_type.open, &store_type.list)
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

    let memory_type = unresolved_store_type
        .pop()
        .map(|(t, _)| UnresolvedType::Tokens(t).with_span(store_type_location))
        .unwrap();

    let item_id = program.new_memory(
        source_store,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
        memory_type,
    );

    let parent_kind = program.get_item_header(parent_id).kind();
    if parent_kind == ItemKind::Function || parent_kind == ItemKind::GenericFunction {
        let pd = program.get_function_data_mut(parent_id);
        pd.allocs.insert(name_token.inner.lexeme, item_id);
    }

    had_error.not().then_some((name_token, item_id)).ok_or(())
}

pub fn parse_struct<'a>(
    program: &mut Program,
    module_id: ItemId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    interner: &Interners,
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

    let generic_params = if token_iter
        .peek()
        .is_some_and(|(_, t)| t.inner.kind == TokenKind::ParenthesisOpen)
    {
        let generic_idents = parse_delimited_token_list(
            token_iter,
            name_token,
            None,
            ("`(`", |t| t == TokenKind::ParenthesisOpen),
            ("`ident`", |t| t == TokenKind::Ident),
            ("`)`", |t| t == TokenKind::ParenthesisClosed),
            interner,
            source_store,
        )
        .recover(&mut had_error, Delimited::fallback(name_token));

        Some(
            generic_idents
                .list
                .into_iter()
                .map(|st| st.map(|t| t.lexeme))
                .collect(),
        )
    } else {
        None
    };

    let is_token = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        keyword,
        interner,
        source_store,
    )
    .map(|(_, a)| a)
    .recover(&mut had_error, name_token);

    let mut fields = Vec::new();
    let mut prev_token = expect_token(
        token_iter,
        "field",
        |k| k == TokenKind::Field,
        keyword,
        interner,
        source_store,
    )
    .map(|(_, a)| a)
    .recover(&mut had_error, is_token);

    loop {
        let type_tokens = parse_delimited_token_list(
            token_iter,
            prev_token,
            None,
            ("ident", |t| t == TokenKind::Ident),
            ("type name", valid_type_token),
            ("end or field", |t| {
                t == TokenKind::End || t == TokenKind::Field
            }),
            interner,
            source_store,
        )
        .recover(&mut had_error, Delimited::fallback(name_token));

        let last_type_token = type_tokens
            .list
            .last()
            .copied()
            .unwrap_or(type_tokens.close);
        let store_type_location = type_tokens.open.location.merge(last_type_token.location);
        let mut unresolved_store_type =
            parse_unresolved_types(interner, source_store, type_tokens.open, &type_tokens.list)
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

        fields.push(UnresolvedField {
            name: type_tokens.open.map(|t| t.lexeme),
            kind: UnresolvedType::Tokens(unresolved_store_type.pop().unwrap().0),
        });
        prev_token = type_tokens.close;

        if type_tokens.close.inner.kind == TokenKind::End {
            break;
        }
    }

    let struct_def = UnresolvedStruct {
        name: name_token.map(|t| t.lexeme),
        fields,
        generic_params,
    };

    program.new_struct(source_store, &mut had_error, module_id, struct_def);

    if !had_error {
        Ok(())
    } else {
        Err(())
    }
}

pub fn parse_module<'a>(
    interner: &Interners,
    source_store: &SourceStorage,
    include_queue: &mut VecDeque<(ModuleQueueType, Option<ItemId>)>,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    module_id: ItemId,
) -> Result<(), ()> {
    let (_, module_ident) = expect_token(
        token_iter,
        "ident",
        |k| k == TokenKind::Ident,
        token,
        interner,
        source_store,
    )?;

    include_queue.push_back((
        ModuleQueueType::Include(module_ident.map(|t| t.lexeme)),
        Some(module_id),
    ));

    Ok(())
}

pub fn parse_import<'a>(
    program: &mut Program,
    interner: &Interners,
    source_store: &SourceStorage,
    had_error: &mut bool,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    module_id: ItemId,
) -> Result<(), ()> {
    let (_, root_name) = expect_token(
        token_iter,
        "ident",
        |k| k == TokenKind::Ident,
        token,
        interner,
        source_store,
    )?;

    let path = parse_ident(token_iter, interner, source_store, had_error, root_name)
        .map(|id| id.path)
        .recover(had_error, Vec::new());

    program
        .get_module_mut(module_id)
        .add_unresolved_import(path);

    Ok(())
}
