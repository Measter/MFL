use std::{collections::VecDeque, iter::Peekable};

use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interner,
    lexer::{Token, TokenKind},
    opcode::{Op, OpCode, OpId},
    program::{ItemId, ModuleQueueType, Program},
    source_file::{SourceStorage, Spanned, WithSpan},
    type_store::{UnresolvedField, UnresolvedStruct, UnresolvedType},
};

use super::{
    expect_token, parse_delimited_token_list, parse_item_body_contents,
    utils::{parse_ident, parse_stack_def, parse_unresolved_types, valid_type_token},
    Delimited, Recover,
};
fn parse_item_body<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    name_token: Spanned<Token>,
    interner: &mut Interner,
    source_store: &SourceStorage,
    had_error: &mut bool,
    program: &mut Program,
    parent_id: ItemId,
) -> Vec<Op> {
    let mut op_id = 0;
    let mut op_id_gen = || {
        let id = op_id;
        op_id += 1;
        OpId(id)
    };

    let body_delim = parse_delimited_token_list(
        token_iter,
        name_token,
        None,
        ("is", |t| t == TokenKind::Is),
        ("item", |_| true),
        ("end", |t| t == TokenKind::End),
        interner,
        source_store,
    )
    .recover(had_error, Delimited::fallback(name_token));

    let mut body = parse_item_body_contents(
        program,
        &body_delim.list,
        &mut op_id_gen,
        interner,
        parent_id,
        source_store,
    )
    .recover(had_error, Vec::new());

    // Makes later logic easier if we always have a prologue and epilogue.
    body.insert(
        0,
        Op {
            code: OpCode::Prologue,
            id: op_id_gen(),
            token: body_delim.open.map(|t| t.lexeme),
        },
    );
    body.push(Op {
        code: OpCode::Epilogue,
        id: op_id_gen(),
        token: body_delim.close.map(|t| t.lexeme),
    });

    body
}

pub fn parse_function<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    parent_id: ItemId,
    interner: &mut Interner,
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
        parse_delimited_token_list(
            token_iter,
            name_token,
            None,
            ("(", |t| t == TokenKind::ParenthesisOpen),
            ("ident", |t| t == TokenKind::Ident),
            (")", |t| t == TokenKind::ParenthesisClosed),
            interner,
            source_store,
        )
        .recover(&mut had_error, Delimited::fallback(name_token))
    } else {
        Delimited::fallback(name_token)
    };

    let entry_stack = parse_stack_def(
        token_iter,
        &mut had_error,
        name_token,
        interner,
        source_store,
    );

    let entry_stack = entry_stack.map(|st| {
        st.into_iter()
            .map(|t| t.map(UnresolvedType::Tokens))
            .collect()
    });

    expect_token(
        token_iter,
        "to",
        |k| k == TokenKind::GoesTo,
        name_token,
        interner,
        source_store,
    )
    .recover(&mut had_error, (0, name_token));

    let exit_stack = parse_stack_def(
        token_iter,
        &mut had_error,
        name_token,
        interner,
        source_store,
    );

    let exit_stack = exit_stack.map(|st| {
        st.into_iter()
            .map(|t| t.map(UnresolvedType::Tokens))
            .collect()
    });

    let item_id = if generic_params.list.is_empty() {
        program.new_function(
            source_store,
            &mut had_error,
            name_token.map(|t| t.lexeme),
            parent_id,
            entry_stack,
            exit_stack,
        )
    } else {
        program.new_generic_function(
            source_store,
            &mut had_error,
            name_token.map(|t| t.lexeme),
            parent_id,
            entry_stack,
            exit_stack,
            generic_params
                .list
                .into_iter()
                .map(|t| t.map(|t| t.lexeme))
                .collect(),
        )
    };

    let body = parse_item_body(
        token_iter,
        name_token,
        interner,
        source_store,
        &mut had_error,
        program,
        item_id,
    );

    program.set_item_body(item_id, body);

    if had_error {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_assert<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    parent_id: ItemId,
    interner: &mut Interner,
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

    let item_id = program.new_assert(
        source_store,
        interner,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
    );

    let body = parse_item_body(
        token_iter,
        name_token,
        interner,
        source_store,
        &mut had_error,
        program,
        item_id,
    );

    program.set_item_body(item_id, body);

    if had_error {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_const<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    parent_id: ItemId,
    interner: &mut Interner,
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

    let exit_stack = parse_stack_def(
        token_iter,
        &mut had_error,
        name_token,
        interner,
        source_store,
    );

    let exit_stack = exit_stack.map(|st| {
        st.into_iter()
            .map(|t| t.map(UnresolvedType::Tokens))
            .collect()
    });

    let item_id = program.new_const(
        source_store,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
        exit_stack,
    );

    let body = parse_item_body(
        token_iter,
        name_token,
        interner,
        source_store,
        &mut had_error,
        program,
        item_id,
    );

    program.set_item_body(item_id, body);

    if had_error {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_memory<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    parent_id: ItemId,
    interner: &Interner,
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

    // TODO: Make this not crash on an empty store type
    let memory_type = unresolved_store_type
        .pop()
        .map(|t| UnresolvedType::Tokens(t.inner).with_span(store_type_location))
        .unwrap();

    program.new_memory(
        source_store,
        &mut had_error,
        name_token.map(|t| t.lexeme),
        parent_id,
        memory_type,
    );

    if had_error {
        Err(())
    } else {
        Ok(())
    }
}

pub fn parse_struct<'a>(
    program: &mut Program,
    module_id: ItemId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    interner: &Interner,
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
            kind: UnresolvedType::Tokens(unresolved_store_type.pop().unwrap().inner),
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
    interner: &Interner,
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
    interner: &Interner,
    source_store: &SourceStorage,
    had_error: &mut bool,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    token: Spanned<Token>,
    module_id: ItemId,
) -> Result<(), ()> {
    let (_, root_name) = expect_token(
        token_iter,
        "ident",
        |k| k == TokenKind::Ident || k == TokenKind::ColonColon,
        token,
        interner,
        source_store,
    )?;

    let Ok((path, _)) = parse_ident(token_iter, interner, source_store, had_error, root_name) else {
        *had_error = true;
        return Ok(());
    };

    program.get_scope_mut(module_id).add_unresolved_import(path);

    Ok(())
}
