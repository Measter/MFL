use std::iter::Peekable;

use crate::{
    interners::Interner,
    lexer::{Token, TokenKind},
    opcode::{If, Op, OpCode, OpId, While},
    program::{ItemId, Program},
    source_file::{SourceStorage, Spanned},
};

use super::{parse_item_body_contents, utils::get_terminated_tokens};

pub fn parse_if<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
    interner: &mut Interner,
    source_store: &SourceStorage,
) -> Result<OpCode, ()> {
    let condition_tokens = get_terminated_tokens(
        token_iter,
        keyword,
        None,
        ("any", |_| true),
        ("do", |t| t == TokenKind::Do),
        interner,
        source_store,
    )?;

    let condition = parse_item_body_contents(
        program,
        &condition_tokens.list,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let then_block_tokens = get_terminated_tokens(
        token_iter,
        condition_tokens.close,
        None,
        ("any", |_| true),
        ("end`, `else` or `elif", |t| {
            matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif)
        }),
        interner,
        source_store,
    )?;
    let mut close_token = then_block_tokens.close;

    let then_block = parse_item_body_contents(
        program,
        &then_block_tokens.list,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let else_token = close_token;
    let mut elif_blocks = Vec::new();

    while close_token.inner.kind == TokenKind::Elif {
        let elif_condition_tokens = get_terminated_tokens(
            token_iter,
            close_token,
            None,
            ("any", |_| true),
            ("do", |t| t == TokenKind::Do),
            interner,
            source_store,
        )?;

        let elif_condition = parse_item_body_contents(
            program,
            &elif_condition_tokens.list,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        let elif_block_tokens = get_terminated_tokens(
            token_iter,
            elif_condition_tokens.close,
            None,
            ("any", |_| true),
            ("end`, `else`, or `elif", |t| {
                matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif)
            }),
            interner,
            source_store,
        )?;

        let elif_block = parse_item_body_contents(
            program,
            &elif_block_tokens.list,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        elif_blocks.push((
            close_token,
            elif_condition,
            elif_condition_tokens.close,
            elif_block,
            elif_block_tokens.close,
        ));
        close_token = elif_block_tokens.close;
    }

    let mut else_block = if close_token.inner.kind == TokenKind::Else {
        let else_block_tokens = get_terminated_tokens(
            token_iter,
            close_token,
            None,
            ("any", |_| true),
            ("end", |t| t == TokenKind::End),
            interner,
            source_store,
        )?;

        let else_block = parse_item_body_contents(
            program,
            &else_block_tokens.list,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        close_token = else_block_tokens.close;

        else_block
    } else {
        Vec::new()
    };

    // Normalize into an `if <cond> do <body> else <body> end` structure.
    while let Some((open_token, condition, do_token, then_block, else_token)) = elif_blocks.pop() {
        let if_op = Op::new(
            op_id_gen(),
            OpCode::If(Box::new(If {
                open_token: open_token.location,
                condition,
                is_condition_terminal: false,
                do_token: do_token.location,
                then_block,
                is_then_terminal: false,
                else_token: else_token.location,
                else_block,
                is_else_terminal: false,
                end_token: close_token.location,
            })),
            open_token.map(|t| t.lexeme),
        );

        else_block = vec![if_op];
    }

    Ok(OpCode::If(Box::new(If {
        open_token: keyword.location,
        condition,
        is_condition_terminal: false,
        do_token: condition_tokens.close.location,
        then_block,
        is_then_terminal: false,
        else_token: else_token.location,
        else_block,
        is_else_terminal: false,
        end_token: close_token.location,
    })))
}

pub fn parse_while<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    keyword: Spanned<Token>,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
    interner: &mut Interner,
    source_store: &SourceStorage,
) -> Result<OpCode, ()> {
    let condition_tokens = get_terminated_tokens(
        token_iter,
        keyword,
        None,
        ("any", |_| true),
        ("do", |t| t == TokenKind::Do),
        interner,
        source_store,
    )?;

    let condition = parse_item_body_contents(
        program,
        &condition_tokens.list,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let body_tokens = get_terminated_tokens(
        token_iter,
        condition_tokens.close,
        None,
        ("any", |_| true),
        ("end", |t| t == TokenKind::End),
        interner,
        source_store,
    )?;

    let body_block = parse_item_body_contents(
        program,
        &body_tokens.list,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    Ok(OpCode::While(Box::new(While {
        do_token: condition_tokens.close.location,
        condition,
        body_block,
        end_token: body_tokens.close.location,
    })))
}
