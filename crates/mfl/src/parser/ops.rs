use std::iter::Peekable;

use crate::{
    interners::Interner,
    lexer::{Token, TokenKind},
    opcode::{If, Op, OpCode, OpId, While},
    program::{ItemId, Program},
    source_file::{SourceStorage, Spanned},
};

use super::{get_item_body, parse_item_body_contents};

pub fn parse_if<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Spanned<Token>)>>,
    tokens: &'a [Spanned<Token>],
    keyword: Spanned<Token>,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
    interner: &mut Interner,
    source_store: &SourceStorage,
) -> Result<OpCode, ()> {
    let (condition, do_token) = get_item_body(
        token_iter,
        tokens,
        keyword,
        keyword,
        |t| matches!(t, TokenKind::Do),
        source_store,
    )?;

    let condition = parse_item_body_contents(
        program,
        condition,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let (main_block, mut close_token) = get_item_body(
        token_iter,
        tokens,
        keyword,
        keyword,
        |t| matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif),
        source_store,
    )?;

    let then_block = parse_item_body_contents(
        program,
        main_block,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let else_token = close_token;
    let mut elif_blocks = Vec::new();

    while close_token.inner.kind == TokenKind::Elif {
        let (elif_condition, do_token) = get_item_body(
            token_iter,
            tokens,
            keyword,
            keyword,
            |t| matches!(t, TokenKind::Do),
            source_store,
        )?;

        let elif_condition = parse_item_body_contents(
            program,
            elif_condition,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        let (elif_block, cur_close_token) = get_item_body(
            token_iter,
            tokens,
            keyword,
            keyword,
            |t| matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif),
            source_store,
        )?;

        let elif_block = parse_item_body_contents(
            program,
            elif_block,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        elif_blocks.push((
            close_token,
            elif_condition,
            do_token,
            elif_block,
            cur_close_token,
        ));
        close_token = cur_close_token;
    }

    let mut else_block = if close_token.inner.kind == TokenKind::Else {
        let (else_block, end_token) = get_item_body(
            token_iter,
            tokens,
            keyword,
            keyword,
            |t| matches!(t, TokenKind::End),
            source_store,
        )?;

        let else_block = parse_item_body_contents(
            program,
            else_block,
            op_id_gen,
            interner,
            parent_id,
            source_store,
        )?;

        close_token = end_token;

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
        do_token: do_token.location,
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
    tokens: &'a [Spanned<Token>],
    keyword: Spanned<Token>,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent_id: ItemId,
    interner: &mut Interner,
    source_store: &SourceStorage,
) -> Result<OpCode, ()> {
    let (condition, do_token) = get_item_body(
        token_iter,
        tokens,
        keyword,
        keyword,
        |t| matches!(t, TokenKind::Do),
        source_store,
    )?;

    let condition = parse_item_body_contents(
        program,
        condition,
        op_id_gen,
        interner,
        parent_id,
        source_store,
    )?;

    let (body, end_token) = get_item_body(
        token_iter,
        tokens,
        keyword,
        do_token,
        |t| matches!(t, TokenKind::End),
        source_store,
    )?;

    let body_block =
        parse_item_body_contents(program, body, op_id_gen, interner, parent_id, source_store)?;

    Ok(OpCode::While(Box::new(While {
        do_token: do_token.location,
        condition,
        body_block,
        end_token: end_token.location,
    })))
}
