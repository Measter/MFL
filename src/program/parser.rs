use std::{iter::Peekable, ops::Not};

use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{Token, TokenKind},
    opcode::{ConditionalBlock, Direction, Op, OpCode, OpId},
    source_file::{SourceLocation, SourceStorage},
};

use super::{
    static_analysis::{IntWidth, PorthType, PorthTypeKind},
    FunctionData, ModuleId, ProcedureId, ProcedureKind, Program,
};

fn expect_token<'a>(
    tokens: &mut impl Iterator<Item = (usize, &'a Token)>,
    kind_str: &str,
    expected: fn(TokenKind) -> bool,
    prev: Token,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(usize, Token), ()> {
    match tokens.next() {
        Some((idx, ident)) if expected(ident.kind) => Ok((idx, *ident)),
        Some((_, ident)) => {
            diagnostics::emit_error(
                ident.location,
                format!(
                    "expected `{}`, found `{}`",
                    kind_str,
                    interner.resolve_lexeme(ident.lexeme)
                ),
                Some(
                    Label::new(ident.location)
                        .with_color(Color::Red)
                        .with_message("here"),
                ),
                None,
                source_store,
            );
            Err(())
        }
        None => {
            diagnostics::emit_error(
                prev.location,
                "unexpected end of tokens",
                Some(
                    Label::new(prev.location)
                        .with_color(Color::Red)
                        .with_message("here"),
                ),
                None,
                source_store,
            );
            Err(())
        }
    }
}

fn parse_delimited_token<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    prev: Token,
    (open_delim_str, open_delim_fn): (&'static str, fn(TokenKind) -> bool),
    (token_str, token_fn): (&'static str, fn(TokenKind) -> bool),
    (close_delim_str, close_delim_fn): (&'static str, fn(TokenKind) -> bool),
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<Token, ()> {
    let (_, open_token) = expect_token(
        token_iter,
        open_delim_str,
        open_delim_fn,
        prev,
        interner,
        source_store,
    )?;
    let (_, count_token) = expect_token(
        token_iter,
        token_str,
        token_fn,
        open_token,
        interner,
        source_store,
    )?;
    let _ = expect_token(
        token_iter,
        close_delim_str,
        close_delim_fn,
        count_token,
        interner,
        source_store,
    )?;

    Ok(count_token)
}

pub fn parse_procedure_body(
    program: &mut Program,
    module_id: ModuleId,
    tokens: &[Token],
    op_id_gen: &mut impl FnMut() -> OpId,
    interner: &Interners,
    parent: Option<ProcedureId>,
    source_store: &SourceStorage,
) -> Result<Vec<Op>, ()> {
    let mut ops = Vec::new();
    let mut had_error = false;

    let mut token_iter = tokens.iter().enumerate().peekable();
    while let Some((_, token)) = token_iter.next() {
        let kind = match token.kind {
            TokenKind::Drop
            | TokenKind::Dup
            | TokenKind::Over
            | TokenKind::Swap
            | TokenKind::SysCall => {
                let (count, count_token) = if matches!(token_iter.peek(), Some((_,tk)) if tk.kind == TokenKind::ParenthesisOpen)
                {
                    let count_token = parse_delimited_token(
                        &mut token_iter,
                        *token,
                        ("(", |t| t == TokenKind::ParenthesisOpen),
                        ("Integer", |t| matches!(t, TokenKind::Integer(_))),
                        (")", |t| t == TokenKind::ParenthesisClosed),
                        interner,
                        source_store,
                    )?;

                    let TokenKind::Integer(count) = count_token.kind else { unreachable!() };
                    (count, count_token)
                } else {
                    (1, *token)
                };

                match token.kind {
                    TokenKind::Drop => OpCode::Drop {
                        count: count as usize,
                        count_token,
                    },
                    TokenKind::Dup => OpCode::Dup {
                        count: count as usize,
                        count_token,
                    },
                    TokenKind::Over => OpCode::Over {
                        depth: count as usize,
                        depth_token: count_token,
                    },
                    TokenKind::Swap => OpCode::Swap {
                        count: count as usize,
                        count_token,
                    },
                    TokenKind::SysCall => OpCode::SysCall {
                        arg_count: count as usize,
                        arg_count_token: count_token,
                    },

                    _ => unreachable!(),
                }
            }
            TokenKind::Rot => {
                let (_, paren_open) = expect_token(
                    &mut token_iter,
                    "(",
                    |t| t == TokenKind::ParenthesisOpen,
                    *token,
                    interner,
                    source_store,
                )?;

                let (_, item_count_token) = expect_token(
                    &mut token_iter,
                    "Integer",
                    |t| matches!(t, TokenKind::Integer(_)),
                    paren_open,
                    interner,
                    source_store,
                )?;

                let (_, direction_token) = expect_token(
                    &mut token_iter,
                    "<, >",
                    |t| matches!(t, TokenKind::Less | TokenKind::Greater),
                    item_count_token,
                    interner,
                    source_store,
                )?;

                let (_, shift_count_token) = expect_token(
                    &mut token_iter,
                    "Integer",
                    |t| matches!(t, TokenKind::Integer(_)),
                    direction_token,
                    interner,
                    source_store,
                )?;

                let (_, _) = expect_token(
                    &mut token_iter,
                    "(",
                    |t| t == TokenKind::ParenthesisClosed,
                    shift_count_token,
                    interner,
                    source_store,
                )?;

                let TokenKind::Integer(item_count) = item_count_token.kind else { unreachable!() };
                let TokenKind::Integer(shift_count) = shift_count_token.kind else { unreachable!() };
                let direction = match direction_token.kind {
                    TokenKind::Less => Direction::Left,
                    TokenKind::Greater => Direction::Right,
                    _ => unreachable!(),
                };

                OpCode::Rot {
                    item_count: item_count as usize,
                    direction,
                    shift_count: shift_count as usize,
                    item_count_token,
                    shift_count_token,
                }
            }

            TokenKind::Load | TokenKind::Store => {
                let ident_token = parse_delimited_token(
                    &mut token_iter,
                    *token,
                    ("(", |t| t == TokenKind::ParenthesisOpen),
                    ("Ident", |t| t == TokenKind::Ident),
                    (")", |t| t == TokenKind::ParenthesisClosed),
                    interner,
                    source_store,
                )?;

                let kind = match interner.resolve_lexeme(ident_token.lexeme) {
                    "u8" => PorthTypeKind::Int(IntWidth::I8),
                    "u16" => PorthTypeKind::Int(IntWidth::I16),
                    "u32" => PorthTypeKind::Int(IntWidth::I32),
                    "u64" => PorthTypeKind::Int(IntWidth::I64),
                    "bool" => PorthTypeKind::Bool,
                    "ptr" => PorthTypeKind::Ptr,

                    _ => {
                        diagnostics::emit_error(
                            ident_token.location,
                            "invalid ident",
                            [Label::new(ident_token.location)
                                .with_color(Color::Red)
                                .with_message("unknown type")],
                            None,
                            source_store,
                        );
                        return Err(());
                    }
                };

                match token.kind {
                    TokenKind::Load => OpCode::Load { kind },
                    TokenKind::Store => OpCode::Store { kind },
                    _ => unreachable!(),
                }
            }

            TokenKind::Equal => OpCode::Equal,
            TokenKind::Greater => OpCode::Greater,
            TokenKind::GreaterEqual => OpCode::GreaterEqual,
            TokenKind::Less => OpCode::Less,
            TokenKind::LessEqual => OpCode::LessEqual,
            TokenKind::NotEqual => OpCode::NotEq,

            TokenKind::Boolean(b) => OpCode::PushBool(b),
            TokenKind::Ident => {
                let (module, proc) = if matches!(token_iter.peek(), Some((_, t)) if t.kind == TokenKind::ColonColon)
                {
                    let (_, colons) = token_iter.next().unwrap(); // Consume the ColonColon.
                    let expected = expect_token(
                        &mut token_iter,
                        "ident",
                        |k| k == TokenKind::Ident,
                        *colons,
                        interner,
                        source_store,
                    )
                    .ok()
                    .map(|(_, t)| t);

                    let proc_id = if let Some(t) = expected {
                        t
                    } else {
                        had_error = true;
                        continue;
                    };

                    (Some(*token), proc_id)
                } else {
                    (None, *token)
                };

                OpCode::UnresolvedIdent { module, proc }
            }
            TokenKind::Integer(value) => {
                let (width, ident_token) = if matches!(token_iter.peek(), Some((_,tk)) if tk.kind == TokenKind::ParenthesisOpen)
                {
                    let ident_token = parse_delimited_token(
                        &mut token_iter,
                        *token,
                        ("(", |t| t == TokenKind::ParenthesisOpen),
                        ("Ident", |t| t == TokenKind::Ident),
                        (")", |t| t == TokenKind::ParenthesisClosed),
                        interner,
                        source_store,
                    )?;

                    let width = match interner.resolve_lexeme(ident_token.lexeme) {
                        "u8" => IntWidth::I8,
                        "u16" => IntWidth::I16,
                        "u32" => IntWidth::I32,
                        "u64" => IntWidth::I64,

                        _ => {
                            diagnostics::emit_error(
                                ident_token.location,
                                "invalid integer type",
                                [Label::new(ident_token.location)
                                    .with_color(Color::Red)
                                    .with_message("unknown type")],
                                None,
                                source_store,
                            );
                            return Err(());
                        }
                    };
                    (width, ident_token)
                } else {
                    (IntWidth::I64, *token)
                };

                if !width.bounds().contains(&value) {
                    diagnostics::emit_error(
                        ident_token.location,
                        "literal out of bounds",
                        [Label::new(ident_token.location)
                            .with_color(Color::Red)
                            .with_message(format!(
                                "valid range for {} is {:?}",
                                width.name(),
                                width.bounds(),
                            ))],
                        None,
                        source_store,
                    );
                    return Err(());
                }

                OpCode::PushInt { width, value }
            }
            TokenKind::String { id, is_c_str } => OpCode::PushStr { id, is_c_str },
            TokenKind::Here(id) => OpCode::PushStr {
                id,
                is_c_str: false,
            },
            TokenKind::ArgC => OpCode::ArgC,
            TokenKind::ArgV => OpCode::ArgV,

            TokenKind::While => {
                match parse_while(
                    program,
                    module_id,
                    &mut token_iter,
                    tokens,
                    *token,
                    op_id_gen,
                    parent,
                    interner,
                    source_store,
                ) {
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                    Ok(code) => code,
                }
            }

            TokenKind::Assert | TokenKind::Const | TokenKind::Memory => {
                if parse_procedure(
                    program,
                    module_id,
                    &mut token_iter,
                    tokens,
                    *token,
                    interner,
                    parent,
                    source_store,
                )
                .is_err()
                {
                    had_error = true;
                }
                continue;
            }
            TokenKind::Include | TokenKind::Macro | TokenKind::Proc => {
                diagnostics::emit_error(
                    token.location,
                    format!("cannot use `{:?}` inside a procedure", token.kind),
                    Some(
                        Label::new(token.location)
                            .with_color(Color::Red)
                            .with_message("here"),
                    ),
                    None,
                    source_store,
                );
                had_error = true;
                continue;
            }

            TokenKind::If => {
                match parse_if(
                    program,
                    module_id,
                    &mut token_iter,
                    tokens,
                    *token,
                    op_id_gen,
                    parent,
                    interner,
                    source_store,
                ) {
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                    Ok(code) => code,
                }
            }

            TokenKind::Minus => OpCode::Subtract,
            TokenKind::Plus => OpCode::Add,
            TokenKind::Star => OpCode::Multiply,
            TokenKind::DivMod => OpCode::DivMod,

            TokenKind::BitAnd => OpCode::BitAnd,
            TokenKind::BitNot => OpCode::BitNot,
            TokenKind::BitOr => OpCode::BitOr,
            TokenKind::ShiftLeft => OpCode::ShiftLeft,
            TokenKind::ShiftRight => OpCode::ShiftRight,

            TokenKind::Cast => {
                let ident_token = parse_delimited_token(
                    &mut token_iter,
                    *token,
                    ("(", |t| t == TokenKind::ParenthesisOpen),
                    ("Ident", |t| t == TokenKind::Ident),
                    (")", |t| t == TokenKind::ParenthesisClosed),
                    interner,
                    source_store,
                )?;

                let kind = match interner.resolve_lexeme(ident_token.lexeme) {
                    "u8" => PorthTypeKind::Int(IntWidth::I8),
                    "u16" => PorthTypeKind::Int(IntWidth::I16),
                    "u32" => PorthTypeKind::Int(IntWidth::I32),
                    "u64" => PorthTypeKind::Int(IntWidth::I64),
                    "ptr" => PorthTypeKind::Ptr,

                    "bool" => {
                        diagnostics::emit_error(
                            ident_token.location,
                            "cannot cast to a Bool",
                            [Label::new(ident_token.location).with_color(Color::Red)],
                            Some("use a comparison operator instead".to_owned()),
                            source_store,
                        );
                        return Err(());
                    }
                    _ => {
                        diagnostics::emit_error(
                            ident_token.location,
                            "invalid ident",
                            [Label::new(ident_token.location)
                                .with_color(Color::Red)
                                .with_message("unknown type")],
                            None,
                            source_store,
                        );
                        return Err(());
                    }
                };
                OpCode::Cast {
                    kind,
                    kind_token: ident_token,
                }
            }

            TokenKind::Return => OpCode::Return,

            // These are only used as part of a sub-block. If they're found anywhere else,
            // it's an error.
            TokenKind::ColonColon
            | TokenKind::GoesTo
            | TokenKind::Is
            | TokenKind::Do
            | TokenKind::Elif
            | TokenKind::Else
            | TokenKind::End
            | TokenKind::ParenthesisClosed
            | TokenKind::ParenthesisOpen
            | TokenKind::SquareBracketClosed
            | TokenKind::SquareBracketOpen => {
                diagnostics::emit_error(
                    token.location,
                    format!(
                        "unexpected token `{}` in input",
                        interner.resolve_lexeme(token.lexeme)
                    ),
                    Some(Label::new(token.location)),
                    None,
                    source_store,
                );

                had_error = true;
                continue;
            }
        };

        ops.push(Op::new(op_id_gen(), kind, *token));
    }

    had_error.not().then_some(ops).ok_or(())
}

fn get_procedure_body<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    mut last_token: Token,
    target_token_type: fn(TokenKind) -> bool,
    source_store: &SourceStorage,
) -> Result<(&'a [Token], Token), ()> {
    let body_start_idx = match token_iter.peek() {
        Some((idx, _)) => *idx,
        None => {
            diagnostics::end_of_file(last_token.location, source_store);
            return Err(());
        }
    };

    // We need to keep track of block depth so we know which token is ending the block.
    // We've already consumed the token that opened the block.
    let mut block_depth = 1;
    let mut end_idx = body_start_idx;
    let mut had_error = false;

    for (idx, token) in token_iter {
        use TokenKind::*;
        #[allow(clippy::match_like_matches_macro)]
        let is_nested_err = match (keyword.kind, token.kind) {
            (Proc, Include | Proc | Macro) => true,
            (Memory | Const, Proc | Macro | Const | Memory | Include) => true,
            _ => false,
        };

        if is_nested_err {
            diagnostics::emit_error(
                token.location,
                format!("cannot use {:?} inside a {:?}", token.kind, keyword.kind),
                Some(Label::new(token.location).with_color(Color::Red)),
                None,
                source_store,
            );
            had_error = true;
        }

        // If the block_depth is greater than 1, it means we're in a sub-block. All sub-blocks
        // will always close with an End token, so if we are in a sub-block only look for End.
        if token.kind.new_block() {
            block_depth += 1;
        } else if (block_depth > 1 && token.kind == TokenKind::End)
            || (block_depth == 1 && target_token_type(token.kind))
        {
            block_depth -= 1;
        }

        end_idx = idx;
        last_token = *token;

        if block_depth == 0 {
            break;
        }
    }

    if !target_token_type(last_token.kind) {
        diagnostics::end_of_file(last_token.location, source_store);
        return Err(());
    }

    had_error
        .not()
        .then(|| (&tokens[body_start_idx..end_idx], last_token))
        .ok_or(())
}

fn parse_if<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent: Option<ProcedureId>,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<OpCode, ()> {
    let (main_condition, do_token) = get_procedure_body(
        token_iter,
        tokens,
        keyword,
        keyword,
        |t| matches!(t, TokenKind::Do),
        source_store,
    )?;

    let main_condition = parse_procedure_body(
        program,
        module_id,
        main_condition,
        op_id_gen,
        interner,
        parent,
        source_store,
    )?;

    let (main_block, mut close_token) = get_procedure_body(
        token_iter,
        tokens,
        keyword,
        keyword,
        |t| matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif),
        source_store,
    )?;

    let main_block = parse_procedure_body(
        program,
        module_id,
        main_block,
        op_id_gen,
        interner,
        parent,
        source_store,
    )?;

    let main_conditional = ConditionalBlock {
        condition: main_condition,
        do_token,
        block: main_block,
        close_token,
    };

    let mut elif_blocks = Vec::new();

    while close_token.kind == TokenKind::Elif {
        let (elif_condition, do_token) = get_procedure_body(
            token_iter,
            tokens,
            keyword,
            keyword,
            |t| matches!(t, TokenKind::Do),
            source_store,
        )?;

        let elif_condition = parse_procedure_body(
            program,
            module_id,
            elif_condition,
            op_id_gen,
            interner,
            parent,
            source_store,
        )?;

        let (elif_block, cur_close_token) = get_procedure_body(
            token_iter,
            tokens,
            keyword,
            keyword,
            |t| matches!(t, TokenKind::End | TokenKind::Else | TokenKind::Elif),
            source_store,
        )?;

        let elif_block = parse_procedure_body(
            program,
            module_id,
            elif_block,
            op_id_gen,
            interner,
            parent,
            source_store,
        )?;

        let elif_conditional = ConditionalBlock {
            condition: elif_condition,
            do_token,
            block: elif_block,
            close_token: cur_close_token,
        };

        elif_blocks.push((close_token, elif_conditional));
        close_token = cur_close_token;
    }

    let mut else_block = if close_token.kind == TokenKind::Else {
        let (else_block, end_token) = get_procedure_body(
            token_iter,
            tokens,
            keyword,
            keyword,
            |t| matches!(t, TokenKind::End),
            source_store,
        )?;

        let else_block = parse_procedure_body(
            program,
            module_id,
            else_block,
            op_id_gen,
            interner,
            parent,
            source_store,
        )?;

        close_token = end_token;

        else_block
    } else {
        Vec::new()
    };

    // Normalize into an `if <cond> do <body> else <body> end` structure.
    while let Some((open_token, elif)) = elif_blocks.pop() {
        let if_op = Op::new(
            op_id_gen(),
            OpCode::If {
                open_token,
                end_token: elif.close_token,
                condition: elif,
                else_block,
            },
            open_token,
        );

        else_block = vec![if_op];
    }

    Ok(OpCode::If {
        open_token: keyword,
        condition: main_conditional,
        else_block,
        end_token: close_token,
    })
}

fn parse_while<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    op_id_gen: &mut impl FnMut() -> OpId,
    parent: Option<ProcedureId>,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<OpCode, ()> {
    let (condition, do_token) = get_procedure_body(
        token_iter,
        tokens,
        keyword,
        keyword,
        |t| matches!(t, TokenKind::Do),
        source_store,
    )?;

    let condition = parse_procedure_body(
        program,
        module_id,
        condition,
        op_id_gen,
        interner,
        parent,
        source_store,
    )?;

    let (body, end_token) = get_procedure_body(
        token_iter,
        tokens,
        keyword,
        do_token,
        |t| matches!(t, TokenKind::End),
        source_store,
    )?;

    let block = parse_procedure_body(
        program,
        module_id,
        body,
        op_id_gen,
        interner,
        parent,
        source_store,
    )?;

    Ok(OpCode::While {
        body: ConditionalBlock {
            do_token,
            condition,
            block,
            close_token: end_token,
        },
    })
}

fn parse_type_signature<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    source_store: &SourceStorage,
) -> Result<(Vec<PorthType>, SourceLocation), ()> {
    let (_, open_token) = expect_token(
        token_iter,
        "[",
        |k| k == TokenKind::SquareBracketOpen,
        name,
        interner,
        source_store,
    )?;

    let mut type_list = Vec::new();

    while token_iter.peek().map(|(_, t)| t.kind) == Some(TokenKind::Ident) {
        let (_, token) = token_iter.next().unwrap();

        let lexeme = interner.resolve_lexeme(token.lexeme);
        let typ = match lexeme {
            "u8" => PorthTypeKind::Int(IntWidth::I8),
            "u16" => PorthTypeKind::Int(IntWidth::I16),
            "u32" => PorthTypeKind::Int(IntWidth::I32),
            "u64" => PorthTypeKind::Int(IntWidth::I64),
            "ptr" => PorthTypeKind::Ptr,
            "bool" => PorthTypeKind::Bool,
            _ => {
                diagnostics::emit_error(
                    token.location,
                    format!("unknown type {lexeme}"),
                    Some(Label::new(token.location).with_color(Color::Red)),
                    None,
                    source_store,
                );

                return Err(());
            }
        };

        type_list.push(PorthType {
            kind: typ,
            location: token.location,
        })
    }

    let (_, close_token) = expect_token(
        token_iter,
        "]",
        |k| k == TokenKind::SquareBracketClosed,
        name,
        interner,
        source_store,
    )?;

    let signature_range = open_token.location.merge(close_token.location);

    Ok((type_list, signature_range))
}

fn parse_function_header<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: Option<ProcedureId>,
    source_store: &SourceStorage,
) -> Result<(Token, ProcedureId), ()> {
    let (entry_stack, entry_stack_location) =
        parse_type_signature(token_iter, interner, name, source_store)?;
    expect_token(
        token_iter,
        "to",
        |k| k == TokenKind::GoesTo,
        name,
        interner,
        source_store,
    )?;
    let (exit_stack, exit_stack_location) =
        parse_type_signature(token_iter, interner, name, source_store)?;

    let new_proc = program.new_procedure(
        name,
        module_id,
        ProcedureKind::Function(FunctionData::default()),
        parent,
        exit_stack,
        exit_stack_location,
        entry_stack,
        entry_stack_location,
    );

    let (_, is_token) = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        name,
        interner,
        source_store,
    )?;
    Ok((is_token, new_proc))
}

fn parse_memory_header<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: Option<ProcedureId>,
    source_store: &SourceStorage,
) -> Result<(Token, ProcedureId), ()> {
    let new_proc = program.new_procedure(
        name,
        module_id,
        ProcedureKind::Memory,
        parent,
        vec![PorthType {
            kind: PorthTypeKind::Int(IntWidth::I64),
            location: name.location,
        }],
        name.location,
        Vec::new(),
        name.location,
    );

    let (_, is_token) = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        name,
        interner,
        source_store,
    )?;
    Ok((is_token, new_proc))
}

fn parse_macro_header<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: Option<ProcedureId>,
    source_store: &SourceStorage,
) -> Result<(Token, ProcedureId), ()> {
    let new_proc = program.new_procedure(
        name,
        module_id,
        ProcedureKind::Macro,
        parent,
        Vec::new(),
        name.location,
        Vec::new(),
        name.location,
    );

    let (_, is_token) = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        name,
        interner,
        source_store,
    )?;
    Ok((is_token, new_proc))
}

fn parse_const_header<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: Option<ProcedureId>,
    source_store: &SourceStorage,
) -> Result<(Token, ProcedureId), ()> {
    let (exit_stack, exit_sig_location) =
        parse_type_signature(token_iter, interner, name, source_store)?;

    let new_proc = program.new_procedure(
        name,
        module_id,
        ProcedureKind::Const { const_val: None },
        parent,
        exit_stack,
        exit_sig_location,
        Vec::new(),
        name.location,
    );

    let (_, is_token) = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        name,
        interner,
        source_store,
    )?;
    Ok((is_token, new_proc))
}

fn parse_assert_header<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: Option<ProcedureId>,
    source_store: &SourceStorage,
) -> Result<(Token, ProcedureId), ()> {
    let new_proc = program.new_procedure(
        name,
        module_id,
        ProcedureKind::Assert,
        parent,
        vec![PorthType {
            kind: PorthTypeKind::Bool,
            location: name.location,
        }],
        name.location,
        Vec::new(),
        name.location,
    );

    let (_, is_token) = expect_token(
        token_iter,
        "is",
        |k| k == TokenKind::Is,
        name,
        interner,
        source_store,
    )?;

    Ok((is_token, new_proc))
}

fn parse_procedure<'a>(
    program: &mut Program,
    module_id: ModuleId,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    interner: &Interners,
    parent: Option<ProcedureId>,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let name_token = expect_token(
        token_iter,
        "ident",
        |k| k == TokenKind::Ident,
        keyword,
        interner,
        source_store,
    )
    .map(|(_, a)| a)?;

    let header_func = match keyword.kind {
        TokenKind::Proc => parse_function_header,
        TokenKind::Memory => parse_memory_header,
        TokenKind::Macro => parse_macro_header,
        TokenKind::Const => parse_const_header,
        TokenKind::Assert => parse_assert_header,
        _ => unreachable!(),
    };

    let (is_token, procedure_id) = header_func(
        program,
        module_id,
        token_iter,
        interner,
        name_token,
        parent,
        source_store,
    )?;

    let (body, end_token) = get_procedure_body(
        &mut *token_iter,
        tokens,
        keyword,
        is_token,
        |t| matches!(t, TokenKind::End),
        source_store,
    )?;

    let mut op_id = 0;
    let mut op_id_gen = || {
        let id = op_id;
        op_id += 1;
        OpId(id)
    };

    let mut body = parse_procedure_body(
        program,
        module_id,
        body,
        &mut op_id_gen,
        interner,
        Some(procedure_id),
        source_store,
    )?;

    let proc_header = program.get_proc_mut(procedure_id);

    if !proc_header.kind().is_macro() {
        // Makes later logic a bit easier if we always have a prologue and epilogue.
        body.insert(
            0,
            Op {
                code: OpCode::Prologue,
                id: op_id_gen(),
                token: name_token,
                expansions: Vec::new(),
            },
        );

        body.push(Op {
            code: OpCode::Epilogue,
            id: op_id_gen(),
            token: end_token,
            expansions: Vec::new(),
        });
    }

    *proc_header.body_mut() = body;
    proc_header.new_op_id = op_id;

    // stupid borrow checker...
    let id = proc_header.id();
    let _ = proc_header; // Need to discard the borrow;
    let proc_header = program.get_proc(id);

    if let Some(prev_def) = program
        .get_visible_symbol(proc_header, name_token.lexeme)
        .filter(|&f| f != procedure_id)
    {
        let prev_proc = program.get_proc(prev_def).name();

        diagnostics::emit_error(
            name_token.location,
            "multiple definitions of symbol",
            [
                Label::new(name_token.location)
                    .with_message("defined here")
                    .with_color(Color::Red),
                Label::new(prev_proc.location)
                    .with_message("also defined here")
                    .with_color(Color::Blue),
            ],
            None,
            source_store,
        );
        return Err(());
    }

    if let Some(parent_id) = parent {
        let parent_proc = program.get_proc_mut(parent_id);
        match (parent_proc.kind_mut(), keyword.kind) {
            (ProcedureKind::Function(pd), TokenKind::Const) => {
                pd.consts.insert(name_token.lexeme, procedure_id);
            }
            (ProcedureKind::Function(pd), TokenKind::Memory) => {
                pd.allocs.insert(name_token.lexeme, procedure_id);
            }
            // The other types aren't stored in the proc
            _ => {}
        }
    }

    Ok(())
}

pub(super) fn parse_module(
    program: &mut Program,
    module_id: ModuleId,
    tokens: &[Token],
    interner: &Interners,
    include_queue: &mut Vec<Token>,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    let mut had_error = false;
    let mut token_iter = tokens.iter().enumerate().peekable();

    while let Some((_, token)) = token_iter.next() {
        match token.kind {
            TokenKind::Assert
            | TokenKind::Const
            | TokenKind::Macro
            | TokenKind::Memory
            | TokenKind::Proc => {
                if parse_procedure(
                    program,
                    module_id,
                    &mut token_iter,
                    tokens,
                    *token,
                    interner,
                    None,
                    source_store,
                )
                .is_err()
                {
                    had_error = true;
                }
            }

            TokenKind::Include => {
                let (_, module_ident) = match expect_token(
                    &mut token_iter,
                    "ident",
                    |k| k == TokenKind::Ident,
                    *token,
                    interner,
                    source_store,
                ) {
                    Ok(ident) => ident,
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                };

                include_queue.push(module_ident);
            }

            _ => {
                diagnostics::emit_error(
                    token.location,
                    format!("top-level can only declared `const`, `include`, `macro` `memory` or `proc`, found `{:?}`", token.kind),
                    Some(Label::new(token.location).with_color(Color::Red).with_message("here")),
                    None,
                    source_store
                );

                had_error = true;
                continue;
            }
        }
    }

    had_error.not().then_some(()).ok_or(())
}
