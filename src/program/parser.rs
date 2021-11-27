use std::{iter::Peekable, ops::Not};

use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{Token, TokenKind},
    opcode::{Op, OpCode},
    source_file::SourceStorage,
    type_check::{PorthType, PorthTypeKind},
};

use super::{FunctionData, ModuleId, ProcedureId, ProcedureKind, Program};

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
            diagnostics::emit(
                ident.location,
                format!(
                    "expected `{}`, found `{}`",
                    kind_str,
                    interner.resolve_lexeme(ident.lexeme)
                ),
                Some(Label::new(ident.location).with_color(Color::Red)),
                None,
                source_store,
            );
            Err(())
        }
        None => {
            diagnostics::emit(
                prev.location,
                "unexpected end of file",
                Some(Label::new(prev.location).with_color(Color::Red)),
                None,
                source_store,
            );
            Err(())
        }
    }
}

pub fn parse_procedure_body(
    program: &mut Program,
    module_id: ModuleId,
    tokens: &[Token],
    interner: &Interners,
    parent: Option<ProcedureId>,
    source_store: &SourceStorage,
) -> Result<Vec<Op>, ()> {
    let mut ops = Vec::new();
    let mut had_error = false;

    let mut token_iter = tokens.iter().enumerate().peekable();
    while let Some((_, token)) = token_iter.next() {
        let kind = match token.kind {
            TokenKind::Drop => OpCode::Drop,
            TokenKind::Dup(depth) => OpCode::Dup { depth },
            TokenKind::DupPair => OpCode::DupPair,
            TokenKind::Rot => OpCode::Rot,
            TokenKind::Swap => OpCode::Swap,

            TokenKind::Load(width) => OpCode::Load(width),
            TokenKind::Store(width) => OpCode::Store(width),

            TokenKind::Equal => OpCode::Equal,
            TokenKind::Greater => OpCode::Greater,
            TokenKind::GreaterEqual => OpCode::GreaterEqual,
            TokenKind::Less => OpCode::Less,
            TokenKind::LessEqual => OpCode::LessEqual,
            TokenKind::NotEqual => OpCode::NotEq,

            TokenKind::Ident => {
                let sub_token = if matches!(token_iter.peek(), Some((_, t)) if t.kind == TokenKind::ColonColon)
                {
                    let (_, colons) = token_iter.next().unwrap(); // Consume the ColonColon.
                    expect_token(
                        &mut token_iter,
                        "ident",
                        |k| k == TokenKind::Ident,
                        *colons,
                        interner,
                        source_store,
                    )
                    .ok()
                    .map(|(_, t)| t)
                } else {
                    None
                };

                OpCode::UnresolvedIdent {
                    token: *token,
                    sub_token,
                }
            }
            TokenKind::Integer(value) => OpCode::PushInt(value),
            TokenKind::String { id, is_c_str } => OpCode::PushStr { id, is_c_str },
            TokenKind::Here(id) => OpCode::PushStr {
                id,
                is_c_str: false,
            },
            TokenKind::ArgC => OpCode::ArgC,
            TokenKind::ArgV => OpCode::ArgV,

            TokenKind::While => OpCode::While { ip: usize::MAX },
            TokenKind::Do => OpCode::Do,

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
                diagnostics::emit(
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

            TokenKind::If => OpCode::If,
            TokenKind::Elif => OpCode::Elif {
                else_start: usize::MAX,
                end_ip: usize::MAX,
            },
            TokenKind::Else => OpCode::Else {
                else_start: usize::MAX,
                end_ip: usize::MAX,
            },
            TokenKind::End => OpCode::End,

            TokenKind::Minus => OpCode::Subtract,
            TokenKind::Plus => OpCode::Add,
            TokenKind::Star => OpCode::Multiply,
            TokenKind::DivMod => OpCode::DivMod,

            TokenKind::BitAnd => OpCode::BitAnd,
            TokenKind::BitNot => OpCode::BitNot,
            TokenKind::BitOr => OpCode::BitOr,
            TokenKind::ShiftLeft => OpCode::ShiftLeft,
            TokenKind::ShiftRight => OpCode::ShiftRight,

            TokenKind::CastBool => OpCode::CastBool,
            TokenKind::CastInt => OpCode::CastInt,
            TokenKind::CastPtr => OpCode::CastPtr,

            TokenKind::SysCall(id) => OpCode::SysCall(id),

            // These are only used as part of a sub-block. If they're found anywhere else,
            // it's an error.
            TokenKind::ColonColon
            | TokenKind::GoesTo
            | TokenKind::Is
            | TokenKind::SquareBracketClosed
            | TokenKind::SquareBracketOpen => {
                diagnostics::emit(
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

        ops.push(Op::new(kind, *token));
    }

    had_error.not().then(|| ops).ok_or(())
}

fn get_procedure_body<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    mut last_token: Token,
    source_store: &SourceStorage,
) -> Result<&'a [Token], ()> {
    let body_start_idx = match token_iter.peek() {
        Some((idx, _)) => *idx,
        None => {
            diagnostics::end_of_file(last_token.location, source_store);
            return Err(());
        }
    };

    // We need to keep track of block depth so we know which `end` token is ending the procedure.
    // We've already consumed the `is` token that opened the procedure body.
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
            diagnostics::emit(
                token.location,
                format!("cannot use {:?} inside a {:?}", token.kind, keyword.kind),
                Some(Label::new(token.location).with_color(Color::Red)),
                None,
                source_store,
            );
            had_error = true;
        }

        if token.kind.new_block() {
            block_depth += 1;
        } else if token.kind.end_block() {
            block_depth -= 1;
        }

        end_idx = idx;
        last_token = *token;

        if block_depth == 0 {
            break;
        }
    }

    if last_token.kind != TokenKind::End {
        diagnostics::end_of_file(last_token.location, source_store);
        return Err(());
    }

    had_error
        .not()
        .then(|| &tokens[body_start_idx..end_idx])
        .ok_or(())
}

fn parse_type_signature<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    source_store: &SourceStorage,
) -> Result<Vec<PorthType>, ()> {
    expect_token(
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
            "int" => PorthTypeKind::Int,
            "ptr" => PorthTypeKind::Ptr,
            "bool" => PorthTypeKind::Bool,
            _ => {
                diagnostics::emit(
                    token.location,
                    format!("unknown type {}", lexeme),
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

    expect_token(
        token_iter,
        "]",
        |k| k == TokenKind::SquareBracketClosed,
        name,
        interner,
        source_store,
    )?;

    Ok(type_list)
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
    let entry_stack = parse_type_signature(token_iter, interner, name, source_store)?;
    expect_token(
        token_iter,
        "to",
        |k| k == TokenKind::GoesTo,
        name,
        interner,
        source_store,
    )?;
    let exit_stack = parse_type_signature(token_iter, interner, name, source_store)?;

    let new_proc = program.new_procedure(
        name,
        module_id,
        ProcedureKind::Function(FunctionData::default()),
        parent,
        exit_stack,
        entry_stack,
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
            kind: PorthTypeKind::Int,
            location: name.location,
        }],
        Vec::new(),
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
        Vec::new(),
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
    let exit_stack = parse_type_signature(token_iter, interner, name, source_store)?;

    let new_proc = program.new_procedure(
        name,
        module_id,
        ProcedureKind::Const { const_val: None },
        parent,
        exit_stack,
        Vec::new(),
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
        Vec::new(),
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

    let body = get_procedure_body(&mut *token_iter, tokens, keyword, is_token, source_store)?;

    let mut body = parse_procedure_body(
        program,
        module_id,
        body,
        interner,
        Some(procedure_id),
        source_store,
    )?;

    let proc_header = program.get_proc_mut(procedure_id);

    if keyword.kind == TokenKind::Proc {
        body.insert(
            0,
            Op {
                code: OpCode::Prologue,
                token: name_token,
                expansions: Vec::new(),
            },
        );

        // Makes later logic a bit easier if we always have a return opcode.
        // TODO: Make this less dumb
        match body.last() {
            Some(op) => {
                if !matches!(op.code, OpCode::Return { .. }) {
                    let token = op.token;
                    let expansions = op.expansions.clone();
                    body.push(Op {
                        code: OpCode::Epilogue,
                        token,
                        expansions: expansions.clone(),
                    });
                    body.push(Op {
                        code: OpCode::Return { implicit: true },
                        token,
                        expansions,
                    });
                }
            }
            None => body.push(Op {
                code: OpCode::Return { implicit: true },
                token: proc_header.name(),
                expansions: Vec::new(),
            }),
        }
    }

    *proc_header.body_mut() = body;

    // stupid borrow checker...
    let id = proc_header.id();
    let _ = proc_header; // Need to discard the borrow;
    let proc_header = program.get_proc(id);

    if let Some(prev_def) = program
        .get_visible_symbol(proc_header, name_token.lexeme)
        .filter(|&f| f != procedure_id)
    {
        let prev_proc = program.get_proc(prev_def).name();

        diagnostics::emit(
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
                diagnostics::emit(
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

    had_error.not().then(|| ()).ok_or(())
}
