use std::{
    collections::{HashMap, HashSet},
    iter::Peekable,
};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use lasso::Spur;
use variantly::Variantly;

use crate::{
    interners::Interners,
    lexer::{Token, TokenKind},
    program::{ProcData, Procedure, ProcedureId, ProcedureKind},
    source_file::{FileId, SourceLocation, SourceStorage},
    type_check::{PorthType, PorthTypeKind},
    Program, Width,
};

use self::optimizer_passes::PASSES;

mod optimizer_passes;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Variantly)]
pub enum OpCode {
    Add,
    ArgC,
    ArgV,
    BitAnd,
    BitNot,
    BitOr,
    CallProc(ProcedureId),
    CastBool,
    CastInt,
    CastPtr,
    DivMod,
    Do,
    DoIf {
        end_ip: usize,
    },
    DoWhile {
        end_ip: usize,
        condition_ip: usize,
    },
    Dup {
        depth: usize,
    },
    DupPair,
    Drop,
    Elif {
        else_start: usize,
        end_ip: usize,
    },
    Else {
        else_start: usize,
        end_ip: usize,
    },
    End,
    EndIf {
        ip: usize,
    },
    EndWhile {
        condition_ip: usize,
        end_ip: usize,
    },
    Epilogue,
    Equal,
    Ident(Spur),
    If,
    Include(Spur),
    Less,
    LessEqual,
    Load(Width),
    Greater,
    GreaterEqual,
    Memory {
        name: Spur,
        offset: usize,
        global: bool,
    },
    Multiply,
    NotEq,
    Prologue,
    Print,
    PushBool(bool),
    PushInt(u64),
    PushStr {
        id: Spur,
        is_c_str: bool,
    },
    Return,
    Rot,
    ShiftLeft,
    ShiftRight,
    Store(Width),
    Subtract,
    Swap,
    SysCall(usize),
    While {
        ip: usize,
    },
}

impl OpCode {
    pub fn pop_count(self) -> usize {
        match self {
            OpCode::Rot => 3,

            OpCode::Add
            | OpCode::BitOr
            | OpCode::BitAnd
            | OpCode::DivMod
            | OpCode::Equal
            | OpCode::Greater
            | OpCode::GreaterEqual
            | OpCode::Less
            | OpCode::LessEqual
            | OpCode::Multiply
            | OpCode::NotEq
            | OpCode::ShiftLeft
            | OpCode::ShiftRight
            | OpCode::Store(_)
            | OpCode::Swap
            | OpCode::Subtract => 2,

            OpCode::BitNot
            | OpCode::CastBool
            | OpCode::CastInt
            | OpCode::CastPtr
            | OpCode::Do
            | OpCode::DoIf { .. }
            | OpCode::DoWhile { .. }
            | OpCode::Drop
            | OpCode::Load(_)
            | OpCode::Print => 1,

            OpCode::Dup { depth } => depth + 1,

            OpCode::ArgC
            | OpCode::ArgV
            | OpCode::DupPair
            | OpCode::Elif { .. }
            | OpCode::Else { .. }
            | OpCode::End { .. }
            | OpCode::EndIf { .. }
            | OpCode::EndWhile { .. }
            | OpCode::Ident(_)
            | OpCode::If
            | OpCode::Include(_)
            | OpCode::Memory { .. }
            | OpCode::PushBool(_)
            | OpCode::PushInt(_)
            | OpCode::PushStr { .. }
            | OpCode::While { .. } => 0,

            OpCode::CallProc(_) | OpCode::Return | OpCode::Prologue | OpCode::Epilogue => todo!(),

            OpCode::SysCall(a) => a + 1,
        }
    }

    pub fn is_const(self) -> bool {
        match self {
            OpCode::Add
            | OpCode::BitAnd
            | OpCode::BitNot
            | OpCode::BitOr
            | OpCode::CastBool
            | OpCode::CastInt
            | OpCode::CastPtr
            | OpCode::DivMod
            | OpCode::Do
            | OpCode::DoIf { .. }
            | OpCode::DoWhile { .. }
            | OpCode::Dup { .. }
            | OpCode::DupPair
            | OpCode::Drop
            | OpCode::Elif { .. }
            | OpCode::Else { .. }
            | OpCode::End
            | OpCode::EndIf { .. }
            | OpCode::EndWhile { .. }
            | OpCode::Epilogue
            | OpCode::Equal
            | OpCode::Ident(_)
            | OpCode::If
            | OpCode::Include(_)
            | OpCode::Less
            | OpCode::LessEqual
            | OpCode::Greater
            | OpCode::GreaterEqual
            | OpCode::Multiply
            | OpCode::NotEq
            | OpCode::Prologue
            | OpCode::PushBool(_)
            | OpCode::PushInt(_)
            | OpCode::PushStr { .. }
            | OpCode::Return
            | OpCode::Rot
            | OpCode::ShiftLeft
            | OpCode::ShiftRight
            | OpCode::Subtract
            | OpCode::Swap
            | OpCode::While { .. } => true,

            OpCode::ArgC
            | OpCode::ArgV
            | OpCode::CallProc(_)
            | OpCode::Load(_)
            | OpCode::Memory { .. }
            | OpCode::Print
            | OpCode::Store(_)
            | OpCode::SysCall(_) => false,
        }
    }

    // Used by the opcode optimizer to detect whether it can optimize Push-Push-Op.
    fn is_binary_op(self) -> bool {
        use OpCode::*;
        match self {
            Add | BitAnd | BitOr | Equal | Greater | GreaterEqual | Less | LessEqual | Multiply
            | NotEq | ShiftLeft | ShiftRight | Subtract => true,

            ArgC
            | ArgV
            | BitNot
            | CallProc(_)
            | CastBool
            | CastInt
            | CastPtr
            | DivMod
            | Do
            | DoIf { .. }
            | DoWhile { .. }
            | Drop
            | Dup { .. }
            | DupPair
            | Elif { .. }
            | Else { .. }
            | End { .. }
            | EndIf { .. }
            | EndWhile { .. }
            | Epilogue
            | Ident(_)
            | If
            | Include(_)
            | Load(_)
            | Memory { .. }
            | Prologue
            | Print
            | PushBool(_)
            | PushInt(_)
            | PushStr { .. }
            | Return
            | Rot
            | Store(_)
            | Swap
            | SysCall(_)
            | While { .. } => false,
        }
    }

    fn is_boolean_op(self) -> bool {
        use OpCode::*;
        match self {
            Equal | Greater | GreaterEqual | Less | LessEqual | NotEq => true,

            Add
            | ArgC
            | ArgV
            | BitAnd
            | BitNot
            | BitOr
            | CallProc(_)
            | CastBool
            | CastInt
            | CastPtr
            | DivMod
            | Do
            | DoIf { .. }
            | DoWhile { .. }
            | Drop
            | Dup { .. }
            | DupPair
            | Elif { .. }
            | Else { .. }
            | End { .. }
            | EndIf { .. }
            | EndWhile { .. }
            | Epilogue
            | Ident(_)
            | If
            | Include(_)
            | Load(_)
            | Memory { .. }
            | Multiply
            | Prologue
            | Print
            | PushBool(_)
            | PushInt(_)
            | PushStr { .. }
            | Return
            | Rot
            | ShiftLeft
            | ShiftRight
            | Store(_)
            | Subtract
            | Swap
            | SysCall(_)
            | While { .. } => false,
        }
    }

    fn get_binary_op(self) -> fn(u64, u64) -> u64 {
        use OpCode::*;
        match self {
            Add => |a, b| a + b,
            BitOr => |a, b| a | b,
            BitAnd => |a, b| a & b,
            Equal => |a, b| (a == b) as u64,
            Greater => |a, b| (a > b) as u64,
            GreaterEqual => |a, b| (a >= b) as u64,
            Less => |a, b| (a < b) as u64,
            LessEqual => |a, b| (a <= b) as u64,
            Multiply => |a, b| a * b,
            NotEq => |a, b| (a != b) as u64,
            ShiftLeft => |a, b| a << b,
            ShiftRight => |a, b| a >> b,
            Subtract => |a, b| a - b,

            ArgC
            | ArgV
            | BitNot
            | CallProc(_)
            | CastBool
            | CastInt
            | CastPtr
            | DivMod
            | Do
            | DoIf { .. }
            | DoWhile { .. }
            | Drop
            | Dup { .. }
            | DupPair
            | Elif { .. }
            | Else { .. }
            | End { .. }
            | EndIf { .. }
            | EndWhile { .. }
            | Epilogue
            | Ident(_)
            | If
            | Include { .. }
            | Load(_)
            | Memory { .. }
            | Prologue
            | Print
            | PushBool(_)
            | PushInt(_)
            | PushStr { .. }
            | Return
            | Rot
            | Store(_)
            | Swap
            | SysCall(_)
            | While { .. } => {
                panic!("ICE: Attempted to get the binary_op of a {:?}", self)
            }
        }
    }

    pub fn unwrap_memory(self) -> (Spur, usize, bool) {
        match self {
            Self::Memory {
                name,
                offset,
                global,
            } => (name, offset, global),
            _ => panic!("expected OpCode::Memory"),
        }
    }

    pub fn unwrap_dup(self) -> usize {
        match self {
            OpCode::Dup { depth } => depth,
            _ => panic!("expected OpCode::Dup"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Op {
    pub code: OpCode,
    pub token: Token,
    pub expansions: Vec<SourceLocation>,
}

impl Op {
    fn new(code: OpCode, token: Token) -> Self {
        Self {
            code,
            token,
            expansions: Vec::new(),
        }
    }
}

fn expect_token<'a>(
    tokens: &mut impl Iterator<Item = (usize, &'a Token)>,
    kind_str: &str,
    expected: fn(TokenKind) -> bool,
    prev: Token,
    interner: &Interners,
) -> Result<(usize, Token), Diagnostic<FileId>> {
    match tokens.next() {
        Some((idx, ident)) if expected(ident.kind) => Ok((idx, *ident)),
        Some((_, ident)) => {
            let diag = Diagnostic::error()
                .with_message(format!(
                    "expected {}, found '{}'",
                    kind_str,
                    interner.resolve_lexeme(ident.lexeme)
                ))
                .with_labels(vec![Label::primary(
                    ident.location.file_id,
                    ident.location.range(),
                )]);

            Err(diag)
        }
        None => {
            let diag = Diagnostic::error()
                .with_message("unexpected end of file")
                .with_labels(vec![Label::primary(
                    prev.location.file_id,
                    prev.location.range(),
                )]);

            Err(diag)
        }
    }
}

fn parse_sub_block_contents<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    interner: &Interners,
    parent: ProcedureId,
    mut last_token: Token,
) -> Result<Vec<Op>, Vec<Diagnostic<FileId>>> {
    let body_start_idx = match token_iter.peek() {
        Some((idx, _)) => *idx,
        None => {
            let diag = Diagnostic::error()
                .with_message("unexpected end of file")
                .with_labels(vec![Label::primary(
                    last_token.location.file_id,
                    last_token.location.range(),
                )]);

            return Err(vec![diag]);
        }
    };

    let mut block_depth = 1;
    let mut end_idx = body_start_idx;

    // We need to keep track of whether we're in an if or while block, because they
    // should be usable inside a macro block.
    for (idx, token) in token_iter {
        use TokenKind::*;
        #[allow(clippy::match_like_matches_macro)]
        let is_nested_err = match (keyword.kind, token.kind) {
            (Proc, Include | Proc | Macro) => true,
            (Memory | Const, Proc | Macro | Const | Memory | Include) => true,
            _ => false,
        };

        if is_nested_err {
            let diag = Diagnostic::error()
                .with_message(format!(
                    "cannot use {:?} inside a {:?}",
                    token.kind, keyword.kind
                ))
                .with_labels(vec![Label::primary(
                    token.location.file_id,
                    token.location.range(),
                )]);

            return Err(vec![diag]);
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
        let diag = Diagnostic::error()
            .with_message("unexpected end of file")
            .with_labels(vec![Label::primary(
                last_token.location.file_id,
                last_token.location.range(),
            )]);

        return Err(vec![diag]);
    }

    let body_tokens = &tokens[body_start_idx..end_idx];
    let body_ops = parse_token(program, body_tokens, interner, parent)?;

    Ok(body_ops)
}

fn parse_type_signature<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
) -> Result<Vec<PorthType>, Diagnostic<FileId>> {
    expect_token(
        token_iter,
        "[",
        |k| k == TokenKind::SquareBracketOpen,
        name,
        interner,
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
                let diag = Diagnostic::error()
                    .with_message(format!("unknown type {}", lexeme))
                    .with_labels(vec![Label::primary(
                        token.location.file_id,
                        token.location.range(),
                    )]);
                return Err(diag);
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
    )?;

    Ok(type_list)
}

fn parse_proc_header<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: ProcedureId,
) -> Result<(Token, ProcedureId), Diagnostic<FileId>> {
    let entry_stack = parse_type_signature(token_iter, interner, name)?;
    expect_token(token_iter, "to", |k| k == TokenKind::GoesTo, name, interner)?;
    let exit_stack = parse_type_signature(token_iter, interner, name)?;

    let new_proc = program.new_procedure(
        name,
        ProcedureKind::Proc(ProcData::default()),
        Some(parent),
        exit_stack,
        entry_stack,
    );

    let (_, is_token) = expect_token(token_iter, "is", |k| k == TokenKind::Is, name, interner)?;
    Ok((is_token, new_proc))
}

fn parse_memory_header<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: ProcedureId,
) -> Result<(Token, ProcedureId), Diagnostic<FileId>> {
    let new_proc = program.new_procedure(
        name,
        ProcedureKind::Memory,
        Some(parent),
        vec![PorthType {
            kind: PorthTypeKind::Int,
            location: name.location,
        }],
        Vec::new(),
    );

    let (_, is_token) = expect_token(token_iter, "is", |k| k == TokenKind::Is, name, interner)?;
    Ok((is_token, new_proc))
}

fn parse_macro_header<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: ProcedureId,
) -> Result<(Token, ProcedureId), Diagnostic<FileId>> {
    let new_proc = program.new_procedure(
        name,
        ProcedureKind::Macro,
        Some(parent),
        Vec::new(),
        Vec::new(),
    );

    let (_, is_token) = expect_token(token_iter, "is", |k| k == TokenKind::Is, name, interner)?;
    Ok((is_token, new_proc))
}

fn parse_const_header<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
    parent: ProcedureId,
) -> Result<(Token, ProcedureId), Diagnostic<FileId>> {
    let exit_stack = parse_type_signature(token_iter, interner, name)?;

    let new_proc = program.new_procedure(
        name,
        ProcedureKind::Const { const_val: None },
        Some(parent),
        exit_stack,
        Vec::new(),
    );

    let (_, is_token) = expect_token(token_iter, "is", |k| k == TokenKind::Is, name, interner)?;
    Ok((is_token, new_proc))
}

fn parse_sub_block<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    interner: &Interners,
    parent: ProcedureId,
) -> Result<(), Vec<Diagnostic<FileId>>> {
    let name_token = match expect_token(
        token_iter,
        "ident",
        |k| k == TokenKind::Ident,
        keyword,
        interner,
    ) {
        Ok((_, a)) => a,
        Err(diag) => return Err(vec![diag]),
    };

    let header_func = match keyword.kind {
        TokenKind::Proc => parse_proc_header,
        TokenKind::Memory => parse_memory_header,
        TokenKind::Macro => parse_macro_header,
        TokenKind::Const => parse_const_header,
        _ => unreachable!(),
    };

    let (is_token, proc_header_id) =
        match header_func(program, token_iter, interner, name_token, parent) {
            Ok(proc) => proc,
            Err(diag) => return Err(vec![diag]),
        };

    let mut body = parse_sub_block_contents(
        program,
        &mut *token_iter,
        tokens,
        keyword,
        interner,
        proc_header_id,
        is_token,
    )?;

    let proc_header = program.get_proc_mut(proc_header_id);

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
        match body.last() {
            Some(op) => {
                if op.code != OpCode::Return {
                    let token = op.token;
                    let expansions = op.expansions.clone();
                    body.push(Op {
                        code: OpCode::Epilogue,
                        token,
                        expansions: expansions.clone(),
                    });
                    body.push(Op {
                        code: OpCode::Return,
                        token,
                        expansions,
                    });
                }
            }
            None => body.push(Op {
                code: OpCode::Return,
                token: proc_header.name(),
                expansions: Vec::new(),
            }),
        }
    }

    *proc_header.body_mut() = body;
    if let Some(prev_def) = program
        .get_visible_symbol(proc_header_id, name_token.lexeme)
        .filter(|&f| f != proc_header_id)
    {
        let prev_proc = program.get_proc(prev_def).name();

        let diag = Diagnostic::error()
            .with_message("multiple definitions of symbol")
            .with_labels(vec![
                Label::primary(name_token.location.file_id, name_token.location.range())
                    .with_message("defined here"),
                Label::secondary(prev_proc.location.file_id, prev_proc.location.range())
                    .with_message("also defined here"),
            ]);
        return Err(vec![diag]);
    }

    let parent_proc = program.get_proc_mut(parent);
    match (parent_proc.kind_mut(), keyword.kind) {
        (ProcedureKind::Proc(pd), TokenKind::Const) => {
            pd.consts.insert(name_token.lexeme, proc_header_id);
        }
        (ProcedureKind::Proc(pd), TokenKind::Memory) => {
            pd.allocs.insert(name_token.lexeme, proc_header_id);
        }
        // The other types aren't stored in the proc
        _ => {}
    }

    Ok(())
}

pub fn parse_token(
    program: &mut Program,
    tokens: &[Token],
    interner: &Interners,
    parent: ProcedureId,
) -> Result<Vec<Op>, Vec<Diagnostic<FileId>>> {
    let mut ops = Vec::new();
    let mut diags = Vec::new();

    let mut token_iter = tokens.iter().enumerate().peekable();
    while let Some((_, token)) = token_iter.next() {
        let kind = match token.kind {
            TokenKind::Drop => OpCode::Drop,
            TokenKind::Print => OpCode::Print,
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

            TokenKind::Ident => OpCode::Ident(token.lexeme),
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

            TokenKind::Const | TokenKind::Macro | TokenKind::Memory | TokenKind::Proc => {
                if let Err(mut d) =
                    parse_sub_block(program, &mut token_iter, tokens, *token, interner, parent)
                {
                    diags.append(&mut d);
                }
                continue;
            }
            TokenKind::Include => {
                let (_, path_token) = match expect_token(
                    &mut token_iter,
                    "string",
                    |k| matches!(k, TokenKind::String { .. }),
                    *token,
                    interner,
                ) {
                    Ok(ident) => ident,
                    Err(diag) => {
                        diags.push(diag);
                        continue;
                    }
                };

                let literal = match path_token.kind {
                    TokenKind::String { id, .. } => id,
                    _ => unreachable!(),
                };

                program.add_include(path_token, literal);
                OpCode::Include(literal)
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
            TokenKind::GoesTo
            | TokenKind::Is
            | TokenKind::SquareBracketClosed
            | TokenKind::SquareBracketOpen => {
                let diag = Diagnostic::error()
                    .with_message(format!(
                        "unexpected token `{}` in input",
                        interner.resolve_lexeme(token.lexeme)
                    ))
                    .with_labels(vec![Label::primary(
                        token.location.file_id,
                        token.location.range(),
                    )]);
                diags.push(diag);
                continue;
            }
        };

        ops.push(Op::new(kind, *token));
    }

    diags.is_empty().then(|| ops).ok_or(diags)
}

struct JumpIpStack {
    ip: usize,
    kind: TokenKind,
    location: SourceLocation,
}

pub fn generate_jump_labels(ops: &mut [Op]) -> Result<(), Vec<Diagnostic<FileId>>> {
    let mut jump_ip_stack: Vec<JumpIpStack> = Vec::new();
    // Stores the IPs of the Elif opcodes so we can update their end IPs when we encounter an End opcode.
    let mut if_blocks_stack_ips: Vec<Vec<usize>> = Vec::new();
    let mut diags = Vec::new();

    for ip in 0..ops.len() {
        let op = &ops[ip];
        match op.code {
            OpCode::While { .. } => {
                jump_ip_stack.push(JumpIpStack {
                    ip,
                    kind: op.token.kind,
                    location: op.token.location,
                });
                // Update our own IP.
                match &mut ops[ip].code {
                    OpCode::While { ip: while_ip } => *while_ip = ip,
                    _ => unreachable!(),
                }
            }

            OpCode::If => {
                if_blocks_stack_ips.push(Vec::new());
                jump_ip_stack.push(JumpIpStack {
                    ip,
                    kind: op.token.kind,
                    location: op.token.location,
                })
            }
            OpCode::Elif { .. } => {
                let if_idx = match jump_ip_stack.pop() {
                    Some(JumpIpStack {
                        ip: if_idx,
                        kind: TokenKind::Do,
                        ..
                    }) => if_idx,
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message("`elif` requires a preceding `if-do`")
                            .with_labels(vec![Label::primary(
                                op.token.location.file_id,
                                op.token.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                let kind = op.token.kind;
                let location = op.token.location;

                // update our own IP.
                match &mut ops[ip].code {
                    OpCode::Elif { else_start, .. } => *else_start = ip,
                    _ => unreachable!(),
                };
                match &mut ops[if_idx].code {
                    OpCode::DoIf { end_ip } => *end_ip = ip,
                    OpCode::DoWhile { .. } => {
                        let while_token = &ops[if_idx].token;
                        let diag = Diagnostic::error()
                            .with_message("`elif` can only be used with `if` blocks")
                            .with_labels(vec![
                                Label::primary(location.file_id, location.range()),
                                Label::secondary(
                                    while_token.location.file_id,
                                    while_token.location.range(),
                                )
                                .with_message("opened here"),
                            ]);
                        diags.push(diag);
                        continue;
                    }
                    _ => unreachable!(),
                };

                if_blocks_stack_ips.last_mut().unwrap().push(ip);
                jump_ip_stack.push(JumpIpStack { ip, kind, location });
            }
            OpCode::Else { .. } => {
                let if_idx = match jump_ip_stack.pop() {
                    Some(JumpIpStack {
                        ip: if_idx,
                        kind: TokenKind::Do,
                        ..
                    }) => if_idx,
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message("`else` requires a preceding `if-do`")
                            .with_labels(vec![Label::primary(
                                op.token.location.file_id,
                                op.token.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                let kind = op.token.kind;
                let location = op.token.location;

                // Update our own IP.
                match &mut ops[ip].code {
                    OpCode::Else { else_start, .. } => *else_start = ip,
                    _ => unreachable!(),
                }
                match &mut ops[if_idx].code {
                    OpCode::DoIf { end_ip } => *end_ip = ip,
                    _ => unreachable!(),
                }

                jump_ip_stack.push(JumpIpStack { ip, kind, location });
            }

            OpCode::Do => {
                let src_ip = match jump_ip_stack.pop() {
                    Some(JumpIpStack {
                        ip,
                        kind: TokenKind::Elif | TokenKind::If | TokenKind::While,
                        ..
                    }) => ip,
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message("`do` requires a preceding `if`, `elif` or `while`")
                            .with_labels(vec![Label::primary(
                                op.token.location.file_id,
                                op.token.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                jump_ip_stack.push(JumpIpStack {
                    ip,
                    kind: op.token.kind,
                    location: op.token.location,
                });

                // Now we need to specialize our own type based on our source.
                match &mut ops[src_ip].code {
                    OpCode::While { ip: condition_ip } => {
                        ops[ip].code = OpCode::DoWhile {
                            end_ip: usize::MAX,
                            condition_ip: *condition_ip,
                        };
                    }
                    OpCode::Elif { .. } | OpCode::If => {
                        ops[ip].code = OpCode::DoIf { end_ip: usize::MAX }
                    }
                    _ => unreachable!(),
                }
            }

            OpCode::End { .. } => {
                let src_ip = match jump_ip_stack.pop() {
                    Some(JumpIpStack {
                        ip,
                        kind: TokenKind::Else | TokenKind::Do,
                        ..
                    }) => ip,
                    _ => {
                        let diag = Diagnostic::error()
                            .with_message(
                                "`end` requires a preceding `if-do`, `else`, or `while-do`",
                            )
                            .with_labels(vec![Label::primary(
                                op.token.location.file_id,
                                op.token.location.range(),
                            )]);
                        diags.push(diag);
                        continue;
                    }
                };

                // Now we need to specialize our own type based on our source.
                match &mut ops[src_ip].code {
                    OpCode::DoWhile {
                        end_ip,
                        condition_ip,
                    } => {
                        *end_ip = ip;
                        ops[ip].code = OpCode::EndWhile {
                            condition_ip: *condition_ip,
                            end_ip: ip,
                        };
                    }
                    OpCode::DoIf { end_ip } | OpCode::Else { end_ip, .. } => {
                        *end_ip = ip;
                        ops[ip].code = OpCode::EndIf { ip };

                        // Update any Elifs in the block.
                        for elif_ip in if_blocks_stack_ips.pop().unwrap() {
                            match &mut ops[elif_ip].code {
                                OpCode::Elif { end_ip, .. } => *end_ip = ip,
                                _ => unreachable!(),
                            }
                        }
                    }
                    _ => unreachable!(),
                }
            }

            _ => {}
        }
    }

    while let Some(JumpIpStack { location, .. }) = jump_ip_stack.pop() {
        let diag = Diagnostic::error()
            .with_message("unclosed `if`, `else`, or `while-do` block")
            .with_labels(vec![Label::primary(location.file_id, location.range())]);
        diags.push(diag);
    }

    diags.is_empty().then(|| ()).ok_or(diags)
}

pub fn optimize(ops: &[Op], interner: &mut Interners, sources: &SourceStorage) -> Vec<Op> {
    let mut src_vec = ops.to_owned();
    let mut dst_vec: Vec<Op> = Vec::with_capacity(ops.len());

    // Keep making passes until we get no changes.
    loop {
        let mut src = src_vec.as_slice();
        let mut changed = false;

        while !src.is_empty() {
            if let Some((ops, xs)) = PASSES
                .iter()
                .filter_map(|pass| pass(src, interner, sources))
                .next()
            {
                dst_vec.extend(ops);
                src = xs;
                changed = true;
            } else if let [op, xs @ ..] = src {
                dst_vec.push(op.clone());
                src = xs;
            }
        }

        if !changed {
            break;
        }

        src_vec.clear();
        std::mem::swap(&mut src_vec, &mut dst_vec);
    }

    dst_vec
}

pub fn expand_includes(included_files: &HashMap<Spur, Vec<Op>>, ops: &[Op]) -> Vec<Op> {
    let mut src_vec = ops.to_owned();
    let mut dst_vec = Vec::with_capacity(ops.len());
    let mut already_included = HashSet::new();

    loop {
        let mut changed = false;

        for op in src_vec.drain(..) {
            match op.code {
                OpCode::Include(id) => {
                    changed = true;
                    if !already_included.contains(&id) {
                        dst_vec.extend_from_slice(&included_files[&id]);
                        already_included.insert(id);
                    }
                }
                _ => dst_vec.push(op),
            }
        }

        if !changed {
            break;
        }

        std::mem::swap(&mut src_vec, &mut dst_vec);
    }

    dst_vec
}

pub fn expand_sub_blocks(
    program: &Program,
    interner: &Interners,
    proc: &Procedure,
) -> Result<(Vec<Op>, bool), Vec<Diagnostic<FileId>>> {
    let mut src_vec = proc.body().to_owned();
    let mut dst_vec = Vec::with_capacity(src_vec.len());
    let mut diags = Vec::new();

    // Keep making changes until we get no changes.
    let mut num_expansions = 0;
    let mut last_changed_macros = Vec::new();
    let mut failed_const_expansion = false;
    loop {
        let mut expanded_macro = false;
        last_changed_macros.clear();

        for op in src_vec.drain(..) {
            let ident_id = match op.code {
                OpCode::Ident(id) => id,
                _ => {
                    dst_vec.push(op);
                    continue;
                }
            };

            let found_proc_id = match proc.get_visible_symbol(ident_id) {
                Some(id) => id,
                None => {
                    let diag = Diagnostic::error()
                        .with_message(format!(
                            "unknown symbol `{}`",
                            interner.resolve_lexeme(ident_id)
                        ))
                        .with_labels(vec![Label::primary(
                            op.token.location.file_id,
                            op.token.location.range(),
                        )]);
                    diags.push(diag);
                    continue;
                }
            };

            let found_proc = if found_proc_id == proc.id() {
                proc
            } else {
                program.get_proc(found_proc_id)
            };

            match found_proc.kind() {
                ProcedureKind::Macro => {
                    expanded_macro = true;
                    last_changed_macros.push(found_proc.name());
                    dst_vec.extend(found_proc.body().iter().map(|new_op| {
                        let mut new_op = new_op.clone();
                        new_op.expansions.push(op.token.location);
                        new_op.expansions.extend_from_slice(&op.expansions);
                        new_op
                    }));
                }
                ProcedureKind::Const { const_val: None } => {
                    failed_const_expansion = true;
                    dst_vec.push(op);
                }
                ProcedureKind::Const {
                    const_val: Some(val),
                } => dst_vec.push(Op {
                    code: OpCode::PushInt(*val),
                    token: op.token,
                    expansions: op.expansions,
                }),

                ProcedureKind::Memory => {
                    dst_vec.push(Op {
                        code: OpCode::Memory {
                            name: ident_id,
                            offset: 0,
                            global: found_proc.parent() == Some(program.top_level_proc_id()),
                        },
                        token: op.token,
                        expansions: op.expansions,
                    });
                }
                ProcedureKind::Proc(_) => {
                    dst_vec.push(Op {
                        code: OpCode::CallProc(found_proc_id),
                        token: op.token,
                        expansions: op.expansions,
                    });
                }
            }
        }

        if !expanded_macro {
            break;
        }

        if num_expansions > 128 {
            let mut labels = Vec::new();

            for mac in last_changed_macros {
                labels.push(Label::primary(mac.location.file_id, mac.location.range()));
            }

            let diag = Diagnostic::error()
                .with_message("depth of macro expansion exceeded 128")
                .with_labels(labels);

            diags.push(diag);
            break;
        }

        num_expansions += 1;

        std::mem::swap(&mut src_vec, &mut dst_vec);
    }

    diags
        .is_empty()
        .then(|| (dst_vec, failed_const_expansion))
        .ok_or(diags)
}
