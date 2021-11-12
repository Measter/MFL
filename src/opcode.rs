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
    CallProc(Spur),
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

            OpCode::CallProc(_) | OpCode::Return => todo!(),

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
            | Ident(_)
            | If
            | Include(_)
            | Load(_)
            | Memory { .. }
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
            | Ident(_)
            | If
            | Include(_)
            | Load(_)
            | Memory { .. }
            | Multiply
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
            | Ident(_)
            | If
            | Include { .. }
            | Load(_)
            | Memory { .. }
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
}

#[derive(Debug, Clone, Copy)]
pub struct AllocData {
    pub size: usize,
    pub offset: usize,
}

#[derive(Debug)]
pub struct Procedure {
    pub name: Token,
    pub body: Vec<Op>,
    pub allocs: HashMap<Spur, Procedure>,
    pub expected_exit_stack: Vec<PorthType>,
    pub expected_entry_stack: Vec<PorthType>,
    pub is_const: bool,
    pub is_global: bool,
    pub const_val: Option<u64>,
    pub alloc_size_and_offsets: HashMap<Spur, AllocData>,
    pub total_alloc_size: usize,
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
    current_scope: Option<&mut Procedure>,
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
        let is_nested_err = matches!(
            (keyword.kind, token.kind),
            (
                TokenKind::Proc,
                TokenKind::Proc | TokenKind::Macro | TokenKind::Const
            ) | (
                TokenKind::Memory | TokenKind::Const,
                TokenKind::Proc | TokenKind::Macro | TokenKind::Const | TokenKind::Memory,
            )
        );

        if is_nested_err {
            let diag = Diagnostic::error()
                .with_message(format!(
                    "cannot define a {:?} inside another {:?}",
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
    let body_ops = parse_token(program, body_tokens, interner, current_scope)?;

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
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
) -> Result<(Token, Procedure), Diagnostic<FileId>> {
    let expected_entry_stack = parse_type_signature(token_iter, interner, name)?;
    expect_token(token_iter, "to", |k| k == TokenKind::GoesTo, name, interner)?;
    let expected_exit_stack = parse_type_signature(token_iter, interner, name)?;

    let new_proc = Procedure {
        name,
        body: Vec::new(),
        allocs: HashMap::new(),
        expected_exit_stack,
        expected_entry_stack,
        is_const: false,
        is_global: false,
        const_val: None,
        alloc_size_and_offsets: HashMap::new(),
        total_alloc_size: 0,
    };

    let (_, is_token) = expect_token(token_iter, "is", |k| k == TokenKind::Is, name, interner)?;
    Ok((is_token, new_proc))
}

fn parse_memory_header<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
) -> Result<(Token, Procedure), Diagnostic<FileId>> {
    let new_proc = Procedure {
        name,
        body: Vec::new(),
        allocs: HashMap::new(),
        expected_exit_stack: vec![PorthType {
            kind: PorthTypeKind::Int,
            location: name.location,
        }],
        expected_entry_stack: Vec::new(),
        is_const: true,
        is_global: false,
        const_val: None,
        alloc_size_and_offsets: HashMap::new(),
        total_alloc_size: 0,
    };

    let (_, is_token) = expect_token(token_iter, "is", |k| k == TokenKind::Is, name, interner)?;
    Ok((is_token, new_proc))
}

fn parse_macro_header<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
) -> Result<(Token, Procedure), Diagnostic<FileId>> {
    let new_proc = Procedure {
        name,
        body: Vec::new(),
        allocs: HashMap::new(),
        expected_exit_stack: Vec::new(),
        expected_entry_stack: Vec::new(),
        is_const: false,
        is_global: false,
        const_val: None,
        alloc_size_and_offsets: HashMap::new(),
        total_alloc_size: 0,
    };

    let (_, is_token) = expect_token(token_iter, "is", |k| k == TokenKind::Is, name, interner)?;
    Ok((is_token, new_proc))
}

fn parse_const_header<'a>(
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    interner: &Interners,
    name: Token,
) -> Result<(Token, Procedure), Diagnostic<FileId>> {
    let expected_exit_stack = parse_type_signature(token_iter, interner, name)?;

    let new_proc = Procedure {
        name,
        body: Vec::new(),
        allocs: HashMap::new(),
        expected_exit_stack,
        expected_entry_stack: Vec::new(),
        is_const: true,
        is_global: false,
        const_val: None,
        alloc_size_and_offsets: HashMap::new(),
        total_alloc_size: 0,
    };

    let (_, is_token) = expect_token(token_iter, "is", |k| k == TokenKind::Is, name, interner)?;
    Ok((is_token, new_proc))
}

fn parse_sub_block<'a>(
    program: &mut Program,
    token_iter: &mut Peekable<impl Iterator<Item = (usize, &'a Token)>>,
    tokens: &'a [Token],
    keyword: Token,
    interner: &Interners,
    mut current_scope: Option<&mut Procedure>,
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

    let (is_token, mut proc_header) = match header_func(token_iter, interner, name_token) {
        Ok(proc) => proc,
        Err(diag) => return Err(vec![diag]),
    };

    let mut body = parse_sub_block_contents(
        program,
        &mut *token_iter,
        tokens,
        keyword,
        interner,
        Some(&mut proc_header),
        is_token,
    )?;

    if keyword.kind == TokenKind::Proc {
        // Makes later logic a bit easier if we always have a return opcode.
        match body.last() {
            Some(op) => {
                if op.code != OpCode::Return {
                    let ret_op = Op {
                        code: OpCode::Return,
                        token: op.token,
                        expansions: op.expansions.clone(),
                    };
                    body.push(ret_op);
                }
            }
            None => body.push(Op {
                code: OpCode::Return,
                token: proc_header.name,
                expansions: Vec::new(),
            }),
        }
    }

    proc_header.body = body;

    let namespaces = if let Some(proc) = current_scope.as_deref_mut() {
        [
            &program.macros,
            &proc.allocs,
            &program.procedures,
            &program.const_values,
        ]
    } else {
        [
            &program.macros,
            &program.global.allocs,
            &program.procedures,
            &program.const_values,
        ]
    };

    for namespace in namespaces {
        if let Some(prev_def) = namespace.get(&proc_header.name.lexeme) {
            let diag = Diagnostic::error()
                .with_message("multiple definitions of symbol")
                .with_labels(vec![
                    Label::primary(
                        proc_header.name.location.file_id,
                        proc_header.name.location.range(),
                    )
                    .with_message("defined here"),
                    Label::secondary(
                        prev_def.name.location.file_id,
                        prev_def.name.location.range(),
                    )
                    .with_message("also defined here"),
                ]);
            return Err(vec![diag]);
        }
    }

    let namespace = match (keyword.kind, current_scope.as_deref_mut()) {
        (TokenKind::Const, _) => &mut program.const_values,
        (TokenKind::Proc, _) => &mut program.procedures,
        (TokenKind::Macro, _) => &mut program.macros,
        (TokenKind::Memory, None) => &mut program.global.allocs,
        (TokenKind::Memory, Some(proc)) => &mut proc.allocs,
        _ => unreachable!(),
    };

    namespace.insert(proc_header.name.lexeme, proc_header);

    Ok(())
}

pub fn parse_token(
    program: &mut Program,
    tokens: &[Token],
    interner: &Interners,
    mut current_scope: Option<&mut Procedure>,
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
                if let Err(mut d) = parse_sub_block(
                    program,
                    &mut token_iter,
                    tokens,
                    *token,
                    interner,
                    current_scope.as_deref_mut(),
                ) {
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

                program.include_queue.push((path_token, literal));
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
    macros: &HashMap<Spur, Procedure>,
    const_values: &HashMap<Spur, Procedure>,
    global_allocs: &HashSet<Spur>,
    procedure_names: &HashSet<Spur>,
    ops: &[Op],
    is_global: bool,
    local_allocs: &HashMap<Spur, Procedure>,
) -> Result<(Vec<Op>, bool), Vec<Diagnostic<FileId>>> {
    let mut src_vec = ops.to_owned();
    let mut dst_vec = Vec::with_capacity(ops.len());
    let mut diags = Vec::new();

    // Keep making changes until we get no changes.
    let mut num_expansions = 0;
    let mut last_changed_macros = Vec::new();
    let mut failed_const_expansion = false;
    loop {
        let mut changed = false;
        last_changed_macros.clear();

        for op in src_vec.drain(..) {
            match op.code {
                OpCode::Ident(id) if macros.contains_key(&id) => {
                    changed = true;
                    let macro_proc = macros.get(&id).unwrap();
                    last_changed_macros.push(macro_proc.name);
                    dst_vec.extend(macro_proc.body.iter().map(|new_op| {
                        let mut new_op = new_op.clone();
                        new_op.expansions.push(op.token.location);
                        new_op.expansions.extend_from_slice(&op.expansions);
                        new_op
                    }));
                }

                OpCode::Ident(id) if !is_global && local_allocs.contains_key(&id) => {
                    dst_vec.push(Op {
                        code: OpCode::Memory {
                            name: id,
                            offset: 0,
                            global: false,
                        },
                        token: op.token,
                        expansions: op.expansions,
                    });
                }
                OpCode::Ident(id) if global_allocs.contains(&id) => {
                    dst_vec.push(Op {
                        code: OpCode::Memory {
                            name: id,
                            offset: 0,
                            global: true,
                        },
                        token: op.token,
                        expansions: op.expansions,
                    });
                }

                OpCode::Ident(id) if procedure_names.contains(&id) => dst_vec.push(Op {
                    code: OpCode::CallProc(id),
                    token: op.token,
                    expansions: op.expansions,
                }),
                OpCode::Ident(id) if const_values.contains_key(&id) => {
                    let val = const_values.get(&id).unwrap();
                    if let Some(val) = val.const_val {
                        dst_vec.push(Op {
                            code: OpCode::PushInt(val),
                            token: op.token,
                            expansions: op.expansions,
                        });
                    } else {
                        failed_const_expansion = true;
                        dst_vec.push(op);
                    }
                }
                OpCode::Ident(_) => {
                    let diag = Diagnostic::error()
                        .with_message("unknown macro or memory allocation")
                        .with_labels(vec![Label::primary(
                            op.token.location.file_id,
                            op.token.location.range(),
                        )]);
                    diags.push(diag);
                }
                _ => dst_vec.push(op),
            }
        }

        if !changed {
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
