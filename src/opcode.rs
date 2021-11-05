use std::collections::{HashMap, HashSet};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use lasso::Spur;
use variantly::Variantly;

use crate::{
    interners::Interners,
    lexer::{Token, TokenKind},
    source_file::{FileId, SourceLocation, SourceStorage},
    type_check::{PorthType, PorthTypeKind},
    Width,
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
    DoIf { end_ip: usize },
    DoWhile { end_ip: usize, condition_ip: usize },
    Dup { depth: usize },
    DupPair,
    Drop,
    Elif { else_start: usize, end_ip: usize },
    Else { else_start: usize, end_ip: usize },
    End,
    EndIf { ip: usize },
    EndWhile { condition_ip: usize, end_ip: usize },
    Equal,
    Ident(Spur),
    If,
    Include(Spur),
    Less,
    LessEqual,
    Load(Width),
    Greater,
    GreaterEqual,
    Memory { name: Spur, offset: usize },
    Multiply,
    NotEq,
    Print,
    PushBool(bool),
    PushInt(u64),
    PushStr { id: Spur, is_c_str: bool },
    Return,
    Rot,
    ShiftLeft,
    ShiftRight,
    Store(Width),
    Subtract,
    Swap,
    SysCall(usize),
    While { ip: usize },
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
            | OpCode::CallProc(_)
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

    pub fn unwrap_memory(self) -> (Spur, usize) {
        match self {
            Self::Memory { name, offset } => (name, offset),
            _ => panic!("expected OpCode::Memory"),
        }
    }
}

pub struct Procedure {
    pub name: Token,
    pub body: Vec<Op>,
    pub expected_exit_stack: Vec<PorthType>,
    pub expected_entry_stack: Vec<PorthType>,
    pub is_const: bool,
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

fn parse_sub_block<'a>(
    token_iter: &mut impl Iterator<Item = (usize, &'a Token)>,
    tokens: &'a [Token],
    keyword: Token,
    interner: &Interners,
    macros: &mut HashMap<Spur, (Token, Vec<Op>)>,
    static_allocs: &mut HashMap<Spur, Procedure>,
    procedures: &mut HashMap<Spur, Procedure>,
    include_list: &mut Vec<(Token, Spur)>,
) -> Result<(Token, Vec<Op>), Vec<Diagnostic<FileId>>> {
    let (ident_idx, ident_token) = match expect_token(
        token_iter,
        "ident",
        |k| k == TokenKind::Ident,
        keyword,
        interner,
    ) {
        Ok(a) => a,
        Err(diag) => return Err(vec![diag]),
    };

    let body_start_idx = ident_idx + 1;
    let mut block_depth = 1;
    let mut end_idx = body_start_idx;
    let mut last_token = ident_token;

    // We need to keep track of whether we're in an if or while block, because they
    // should be usable inside a macro block.
    for (idx, token) in token_iter {
        if keyword.kind == TokenKind::Proc && token.kind == TokenKind::Proc {
            let diag = Diagnostic::error()
                .with_message("cannot define a procedure inside another procedure")
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
    let body_ops = parse_token(
        body_tokens,
        interner,
        macros,
        static_allocs,
        procedures,
        include_list,
    )?;

    Ok((ident_token, body_ops))
}

pub fn parse_token(
    tokens: &[Token],
    interner: &Interners,
    macros: &mut HashMap<Spur, (Token, Vec<Op>)>,
    static_allocs: &mut HashMap<Spur, Procedure>,
    procedures: &mut HashMap<Spur, Procedure>,
    include_list: &mut Vec<(Token, Spur)>,
) -> Result<Vec<Op>, Vec<Diagnostic<FileId>>> {
    let mut ops = Vec::new();
    let mut diags = Vec::new();

    let mut token_iter = tokens.iter().enumerate();
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

            TokenKind::Macro => {
                let (name, body) = match parse_sub_block(
                    &mut token_iter,
                    tokens,
                    *token,
                    interner,
                    macros,
                    static_allocs,
                    procedures,
                    include_list,
                ) {
                    Ok(a) => a,
                    Err(mut e) => {
                        diags.append(&mut e);
                        continue;
                    }
                };

                if let Some((prev_name, _)) = macros.insert(name.lexeme, (name, body)) {
                    let diag = Diagnostic::error()
                        .with_message("macro defined multiple times")
                        .with_labels(vec![
                            Label::primary(name.location.file_id, name.location.range())
                                .with_message("defined here"),
                            Label::secondary(
                                prev_name.location.file_id,
                                prev_name.location.range(),
                            )
                            .with_message("also defined here"),
                        ]);
                    diags.push(diag);
                }

                continue;
            }
            TokenKind::Memory => {
                let (name, body) = match parse_sub_block(
                    &mut token_iter,
                    tokens,
                    *token,
                    interner,
                    macros,
                    static_allocs,
                    procedures,
                    include_list,
                ) {
                    Ok(a) => a,
                    Err(mut e) => {
                        diags.append(&mut e);
                        continue;
                    }
                };

                let new_alloc = Procedure {
                    name,
                    body,
                    expected_exit_stack: vec![PorthType {
                        kind: PorthTypeKind::Int,
                        location: name.location,
                    }],
                    expected_entry_stack: Vec::new(),
                    is_const: true,
                };

                if let Some(prev_def) = static_allocs.insert(name.lexeme, new_alloc) {
                    let diag = Diagnostic::error()
                        .with_message("multiple allocations defined with the same name")
                        .with_labels(vec![
                            Label::primary(name.location.file_id, name.location.range())
                                .with_message("defined here"),
                            Label::secondary(
                                prev_def.name.location.file_id,
                                prev_def.name.location.range(),
                            )
                            .with_message("also defined here"),
                        ]);
                    diags.push(diag);
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

                include_list.push((path_token, literal));
                OpCode::Include(literal)
            }
            TokenKind::Proc => {
                let (name, mut body) = match parse_sub_block(
                    &mut token_iter,
                    tokens,
                    *token,
                    interner,
                    macros,
                    static_allocs,
                    procedures,
                    include_list,
                ) {
                    Ok(a) => a,
                    Err(mut e) => {
                        diags.append(&mut e);
                        continue;
                    }
                };

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
                        token: name,
                        expansions: Vec::new(),
                    }),
                }

                let new_proc = Procedure {
                    name,
                    body,
                    expected_entry_stack: Vec::new(),
                    expected_exit_stack: Vec::new(),
                    is_const: false,
                };

                if let Some(prev_def) = procedures.insert(name.lexeme, new_proc) {
                    let diag = Diagnostic::error()
                        .with_message("procedure defined multiple times")
                        .with_labels(vec![
                            Label::primary(name.location.file_id, name.location.range())
                                .with_message("defined here"),
                            Label::secondary(
                                prev_def.name.location.file_id,
                                prev_def.name.location.range(),
                            )
                            .with_message("also defined here"),
                        ]);
                    diags.push(diag);
                }

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
    macros: &HashMap<Spur, (Token, Vec<Op>)>,
    static_allocs: &HashSet<Spur>,
    procudure_names: &HashSet<Spur>,
    ops: &[Op],
) -> Result<Vec<Op>, Vec<Diagnostic<FileId>>> {
    let mut src_vec = ops.to_owned();
    let mut dst_vec = Vec::with_capacity(ops.len());
    let mut diags = Vec::new();

    // Keep making changes until we get no changes.
    let mut num_expansions = 0;
    let mut last_changed_macros = Vec::new();
    loop {
        let mut changed = false;
        last_changed_macros.clear();

        for op in src_vec.drain(..) {
            match op.code {
                OpCode::Ident(id) if macros.contains_key(&id) => {
                    changed = true;
                    let (name, body) = macros.get(&id).unwrap();
                    last_changed_macros.push(*name);
                    dst_vec.extend(body.iter().map(|new_op| {
                        let mut new_op = new_op.clone();
                        new_op.expansions.push(op.token.location);
                        new_op.expansions.extend_from_slice(&op.expansions);
                        new_op
                    }));
                }
                OpCode::Ident(id) if static_allocs.contains(&id) => {
                    dst_vec.push(Op {
                        code: OpCode::Memory {
                            name: id,
                            offset: 0,
                        },
                        token: op.token,
                        expansions: op.expansions,
                    });
                }
                OpCode::Ident(id) if procudure_names.contains(&id) => dst_vec.push(Op {
                    code: OpCode::CallProc(id),
                    token: op.token,
                    expansions: op.expansions,
                }),
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

    diags.is_empty().then(|| dst_vec).ok_or(diags)
}
