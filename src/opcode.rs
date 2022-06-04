use std::ops::Not;

use ariadne::{Color, Label};
use lasso::Spur;
use variantly::Variantly;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{Token, TokenKind},
    program::{ModuleId, ProcedureId},
    source_file::{SourceLocation, SourceStorage},
    type_check::PorthTypeKind,
    Width,
};

use self::optimizer_passes::PASSES;

mod optimizer_passes;

#[derive(Debug, Clone, Variantly)]
pub enum OpCode {
    Add,
    ArgC,
    ArgV,
    BitAnd,
    BitNot,
    BitOr,
    CallProc {
        module: ModuleId,
        proc_id: ProcedureId,
    },
    CastBool,
    CastInt,
    CastPtr,
    DivMod,
    Do,
    DoIf {
        end_ip: usize,
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
    Epilogue,
    Equal,
    If,
    Less,
    LessEqual,
    Load {
        width: Width,
        kind: PorthTypeKind,
    },
    Greater,
    GreaterEqual,
    Memory {
        module_id: ModuleId,
        proc_id: ProcedureId,
        offset: usize,
        global: bool,
    },
    Multiply,
    NotEq,
    Prologue,
    PushBool(bool),
    PushInt(u64),
    PushStr {
        id: Spur,
        is_c_str: bool,
    },
    ResolvedIdent {
        module: ModuleId,
        proc_id: ProcedureId,
    },
    Return,
    Rot,
    ShiftLeft,
    ShiftRight,
    Store {
        width: Width,
        kind: PorthTypeKind,
    },
    Subtract,
    Swap,
    SysCall(usize),
    UnresolvedIdent {
        module: Option<Token>,
        proc: Token,
    },
    While {
        condition: Vec<Op>,
        do_token: Token,
        body: Vec<Op>,
        end_token: Token,
    },
}

impl OpCode {
    pub fn pop_count(&self) -> usize {
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
            | OpCode::Store { .. }
            | OpCode::Swap
            | OpCode::Subtract => 2,

            OpCode::BitNot
            | OpCode::CastBool
            | OpCode::CastInt
            | OpCode::CastPtr
            | OpCode::Do
            | OpCode::DoIf { .. }
            | OpCode::Drop
            | OpCode::Load { .. } => 1,

            OpCode::Dup { depth } => depth + 1,

            OpCode::ArgC
            | OpCode::ArgV
            | OpCode::DupPair
            | OpCode::Elif { .. }
            | OpCode::Else { .. }
            | OpCode::End { .. }
            | OpCode::EndIf { .. }
            | OpCode::If
            | OpCode::Memory { .. }
            | OpCode::PushBool(_)
            | OpCode::PushInt(_)
            | OpCode::PushStr { .. }
            | OpCode::ResolvedIdent { .. }
            | OpCode::UnresolvedIdent { .. }
            | OpCode::While { .. } => 0,

            OpCode::CallProc { .. }
            | OpCode::Return { .. }
            | OpCode::Prologue
            | OpCode::Epilogue => {
                panic!("ICE: called pop_count on function opcodes")
            }

            OpCode::SysCall(a) => a + 1,
        }
    }

    // Used by the opcode optimizer to detect whether it can optimize Push-Push-Op.
    fn is_binary_op(&self) -> bool {
        use OpCode::*;
        match self {
            Add | BitAnd | BitOr | Equal | Greater | GreaterEqual | Less | LessEqual | Multiply
            | NotEq | ShiftLeft | ShiftRight | Subtract => true,

            ArgC
            | ArgV
            | BitNot
            | CallProc { .. }
            | CastBool
            | CastInt
            | CastPtr
            | DivMod
            | Do
            | DoIf { .. }
            | Drop
            | Dup { .. }
            | DupPair
            | Elif { .. }
            | Else { .. }
            | End { .. }
            | EndIf { .. }
            | Epilogue
            | If
            | Load { .. }
            | Memory { .. }
            | Prologue
            | PushBool(_)
            | PushInt(_)
            | PushStr { .. }
            | ResolvedIdent { .. }
            | Return { .. }
            | Rot
            | Store { .. }
            | Swap
            | SysCall(_)
            | UnresolvedIdent { .. }
            | While { .. } => false,
        }
    }

    fn is_boolean_op(&self) -> bool {
        use OpCode::*;
        match self {
            Equal | Greater | GreaterEqual | Less | LessEqual | NotEq => true,

            Add
            | ArgC
            | ArgV
            | BitAnd
            | BitNot
            | BitOr
            | CallProc { .. }
            | CastBool
            | CastInt
            | CastPtr
            | DivMod
            | Do
            | DoIf { .. }
            | Drop
            | Dup { .. }
            | DupPair
            | Elif { .. }
            | Else { .. }
            | End { .. }
            | EndIf { .. }
            | Epilogue
            | If
            | Load { .. }
            | Memory { .. }
            | Multiply
            | Prologue
            | PushBool(_)
            | PushInt(_)
            | PushStr { .. }
            | ResolvedIdent { .. }
            | Return { .. }
            | Rot
            | ShiftLeft
            | ShiftRight
            | Store { .. }
            | Subtract
            | Swap
            | SysCall(_)
            | UnresolvedIdent { .. }
            | While { .. } => false,
        }
    }

    pub fn get_binary_op(&self) -> fn(u64, u64) -> u64 {
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
            | CallProc { .. }
            | CastBool
            | CastInt
            | CastPtr
            | DivMod
            | Do
            | DoIf { .. }
            | Drop
            | Dup { .. }
            | DupPair
            | Elif { .. }
            | Else { .. }
            | End { .. }
            | EndIf { .. }
            | Epilogue
            | If
            | Load { .. }
            | Memory { .. }
            | Prologue
            | PushBool(_)
            | PushInt(_)
            | PushStr { .. }
            | ResolvedIdent { .. }
            | Return { .. }
            | Rot
            | Store { .. }
            | Swap
            | SysCall(_)
            | UnresolvedIdent { .. }
            | While { .. } => {
                panic!("ICE: Attempted to get the binary_op of a {:?}", self)
            }
        }
    }

    pub fn unwrap_memory(&self) -> (ModuleId, ProcedureId, usize, bool) {
        match self {
            Self::Memory {
                module_id: module,
                proc_id,
                offset,
                global,
            } => (*module, *proc_id, *offset, *global),
            _ => panic!("expected OpCode::Memory"),
        }
    }

    pub fn unwrap_dup(&self) -> usize {
        match self {
            OpCode::Dup { depth } => *depth,
            _ => panic!("expected OpCode::Dup"),
        }
    }

    pub fn unwrap_load(&self) -> (Width, PorthTypeKind) {
        match self {
            OpCode::Load { width, kind } => (*width, *kind),
            _ => panic!("expected Opcode::Load"),
        }
    }

    pub fn unwrap_store(&self) -> (Width, PorthTypeKind) {
        match self {
            OpCode::Store { width, kind } => (*width, *kind),
            _ => panic!("expected Opcode::Store"),
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
    pub fn new(code: OpCode, token: Token) -> Self {
        Self {
            code,
            token,
            expansions: Vec::new(),
        }
    }
}

struct JumpIpStack {
    ip: usize,
    kind: TokenKind,
    location: SourceLocation,
}

pub fn generate_jump_labels(ops: &mut [Op], source_store: &SourceStorage) -> Result<(), ()> {
    let mut jump_ip_stack: Vec<JumpIpStack> = Vec::new();
    // Stores the IPs of the Elif opcodes so we can update their end IPs when we encounter an End opcode.
    let mut if_blocks_stack_ips: Vec<Vec<usize>> = Vec::new();
    let mut had_error = false;

    for ip in 0..ops.len() {
        let op = &ops[ip];
        match op.code {
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
                        diagnostics::emit_error(
                            op.token.location,
                            "`elif` requires a preceding `if-do`",
                            Some(Label::new(op.token.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        had_error = true;
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
                        diagnostics::emit_error(
                            op.token.location,
                            "`else` requires a preceding `if-do`",
                            Some(Label::new(op.token.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        had_error = true;
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
                        kind: TokenKind::Elif | TokenKind::If,
                        ..
                    }) => ip,
                    _ => {
                        diagnostics::emit_error(
                            op.token.location,
                            "`do` requires a preceding `if` or `elif`",
                            Some(Label::new(op.token.location)),
                            None,
                            source_store,
                        );
                        had_error = true;
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
                        diagnostics::emit_error(
                            op.token.location,
                            "`end` requires a preceding `if-do`, `else`, or `while-do`",
                            Some(Label::new(op.token.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        had_error = true;
                        continue;
                    }
                };

                // Now we need to specialize our own type based on our source.
                match &mut ops[src_ip].code {
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
        diagnostics::emit_error(
            location,
            "unclosed `if`, `else`, or `while-do` block",
            Some(Label::new(location).with_color(Color::Red)),
            None,
            source_store,
        );
        had_error = true;
    }

    had_error.not().then(|| ()).ok_or(())
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
                match &op.code {
                    OpCode::While {
                        condition: condition_block,
                        do_token,
                        body: loop_block,
                        end_token,
                    } => {
                        dst_vec.push(Op {
                            code: OpCode::While {
                                condition: optimize(condition_block, interner, sources),
                                do_token: *do_token,
                                body: optimize(loop_block, interner, sources),
                                end_token: *end_token,
                            },
                            token: op.token,
                            expansions: op.expansions.clone(),
                        });
                    }
                    _ => {
                        dst_vec.push(op.clone());
                    }
                }

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
