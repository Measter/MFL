use lasso::Spur;
use variantly::Variantly;

use crate::{
    interners::Interners,
    lexer::Token,
    program::static_analysis::PorthTypeKind,
    program::{ModuleId, ProcedureId},
    source_file::{SourceLocation, SourceStorage},
    Width,
};

use self::optimizer_passes::PASSES;

mod optimizer_passes;

#[derive(Debug, Clone)]
pub struct ConditionalBlock {
    pub condition: Vec<Op>,
    pub do_token: Token,
    pub block: Vec<Op>,
    pub close_token: Token,
}

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
    Dup {
        depth: usize,
    },
    DupPair,
    Drop,
    Epilogue,
    Equal,
    If {
        open_token: Token,
        condition: ConditionalBlock,
        else_block: Vec<Op>,
        end_token: Token,
    },
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
        body: ConditionalBlock,
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
            | OpCode::Drop
            | OpCode::Load { .. } => 1,

            OpCode::Dup { depth } => depth + 1,

            OpCode::ArgC
            | OpCode::ArgV
            | OpCode::DupPair
            | OpCode::If { .. }
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
            | Drop
            | Dup { .. }
            | DupPair
            | Epilogue
            | If { .. }
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
            | Drop
            | Dup { .. }
            | DupPair
            | Epilogue
            | If { .. }
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
            | Drop
            | Dup { .. }
            | DupPair
            | Epilogue
            | If { .. }
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct OpId(pub usize);

#[derive(Debug, Clone)]
pub struct Op {
    pub code: OpCode,
    pub id: OpId,
    pub token: Token,
    pub expansions: Vec<SourceLocation>,
}

impl Op {
    pub fn new(id: OpId, code: OpCode, token: Token) -> Self {
        Self {
            id,
            code,
            token,
            expansions: Vec::new(),
        }
    }
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
                    OpCode::If {
                        condition,
                        else_block,
                        open_token,
                        end_token,
                    } => {
                        //
                        let new_main = ConditionalBlock {
                            condition: optimize(&condition.condition, interner, sources),
                            block: optimize(&condition.block, interner, sources),
                            do_token: condition.do_token,
                            close_token: condition.close_token,
                        };

                        let new_else_block = optimize(else_block, interner, sources);

                        dst_vec.push(Op {
                            code: OpCode::If {
                                condition: new_main,
                                else_block: new_else_block,
                                open_token: *open_token,
                                end_token: *end_token,
                            },
                            id: op.id,
                            token: op.token,
                            expansions: op.expansions.clone(),
                        });
                    }
                    OpCode::While { body } => {
                        let new_body = ConditionalBlock {
                            condition: optimize(&body.condition, interner, sources),
                            block: optimize(&body.block, interner, sources),
                            do_token: body.do_token,
                            close_token: body.close_token,
                        };

                        dst_vec.push(Op {
                            code: OpCode::While { body: new_body },
                            id: op.id,
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
