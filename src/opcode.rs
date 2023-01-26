use lasso::Spur;
use variantly::Variantly;

use crate::{
    lexer::Token,
    program::static_analysis::PorthTypeKind,
    program::{ModuleId, ProcedureId},
    source_file::SourceLocation,
    Width,
};

#[derive(Debug, Clone)]
pub struct ConditionalBlock {
    pub condition: Vec<Op>,
    pub do_token: Token,
    pub block: Vec<Op>,
    pub close_token: Token,
}

#[derive(Debug, Clone, Copy)]
pub enum Direction {
    Left,
    Right,
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
    Cast {
        kind: PorthTypeKind,
        kind_token: Token,
    },
    DivMod,
    Dup {
        count: usize,
        count_token: Token,
    },
    Drop {
        count: usize,
        count_token: Token,
    },
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
    Over {
        depth: usize,
        depth_token: Token,
    },
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
    Rot {
        item_count: usize,
        direction: Direction,
        shift_count: usize,
        item_count_token: Token,
        shift_count_token: Token,
    },
    ShiftLeft,
    ShiftRight,
    Store {
        width: Width,
        kind: PorthTypeKind,
    },
    Subtract,
    Swap {
        count: usize,
        count_token: Token,
    },
    SysCall {
        arg_count: usize,
        arg_count_token: Token,
    },
    UnresolvedIdent {
        module: Option<Token>,
        proc: Token,
    },
    While {
        body: ConditionalBlock,
    },
}

impl OpCode {
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
            | Cast { .. }
            | DivMod
            | Drop { .. }
            | Dup { .. }
            | Epilogue
            | If { .. }
            | Load { .. }
            | Memory { .. }
            | Over { .. }
            | Prologue
            | PushBool(_)
            | PushInt(_)
            | PushStr { .. }
            | ResolvedIdent { .. }
            | Return { .. }
            | Rot { .. }
            | Store { .. }
            | Swap { .. }
            | SysCall { .. }
            | UnresolvedIdent { .. }
            | While { .. } => {
                panic!("ICE: Attempted to get the binary_op of a {self:?}")
            }
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
