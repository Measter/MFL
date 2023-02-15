use lasso::Spur;

use crate::{
    lexer::Token,
    program::static_analysis::PorthTypeKind,
    program::{static_analysis::IntWidth, ModuleId, ProcedureId},
    source_file::SourceLocation,
};

#[derive(Debug, Clone, Copy)]
pub enum Direction {
    Left,
    Right,
}

#[derive(Debug, Clone)]
pub struct While {
    pub condition: Vec<Op>,
    pub do_token: Token,
    pub body_block: Vec<Op>,
    pub end_token: Token,
}

#[derive(Debug, Clone)]
pub struct If {
    pub open_token: Token,
    pub condition: Vec<Op>,
    pub do_token: Token,
    pub then_block: Vec<Op>,
    pub else_token: Token,
    pub else_block: Vec<Op>,
    pub end_token: Token,
}

#[derive(Debug, Clone)]
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
    DivMod,
    Dup {
        count: u8,
        count_token: Token,
    },
    Drop {
        count: u8,
        count_token: Token,
    },
    Epilogue,
    Equal,
    If(Box<If>),
    Less,
    LessEqual,
    Load {
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
        depth: u8,
        depth_token: Token,
    },
    Prologue,
    PushBool(bool),
    PushInt {
        width: IntWidth,
        value: u64,
    },
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
        item_count: u8,
        direction: Direction,
        shift_count: u8,
        item_count_token: Token,
        shift_count_token: Token,
    },
    ShiftLeft,
    ShiftRight,
    Store {
        kind: PorthTypeKind,
    },
    Subtract,
    Swap {
        count: u8,
        count_token: Token,
    },
    SysCall {
        arg_count: u8,
        arg_count_token: Token,
    },
    UnresolvedCast {
        kind_token: Token,
    },
    UnresolvedIdent {
        module: Option<Token>,
        proc: Token,
    },
    While(Box<While>),
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
            | DivMod
            | Drop { .. }
            | Dup { .. }
            | Epilogue
            | If(_)
            | Load { .. }
            | Memory { .. }
            | Over { .. }
            | Prologue
            | PushBool(_)
            | PushInt { .. }
            | PushStr { .. }
            | ResolvedIdent { .. }
            | Return { .. }
            | Rot { .. }
            | Store { .. }
            | Swap { .. }
            | SysCall { .. }
            | UnresolvedCast { .. }
            | UnresolvedIdent { .. }
            | While(_) => {
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
