use lasso::Spur;

use crate::{
    lexer::Token,
    program::{
        type_store::{IntWidth, TypeId},
        ModuleId, ProcedureId,
    },
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
    ResolvedCast {
        id: TypeId,
    },
    ResolvedIdent {
        module: ModuleId,
        proc_id: ProcedureId,
    },
    ResolvedLoad {
        id: TypeId,
    },
    ResolvedStore {
        id: TypeId,
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
    UnresolvedLoad {
        kind_token: Token,
    },
    UnresolvedStore {
        kind_token: Token,
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
            | Memory { .. }
            | Over { .. }
            | Prologue
            | PushBool(_)
            | PushInt { .. }
            | PushStr { .. }
            | ResolvedCast { .. }
            | ResolvedIdent { .. }
            | ResolvedLoad { .. }
            | ResolvedStore { .. }
            | Return { .. }
            | Rot { .. }
            | Swap { .. }
            | SysCall { .. }
            | UnresolvedCast { .. }
            | UnresolvedIdent { .. }
            | UnresolvedLoad { .. }
            | UnresolvedStore { .. }
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
