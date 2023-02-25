use lasso::Spur;
use smallvec::SmallVec;

use crate::{
    lexer::Token,
    program::{
        type_store::{IntWidth, Signedness, TypeId},
        ItemId, ModuleId,
    },
    source_file::SourceLocation,
};

#[derive(Debug, Clone, Copy)]
pub enum Direction {
    Left,
    Right,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntKind {
    Signed(i64),
    Unsigned(u64),
}

impl IntKind {
    pub fn to_signedness(self) -> Signedness {
        match self {
            IntKind::Signed(_) => Signedness::Signed,
            IntKind::Unsigned(_) => Signedness::Unsigned,
        }
    }

    // The cast has already been typechecked, so we know it's valid.
    pub fn cast(self, to_width: IntWidth, to_signed: Signedness) -> IntKind {
        match (self, to_signed) {
            (IntKind::Signed(v), Signedness::Signed) => IntKind::Signed(v & to_width.mask() as i64),
            (IntKind::Unsigned(v), Signedness::Unsigned) => IntKind::Unsigned(v & to_width.mask()),
            (IntKind::Signed(v), Signedness::Unsigned) => {
                IntKind::Unsigned((v & to_width.mask() as i64) as u64)
            }
            (IntKind::Unsigned(v), Signedness::Signed) => {
                IntKind::Signed((v & to_width.mask()) as i64)
            }
        }
    }
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
    CallFunction {
        module: ModuleId,
        item_id: ItemId,
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
        item_id: ItemId,
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
        value: IntKind,
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
        item_id: ItemId,
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
        item: Token,
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
    pub fn get_unsigned_binary_op(&self) -> fn(u64, u64) -> u64 {
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

            _ => {
                panic!("ICE: Attempted to get the binary_op of a {self:?}")
            }
        }
    }

    pub fn get_signed_binary_op(&self) -> fn(i64, i64) -> i64 {
        use OpCode::*;
        match self {
            Add => |a, b| a + b,
            BitOr => |a, b| a | b,
            BitAnd => |a, b| a & b,
            Equal => |a, b| (a == b) as i64,
            Greater => |a, b| (a > b) as i64,
            GreaterEqual => |a, b| (a >= b) as i64,
            Less => |a, b| (a < b) as i64,
            LessEqual => |a, b| (a <= b) as i64,
            Multiply => |a, b| a * b,
            NotEq => |a, b| (a != b) as i64,
            ShiftLeft => |a, b| a << b,
            ShiftRight => |a, b| a >> b,
            Subtract => |a, b| a - b,

            _ => {
                panic!("ICE: Attempted to get the binary_op of a {self:?}")
            }
        }
    }

    pub fn get_bool_binary_op(&self) -> fn(bool, bool) -> bool {
        use OpCode::*;
        #[allow(clippy::bool_comparison)]
        match self {
            Equal => |a, b| a == b,
            NotEq => |a, b| a != b,
            Greater => |a, b| a > b,
            GreaterEqual => |a, b| a >= b,
            Less => |a, b| a < b,
            LessEqual => |a, b| a <= b,

            _ => {
                panic!("ICE: Attempted to get the bool_op of a {self:?}")
            }
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct OpId(pub u32);

#[derive(Debug, Clone)]
pub struct Op {
    pub code: OpCode,
    pub id: OpId,
    pub token: Token,
    pub expansions: SmallVec<[SourceLocation; 2]>,
}

impl Op {
    pub fn new(id: OpId, code: OpCode, token: Token) -> Self {
        Self {
            id,
            code,
            token,
            expansions: SmallVec::new(),
        }
    }
}
