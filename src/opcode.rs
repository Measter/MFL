use std::fmt::Display;

use lasso::Spur;
use smallvec::SmallVec;

use crate::{
    lexer::Token,
    program::ItemId,
    source_file::SourceLocation,
    type_store::{IntWidth, Signedness, TypeId, UnresolvedType},
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
            (IntKind::Signed(v), Signedness::Signed) if to_width == IntWidth::I64 => {
                IntKind::Signed(v)
            }
            (IntKind::Signed(v), Signedness::Signed) => {
                let (min, max) = to_width.bounds_signed().into_inner();
                let full_range = to_width.bounds_unsigned().into_inner().1 as i64;
                let v = if v < min {
                    v + full_range
                } else if v > max {
                    v - full_range
                } else {
                    v
                };
                IntKind::Signed(v)
            }

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
    pub is_condition_terminal: bool,
    pub do_token: Token,
    pub then_block: Vec<Op>,
    pub is_then_terminal: bool,
    pub else_token: Token,
    pub else_block: Vec<Op>,
    pub is_else_terminal: bool,
    pub end_token: Token,
}

#[derive(Debug, Clone, Copy)]
pub struct UnresolvedIdent {
    pub module: Option<Token>,
    pub item: Token,
}

#[derive(Debug, Clone)]
pub enum OpCode {
    Add,
    ArgC,
    ArgV,
    BitAnd,
    BitNot,
    BitOr,
    BitXor,
    CallFunction {
        item_id: ItemId,
    },
    Div,
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
    ExtractArray,
    If(Box<If>),
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    InsertArray,
    Load,
    Memory {
        item_id: ItemId,
        global: bool,
    },
    Multiply,
    NotEq,
    Over {
        depth: u8,
        depth_token: Token,
    },
    Pack {
        count: u8,
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
        item_id: ItemId,
    },
    Rem,
    Return,
    Reverse {
        count: u8,
        count_token: Token,
    },
    Rot {
        item_count: u8,
        direction: Direction,
        shift_count: u8,
        item_count_token: Token,
        shift_count_token: Token,
    },
    ShiftLeft,
    ShiftRight,
    Store,
    Subtract,
    Swap {
        count: u8,
        count_token: Token,
    },
    SysCall {
        arg_count: u8,
        arg_count_token: Token,
    },
    Unpack,
    UnresolvedCast {
        unresolved_type: UnresolvedType,
    },
    UnresolvedIdent(UnresolvedIdent),
    While(Box<While>),
}

impl OpCode {
    pub fn get_unsigned_binary_op(&self) -> fn(u64, u64) -> u64 {
        use OpCode::*;
        match self {
            Add => |a, b| a + b,
            BitOr => |a, b| a | b,
            BitAnd => |a, b| a & b,
            BitXor => |a, b| a ^ b,
            Div => |a, b| a / b,
            Equal => |a, b| (a == b) as u64,
            Greater => |a, b| (a > b) as u64,
            GreaterEqual => |a, b| (a >= b) as u64,
            Less => |a, b| (a < b) as u64,
            LessEqual => |a, b| (a <= b) as u64,
            Multiply => |a, b| a * b,
            NotEq => |a, b| (a != b) as u64,
            Rem => |a, b| a % b,
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
            BitXor => |a, b| a ^ b,
            Div => |a, b| a / b,
            Equal => |a, b| (a == b) as i64,
            Greater => |a, b| (a > b) as i64,
            GreaterEqual => |a, b| (a >= b) as i64,
            Less => |a, b| (a < b) as i64,
            LessEqual => |a, b| (a <= b) as i64,
            Multiply => |a, b| a * b,
            NotEq => |a, b| (a != b) as i64,
            Rem => |a, b| a % b,
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
            BitOr => |a, b| a | b,
            BitAnd => |a, b| a & b,
            BitXor => |a, b| a ^ b,
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

impl Display for OpId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Op")?;
        self.0.fmt(f)
    }
}

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
