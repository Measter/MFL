use std::fmt::Display;

use lasso::Spur;

use crate::{
    program::ItemId,
    source_file::{SourceLocation, Spanned},
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
    pub do_token: SourceLocation,
    pub body_block: Vec<Op>,
    pub end_token: SourceLocation,
}

#[derive(Debug, Clone)]
pub struct If {
    pub open_token: SourceLocation,
    pub condition: Vec<Op>,
    pub is_condition_terminal: bool,
    pub do_token: SourceLocation,
    pub then_block: Vec<Op>,
    pub is_then_terminal: bool,
    pub else_token: SourceLocation,
    pub else_block: Vec<Op>,
    pub is_else_terminal: bool,
    pub end_token: SourceLocation,
}

#[derive(Debug, Clone)]
pub struct UnresolvedIdent {
    pub path: Vec<Spanned<Spur>>,
    pub generic_params: Vec<UnresolvedType>,
}

#[derive(Debug, Clone)]
pub enum OpCode {
    Add,
    BitAnd,
    BitNot,
    BitOr,
    BitXor,
    CallFunction {
        item_id: ItemId,
    },
    Div,
    Dup {
        count: Spanned<u8>,
    },
    Drop {
        count: Spanned<u8>,
    },
    EmitStack(bool),
    Epilogue,
    Equal,
    ExtractArray {
        emit_array: bool,
    },
    ExtractStruct {
        emit_struct: bool,
        field_name: Spanned<Spur>,
    },
    Exit,
    If(Box<If>),
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    InsertArray {
        emit_array: bool,
    },
    InsertStruct {
        emit_struct: bool,
        field_name: Spanned<Spur>,
    },
    IsNull,
    Load,
    Memory {
        item_id: ItemId,
        global: bool,
    },
    Multiply,
    NotEq,
    Over {
        depth: Spanned<u8>,
    },
    PackArray {
        count: u8,
    },
    PackStruct {
        id: TypeId,
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
        generic_params: Vec<UnresolvedType>,
    },
    Rem,
    Return,
    Reverse {
        count: Spanned<u8>,
    },
    Rot {
        item_count: Spanned<u8>,
        direction: Direction,
        shift_count: Spanned<u8>,
    },
    ShiftLeft,
    ShiftRight,
    SizeOf(TypeId),
    Store,
    Subtract,
    Swap {
        count: Spanned<u8>,
    },
    SysCall {
        arg_count: Spanned<u8>,
    },
    Unpack,
    UnresolvedCast {
        unresolved_type: UnresolvedType,
    },
    UnresolvedIdent(UnresolvedIdent),
    UnresolvedPackStruct {
        unresolved_type: UnresolvedType,
    },
    UnresolvedSizeOf {
        unresolved_type: UnresolvedType,
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
    pub token: Spanned<Spur>,
}

impl Op {
    pub fn new(id: OpId, code: OpCode, token: Spanned<Spur>) -> Self {
        Self { id, code, token }
    }
}
