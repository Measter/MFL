use std::fmt::Display;

use lasso::Spur;

use crate::{
    source_file::{SourceLocation, Spanned},
    type_store::{IntWidth, Integer, Signedness, TypeId, UnresolvedTypeIds, UnresolvedTypeTokens},
};

use super::ItemId;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct OpId(pub u32);

impl Display for OpId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Op")?;
        self.0.fmt(f)
    }
}

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
    pub fn cast(self, to: Integer) -> IntKind {
        match (self, to.signed) {
            (IntKind::Signed(v), Signedness::Signed) if to.width == IntWidth::I64 => {
                IntKind::Signed(v)
            }
            (IntKind::Signed(v), Signedness::Signed) => {
                let (min, max) = to.width.bounds_signed().into_inner();
                let full_range = to.width.bounds_unsigned().into_inner().1 as i64;
                let v = if v < min {
                    v + full_range
                } else if v > max {
                    v - full_range
                } else {
                    v
                };
                IntKind::Signed(v)
            }

            (IntKind::Unsigned(v), Signedness::Unsigned) => IntKind::Unsigned(v & to.width.mask()),

            (IntKind::Signed(v), Signedness::Unsigned) => {
                IntKind::Unsigned((v & to.width.mask() as i64) as u64)
            }
            (IntKind::Unsigned(v), Signedness::Signed) => {
                IntKind::Signed((v & to.width.mask()) as i64)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct TerminalBlock<T> {
    pub block: Vec<Op<T>>,
    pub is_terminal: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct WhileTokens {
    pub do_token: SourceLocation,
    pub end_token: SourceLocation,
}

#[derive(Debug, Clone)]
pub struct While<OpType, TokenType = ()> {
    pub tokens: TokenType,
    pub condition: TerminalBlock<OpType>,
    pub body_block: TerminalBlock<OpType>,
}

#[derive(Debug, Copy, Clone)]
pub struct IfTokens {
    pub open_token: SourceLocation,
    pub do_token: SourceLocation,
    pub else_token: SourceLocation,
    pub end_token: SourceLocation,
}

#[derive(Debug, Clone)]
pub struct If<OpType, TokenType = ()> {
    pub tokens: TokenType,
    pub condition: TerminalBlock<OpType>,
    pub then_block: TerminalBlock<OpType>,
    pub else_block: TerminalBlock<OpType>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Arithmetic {
    Add,
    BitAnd,
    BitNot,
    BitOr,
    BitXor,
    Div,
    Multiply,
    Rem,
    ShiftLeft,
    ShiftRight,
    Subtract,
}

impl Arithmetic {
    pub fn get_unsigned_binary_op(self) -> fn(u64, u64) -> u64 {
        use Arithmetic::*;
        match self {
            Add => |a, b| a + b,
            BitAnd => |a, b| a & b,
            BitOr => |a, b| a | b,
            BitXor => |a, b| a ^ b,
            Div => |a, b| a / b,
            Multiply => |a, b| a * b,
            Rem => |a, b| a % b,
            ShiftLeft => |a, b| a << b,
            ShiftRight => |a, b| a >> b,
            Subtract => |a, b| a - b,

            Arithmetic::BitNot => panic!("ICE: Tried to get binary_op of a BitNot"),
        }
    }

    pub fn get_signed_binary_op(self) -> fn(i64, i64) -> i64 {
        use Arithmetic::*;
        match self {
            Add => |a, b| a + b,
            BitAnd => |a, b| a & b,
            BitOr => |a, b| a | b,
            BitXor => |a, b| a ^ b,
            Div => |a, b| a / b,
            Multiply => |a, b| a * b,
            Rem => |a, b| a % b,
            ShiftLeft => |a, b| a << b,
            ShiftRight => |a, b| a >> b,
            Subtract => |a, b| a - b,

            Arithmetic::BitNot => panic!("ICE: Tried to get binary_op of a BitNot"),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Compare {
    Equal,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    NotEq,
    IsNull,
}

impl Compare {
    pub fn get_unsigned_binary_op(self) -> fn(u64, u64) -> u64 {
        use Compare::*;
        match self {
            Equal => |a, b| (a == b) as u64,
            Greater => |a, b| (a > b) as u64,
            GreaterEqual => |a, b| (a >= b) as u64,
            Less => |a, b| (a < b) as u64,
            LessEqual => |a, b| (a <= b) as u64,
            NotEq => |a, b| (a != b) as u64,
            IsNull => unimplemented!(),
        }
    }

    pub fn get_signed_binary_op(self) -> fn(i64, i64) -> i64 {
        use Compare::*;
        match self {
            Equal => |a, b| (a == b) as i64,
            Greater => |a, b| (a > b) as i64,
            GreaterEqual => |a, b| (a >= b) as i64,
            Less => |a, b| (a < b) as i64,
            LessEqual => |a, b| (a <= b) as i64,
            NotEq => |a, b| (a != b) as i64,
            IsNull => unimplemented!(),
        }
    }

    pub fn get_bool_binary_op(self) -> fn(bool, bool) -> bool {
        use Compare::*;
        match self {
            Equal => |a, b| a == b,
            NotEq => |a, b| a != b,
            Greater => |a, b| a > b,
            GreaterEqual => |a, b| a >= b,
            Less => |a, b| a < b,
            LessEqual => |a, b| a <= b,
            IsNull => unimplemented!(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Stack {
    Dup {
        count: Spanned<u8>,
    },
    Drop {
        count: Spanned<u8>,
    },
    Emit {
        show_labels: bool,
    },
    Over {
        depth: Spanned<u8>,
    },
    Reverse {
        count: Spanned<u8>,
    },
    Rotate {
        item_count: Spanned<u8>,
        direction: Direction,
        shift_count: Spanned<u8>,
    },
    Swap {
        count: Spanned<u8>,
    },
}

#[derive(Debug, Copy, Clone)]
pub enum Control {
    Epilogue,
    Exit,
    Prologue,
    Return,
    SysCall { arg_count: Spanned<u8> },
}

#[derive(Debug, Copy, Clone)]
pub enum Memory {
    ExtractArray {
        emit_array: bool,
    },
    ExtractStruct {
        emit_struct: bool,
        field_name: Spanned<Spur>,
    },
    InsertArray {
        emit_array: bool,
    },
    InsertStruct {
        emit_struct: bool,
        field_name: Spanned<Spur>,
    },
    Load,
    PackArray {
        count: u8,
    },
    Store,
    Unpack,
}

#[derive(Debug, Copy, Clone)]
pub enum Basic {
    Arithmetic(Arithmetic),
    Compare(Compare),
    Stack(Stack),
    Control(Control),
    Memory(Memory),

    PushBool(bool),
    PushInt { width: IntWidth, value: IntKind },
    PushStr { id: Spur, is_c_str: bool },
}

#[derive(Debug, Clone, Eq)]
pub struct UnresolvedIdent {
    pub span: SourceLocation,
    pub is_from_root: bool,
    pub path: Vec<Spanned<Spur>>,
    pub generic_params: Option<Vec<UnresolvedTypeTokens>>,
}

impl std::hash::Hash for UnresolvedIdent {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.is_from_root.hash(state);
        self.path.hash(state);
        self.generic_params.hash(state);
    }
}

impl PartialEq for UnresolvedIdent {
    fn eq(&self, other: &Self) -> bool {
        self.is_from_root == other.is_from_root
            && self.path == other.path
            && self.generic_params == other.generic_params
    }
}

#[derive(Debug, Clone)]
pub enum UnresolvedOp {
    Cast { id: UnresolvedTypeTokens },
    Ident(UnresolvedIdent),
    If(Box<If<Self, IfTokens>>),
    PackStruct { id: UnresolvedTypeTokens },
    SizeOf { id: UnresolvedTypeTokens },
    While(Box<While<Self, WhileTokens>>),
}

#[derive(Debug, Clone)]
pub enum NameResolvedOp {
    Cast {
        id: UnresolvedTypeIds,
    },
    CallFunction {
        id: ItemId,
        generic_params: Option<Vec<UnresolvedTypeIds>>,
    },
    Const {
        id: ItemId,
    },
    If(Box<If<Self>>),
    PackStruct {
        id: UnresolvedTypeIds,
    },
    Memory {
        id: ItemId,
        is_global: bool,
    },
    SizeOf {
        id: UnresolvedTypeIds,
    },
    While(Box<While<Self>>),
}

#[derive(Debug, Clone)]
pub enum TypeResolvedOp {
    Cast { id: TypeId },
    CallFunction { id: ItemId },
    Const { id: ItemId },
    If(Box<If<Self>>),
    PackStruct { id: TypeId },
    Memory { id: ItemId, is_global: bool },
    SizeOf { id: TypeId },
    While(Box<While<Self>>),
}

#[derive(Debug, Clone)]
pub enum OpCode<T> {
    Basic(Basic),
    Complex(T),
}

#[derive(Debug, Clone)]
pub struct Op<T> {
    pub code: OpCode<T>,
    pub id: OpId,
    pub token: Spanned<Spur>,
}

impl<T> Op<T> {
    pub fn new(id: OpId, code: OpCode<T>, token: Spanned<Spur>) -> Self {
        Self { id, code, token }
    }
}
