use lasso::Spur;

use crate::{
    opcode::{Direction, IntKind, OpId, UnresolvedIdent},
    program::ItemId,
    source_file::{SourceLocation, Spanned},
    type_store::{IntWidth, TypeId, UnresolvedTypeIds, UnresolvedTypeTokens},
};

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

#[derive(Debug, Copy, Clone)]
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

#[derive(Debug, Copy, Clone)]
pub enum Compare {
    Equal,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    NotEq,
    IsNull,
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
        filed_name: Spanned<Spur>,
    },
    Load,
    PackArray {
        count: u8,
    },
    Store,
    Unpack,
}

#[derive(Debug, Copy, Clone)]
pub enum Trivial {
    Arithmetic(Arithmetic),
    Compare(Compare),
    Stack(Stack),
    Control(Control),
    Memory(Memory),

    PushBool(bool),
    PushInt { width: IntWidth, value: IntKind },
    PushStr { id: Spur, is_c_str: bool },
}

#[derive(Debug, Clone)]
pub enum UnresolvedOp {
    Cast { id: UnresolvedTypeTokens },
    Ident(UnresolvedIdent),
    If(Box<If<Op<Self>, IfTokens>>),
    PackStruct { id: UnresolvedTypeTokens },
    SizeOf { id: UnresolvedTypeTokens },
    While(Box<While<Op<Self>, WhileTokens>>),
}

#[derive(Debug, Clone)]
pub enum NameResolvedOp {
    Cast {
        id: UnresolvedTypeIds,
    },
    Ident {
        item_id: ItemId,
        generic_params: Option<Vec<UnresolvedTypeIds>>,
    },
    If(Box<If<Self>>),
    PackStruct {
        id: UnresolvedTypeIds,
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
    If(Box<If<Self>>),
    PackStruct { id: TypeId },
    Memory { id: ItemId, is_global: bool },
    SizeOf { id: TypeId },
    While(Box<While<Self>>),
}

#[derive(Debug, Clone)]
pub enum OpCode<T> {
    Basic(Trivial),
    Complex(T),
}

#[derive(Debug, Clone)]
pub struct Op<T> {
    pub code: OpCode<T>,
    pub id: OpId,
    pub token: Spanned<Spur>,
}
