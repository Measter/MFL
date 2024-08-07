use lasso::Spur;
use stores::source::{SourceLocation, Spanned};

use crate::stores::{
    block::BlockId,
    types::{BuiltinTypes, Float, FloatWidth, IntWidth, Integer, TypeId, TypeInfo, TypeKind},
    Stores,
};

use super::ItemId;

#[derive(Debug, Clone, Copy)]
pub enum Direction {
    Left,
    Right,
}

pub trait FieldKind {
    type GenericParamType;
}

impl FieldKind for TypeId {
    type GenericParamType = TypeId;
}

impl FieldKind for NameResolvedType {
    type GenericParamType = Spanned<Spur>;
}

impl FieldKind for UnresolvedType {
    type GenericParamType = Spanned<Spur>;
}

impl FieldKind for PartiallyResolvedType {
    type GenericParamType = Spanned<Spur>;
}

#[derive(Debug, Clone)]
pub struct StructDef<Kind: FieldKind> {
    pub name: Spanned<Spur>,
    pub fields: Vec<StructDefField<Kind>>,
    pub generic_params: Vec<Kind::GenericParamType>,
    pub is_union: bool,
}

#[derive(Debug, Clone)]
pub struct StructDefField<Kind> {
    pub name: Spanned<Spur>,
    pub kind: Spanned<Kind>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnresolvedType {
    Simple(UnresolvedIdent),
    Array(Box<UnresolvedType>, usize),
    MultiPointer(Box<UnresolvedType>),
    SinglePointer(Box<UnresolvedType>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NameResolvedType {
    SimpleCustom {
        id: ItemId,
        token: Spanned<Spur>,
    },
    SimpleBuiltin(BuiltinTypes),
    SimpleGenericParam(Spanned<Spur>),
    Array(Box<NameResolvedType>, usize),
    MultiPointer(Box<NameResolvedType>),
    SinglePointer(Box<NameResolvedType>),
    GenericInstance {
        id: ItemId,
        id_token: Spanned<Spur>,
        params: Vec<NameResolvedType>,
    },
}

impl NameResolvedType {
    pub fn item_id(&self) -> Option<ItemId> {
        match self {
            NameResolvedType::SimpleCustom { id, .. }
            | NameResolvedType::GenericInstance { id, .. } => Some(*id),
            NameResolvedType::SimpleBuiltin(_) | NameResolvedType::SimpleGenericParam(_) => None,
            NameResolvedType::Array(sub_type, _)
            | NameResolvedType::MultiPointer(sub_type)
            | NameResolvedType::SinglePointer(sub_type) => sub_type.item_id(),
        }
    }
}
#[derive(Debug, Clone)]
pub enum PartiallyResolvedType {
    Fixed(TypeId),
    GenericParamSimple(Spanned<Spur>),    // T
    GenericParamMultiPointer(Box<Self>),  // T*
    GenericParamSinglePointer(Box<Self>), // T&
    GenericParamArray(Box<Self>, usize),  // T[N]
    GenericStruct(ItemId, Vec<Self>),     // Bar(u32), Bar(T), Bar(Baz(T))
}

impl PartiallyResolvedType {
    pub fn match_generic_type(
        &self,
        stores: &Stores,
        param: Spur,
        input_type_info: TypeInfo,
    ) -> Option<TypeId> {
        match (self, input_type_info.kind) {
            (PartiallyResolvedType::GenericParamSimple(s), _) if s.inner == param => {
                Some(input_type_info.id)
            }
            (
                PartiallyResolvedType::GenericParamMultiPointer(t),
                TypeKind::MultiPointer(ptr_type),
            )
            | (
                PartiallyResolvedType::GenericParamSinglePointer(t),
                TypeKind::SinglePointer(ptr_type),
            ) => {
                let inner_info = stores.types.get_type_info(ptr_type);
                t.match_generic_type(stores, param, inner_info)
            }

            (PartiallyResolvedType::GenericParamArray(t, ..), TypeKind::Array { type_id, .. }) => {
                let inner_info = stores.types.get_type_info(type_id);
                t.match_generic_type(stores, param, inner_info)
            }

            (
                PartiallyResolvedType::GenericStruct(struct_id, params),
                TypeKind::GenericStructInstance(input_struct_id),
            ) if input_struct_id == *struct_id => {
                // We know the input struct is the same as the field struct.

                let input_struct_def = stores.types.get_struct_def(input_type_info.id);
                params
                    .iter()
                    .zip(&input_struct_def.generic_params)
                    .flat_map(|(p, itp)| {
                        let itp_info = stores.types.get_type_info(*itp);
                        p.match_generic_type(stores, param, itp_info)
                    })
                    .next()
                // None
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct WhileTokens {
    pub do_token: SourceLocation,
    pub end_token: SourceLocation,
}

#[derive(Debug, Clone, Copy)]
pub struct While {
    pub tokens: WhileTokens,
    pub condition: BlockId,
    pub body_block: BlockId,
}

#[derive(Debug, Copy, Clone)]
pub struct IfTokens {
    pub do_token: SourceLocation,
    pub else_token: SourceLocation,
    pub end_token: SourceLocation,
}

#[derive(Debug, Clone, Copy)]
pub struct If {
    pub tokens: IfTokens,
    pub condition: BlockId,
    pub then_block: BlockId,
    pub else_block: BlockId,
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

    pub fn get_bool_binary_op(self) -> fn(bool, bool) -> bool {
        use Arithmetic::*;
        match self {
            BitAnd => |a, b| a & b,
            BitOr => |a, b| a | b,
            BitXor => |a, b| a ^ b,
            _ => panic!("ICE: Unsupported binary op on Bool"),
        }
    }

    pub fn get_float_binary_op(self) -> fn(f64, f64) -> f64 {
        use Arithmetic::*;
        match self {
            Add => |a, b| a + b,
            Div => |a, b| a / b,
            Multiply => |a, b| a * b,
            Rem => |a, b| a % b,
            Subtract => |a, b| a - b,

            BitAnd | BitNot | BitOr | BitXor | ShiftLeft | ShiftRight => {
                panic!("ICE: Unsupported float_binary_op: {self:?}")
            }
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
        // We allow the bool comparison in here so the relation to the compare operation is more clear.

        use Compare::*;
        match self {
            Equal => |a, b| a == b,
            NotEq => |a, b| a != b,
            #[allow(clippy::bool_comparison)]
            Greater => |a, b| a > b,
            GreaterEqual => |a, b| a >= b,
            #[allow(clippy::bool_comparison)]
            Less => |a, b| a < b,
            LessEqual => |a, b| a <= b,
            IsNull => unimplemented!(),
        }
    }

    pub fn get_float_binary_op(self) -> fn(f64, f64) -> bool {
        use Compare::*;
        match self {
            Equal => |a, b| a == b,
            Less => |a, b| a < b,
            LessEqual => |a, b| a <= b,
            Greater => |a, b| a > b,
            GreaterEqual => |a, b| a >= b,
            NotEq => |a, b| a != b,
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
    If(If),
    While(While),
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
    FieldAccess {
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
    PushInt { width: IntWidth, value: Integer },
    PushFloat { width: FloatWidth, value: Float },
    PushStr { id: Spur },
}

#[derive(Debug, Clone, Eq)]
pub struct UnresolvedIdent {
    pub span: SourceLocation,
    pub is_from_root: bool,
    pub path: Vec<Spanned<Spur>>,
    pub generic_params: Vec<UnresolvedType>,
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
    Cast { id: UnresolvedType },
    Ident(UnresolvedIdent),
    SizeOf { id: UnresolvedType },
}

#[derive(Debug, Clone)]
pub enum NResolvedOp<T> {
    Cast { id: T },
    CallFunction { id: ItemId, generic_params: Vec<T> },
    Const { id: ItemId },
    PackStruct { id: T },
    Variable { id: ItemId, is_global: bool },
    SizeOf { id: T },
}

// These are the same shape, just differ in the resolve type.
pub type NameResolvedOp = NResolvedOp<NameResolvedType>;
pub type PartiallyResolvedOp = NResolvedOp<PartiallyResolvedType>;
pub type TypeResolvedOp = NResolvedOp<TypeId>;

#[derive(Debug, Clone)]
pub enum OpCode<T> {
    Basic(Basic),
    Complex(T),
}
