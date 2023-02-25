use std::ops::RangeInclusive;

use ariadne::{Color, Label};
use hashbrown::HashMap;
use intcast::IntCast;
use lasso::Spur;

use crate::{diagnostics, interners::Interners, lexer::Token, source_file::SourceStorage};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(u16);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntWidth {
    I8,
    I16,
    I32,
    I64,
}

impl IntWidth {
    pub fn name(self, sign: Signedness) -> &'static str {
        match (self, sign) {
            (IntWidth::I8, Signedness::Signed) => "s8",
            (IntWidth::I16, Signedness::Signed) => "s16",
            (IntWidth::I32, Signedness::Signed) => "s32",
            (IntWidth::I64, Signedness::Signed) => "s64",
            (IntWidth::I8, Signedness::Unsigned) => "u8",
            (IntWidth::I16, Signedness::Unsigned) => "u16",
            (IntWidth::I32, Signedness::Unsigned) => "u32",
            (IntWidth::I64, Signedness::Unsigned) => "u64",
        }
    }

    pub fn mask(self) -> u64 {
        match self {
            IntWidth::I8 => u8::MAX.to_u64(),
            IntWidth::I16 => u16::MAX.to_u64(),
            IntWidth::I32 => u32::MAX.to_u64(),
            IntWidth::I64 => u64::MAX.to_u64(),
        }
    }

    pub fn bounds_unsigned(self) -> RangeInclusive<u64> {
        match self {
            IntWidth::I8 => 0..=u8::MAX.to_u64(),
            IntWidth::I16 => 0..=u16::MAX.to_u64(),
            IntWidth::I32 => 0..=u32::MAX.to_u64(),
            IntWidth::I64 => 0..=u64::MAX.to_u64(),
        }
    }

    pub fn bounds_signed(self) -> RangeInclusive<i64> {
        match self {
            IntWidth::I8 => i8::MIN.to_i64()..=i8::MAX.to_i64(),
            IntWidth::I16 => i16::MIN.to_i64()..=i16::MAX.to_i64(),
            IntWidth::I32 => i32::MIN.to_i64()..=i32::MAX.to_i64(),
            IntWidth::I64 => i64::MIN.to_i64()..=i64::MAX.to_i64(),
        }
    }

    pub fn bit_width(self) -> u8 {
        match self {
            IntWidth::I8 => 8,
            IntWidth::I16 => 16,
            IntWidth::I32 => 32,
            IntWidth::I64 => 64,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Signedness {
    Signed,
    Unsigned,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeKind {
    Integer { width: IntWidth, signed: Signedness },
    Pointer,
    Bool,
}

#[derive(Debug, Clone, Copy)]
pub enum BuiltinTypes {
    U8,
    U16,
    U32,
    U64,
    S8,
    S16,
    S32,
    S64,
    Bool,
    Pointer,
}

impl From<(Signedness, IntWidth)> for BuiltinTypes {
    fn from(value: (Signedness, IntWidth)) -> Self {
        match value {
            (Signedness::Signed, IntWidth::I8) => BuiltinTypes::S8,
            (Signedness::Signed, IntWidth::I16) => BuiltinTypes::S16,
            (Signedness::Signed, IntWidth::I32) => BuiltinTypes::S32,
            (Signedness::Signed, IntWidth::I64) => BuiltinTypes::S64,
            (Signedness::Unsigned, IntWidth::I8) => BuiltinTypes::U8,
            (Signedness::Unsigned, IntWidth::I16) => BuiltinTypes::U16,
            (Signedness::Unsigned, IntWidth::I32) => BuiltinTypes::U32,
            (Signedness::Unsigned, IntWidth::I64) => BuiltinTypes::U64,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TypeInfo {
    pub id: TypeId,
    pub name: Spur,
    pub kind: TypeKind,
    pub width: u8,
}

#[derive(Debug)]
pub struct TypeStore {
    kinds: HashMap<TypeId, TypeInfo>,
    name_map: HashMap<Spur, TypeId>,
    builtins: [TypeId; 10],
}

impl TypeStore {
    pub fn new() -> Self {
        Self {
            kinds: HashMap::new(),
            name_map: HashMap::new(),
            builtins: [TypeId(0); 10],
        }
    }

    pub(super) fn init_builtins(&mut self, interner: &mut Interners) {
        let builtins = [
            (
                "u8",
                BuiltinTypes::U8,
                TypeKind::Integer {
                    width: IntWidth::I8,
                    signed: Signedness::Unsigned,
                },
                1,
            ),
            (
                "u16",
                BuiltinTypes::U16,
                TypeKind::Integer {
                    width: IntWidth::I16,
                    signed: Signedness::Unsigned,
                },
                2,
            ),
            (
                "u32",
                BuiltinTypes::U32,
                TypeKind::Integer {
                    width: IntWidth::I32,
                    signed: Signedness::Unsigned,
                },
                4,
            ),
            (
                "u64",
                BuiltinTypes::U64,
                TypeKind::Integer {
                    width: IntWidth::I64,
                    signed: Signedness::Unsigned,
                },
                8,
            ),
            (
                "s8",
                BuiltinTypes::S8,
                TypeKind::Integer {
                    width: IntWidth::I8,
                    signed: Signedness::Signed,
                },
                1,
            ),
            (
                "s16",
                BuiltinTypes::S16,
                TypeKind::Integer {
                    width: IntWidth::I16,
                    signed: Signedness::Signed,
                },
                2,
            ),
            (
                "s32",
                BuiltinTypes::S32,
                TypeKind::Integer {
                    width: IntWidth::I32,
                    signed: Signedness::Signed,
                },
                4,
            ),
            (
                "s64",
                BuiltinTypes::S64,
                TypeKind::Integer {
                    width: IntWidth::I64,
                    signed: Signedness::Signed,
                },
                8,
            ),
            ("bool", BuiltinTypes::Bool, TypeKind::Bool, 1),
            ("ptr", BuiltinTypes::Pointer, TypeKind::Pointer, 8),
        ];

        for (name, builtin, kind, size) in builtins {
            let name = interner.intern_lexeme(name);
            let id = self.add_type(name, kind, size);
            self.builtins[builtin as usize] = id;
        }
    }

    fn add_type(&mut self, name: Spur, kind: TypeKind, width: u8) -> TypeId {
        let id = self.kinds.len().to_u16().map(TypeId).unwrap();

        self.name_map.insert(name, id);
        self.kinds.insert(
            id,
            TypeInfo {
                id,
                name,
                kind,
                width,
            },
        );

        id
    }

    pub fn resolve_type(&self, name: Spur) -> Option<TypeInfo> {
        self.name_map.get(&name).map(|id| self.kinds[id])
    }

    pub fn get_type_info(&self, id: TypeId) -> TypeInfo {
        self.kinds[&id]
    }

    pub fn get_builtin(&self, id: BuiltinTypes) -> TypeInfo {
        self.kinds[&self.builtins[id as usize]]
    }
}

pub fn emit_type_error_diag(token: Token, interner: &Interners, source_store: &SourceStorage) {
    diagnostics::emit_error(
        token.location,
        format!("unknown type `{}`", interner.resolve_lexeme(token.lexeme)),
        [Label::new(token.location).with_color(Color::Red)],
        None,
        source_store,
    );
}
