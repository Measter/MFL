use std::ops::RangeInclusive;

use ariadne::{Color, Label};
use hashbrown::HashMap;
use intcast::IntCast;
use lasso::Spur;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::Token,
    opcode::UnresolvedIdent,
    program::ItemId,
    source_file::{SourceLocation, SourceStorage},
};

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
    Array { type_id: TypeId, length: usize },
    Integer { width: IntWidth, signed: Signedness },
    Pointer(TypeId),
    Bool,
    Struct(ItemId),
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
}

impl BuiltinTypes {
    pub fn from_name(name: &str) -> Option<Self> {
        let builtin = match name {
            "u8" => BuiltinTypes::U8,
            "s8" => BuiltinTypes::S8,
            "u16" => BuiltinTypes::U16,
            "s16" => BuiltinTypes::S16,
            "u32" => BuiltinTypes::U32,
            "s32" => BuiltinTypes::S32,
            "u64" => BuiltinTypes::U64,
            "s64" => BuiltinTypes::S64,
            "bool" => BuiltinTypes::Bool,
            _ => return None,
        };
        Some(builtin)
    }
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

#[derive(Debug, Clone)]
pub struct ResolvedStruct {
    pub name: Token,
    pub fields: Vec<ResolvedField>,
}

#[derive(Debug, Clone)]
pub struct ResolvedField {
    pub name: Token,
    pub kind: TypeId,
}

#[derive(Debug, Clone)]
pub struct UnresolvedStruct {
    pub name: Token,
    pub fields: Vec<UnresolvedField>,
}

#[derive(Debug, Clone)]
pub struct UnresolvedField {
    pub name: Token,
    pub kind: UnresolvedType,
}

#[derive(Debug, Clone)]
pub enum UnresolvedType {
    Simple(UnresolvedIdent),
    SimpleBuiltin(BuiltinTypes),
    SimpleCustom { id: ItemId, token: Token },
    Array(SourceLocation, Box<UnresolvedType>, usize),
    Pointer(SourceLocation, Box<UnresolvedType>),
}

#[derive(Debug, Clone, Copy)]
pub struct TypeInfo {
    pub id: TypeId,
    pub name: Spur,
    pub location: Option<SourceLocation>,
    pub kind: TypeKind,
}

#[derive(Debug, Clone)]
struct PointerInfo {
    ptr_id: TypeId,
}

#[derive(Debug)]
pub struct TypeStore {
    kinds: HashMap<TypeId, TypeInfo>,
    pointer_map: HashMap<TypeId, PointerInfo>,
    array_map: HashMap<(TypeId, usize), TypeId>,
    builtins: [TypeId; 9],

    struct_id_map: HashMap<ItemId, TypeId>,
    struct_defs: HashMap<TypeId, ResolvedStruct>,
}

impl TypeStore {
    pub fn new(interner: &mut Interners) -> Self {
        let mut s = Self {
            kinds: HashMap::new(),
            pointer_map: HashMap::new(),
            array_map: HashMap::new(),
            builtins: [TypeId(0); 9],
            struct_id_map: HashMap::new(),
            struct_defs: HashMap::new(),
        };
        s.init_builtins(interner);
        s
    }

    fn init_builtins(&mut self, interner: &mut Interners) {
        let builtins = [
            (
                "u8",
                BuiltinTypes::U8,
                TypeKind::Integer {
                    width: IntWidth::I8,
                    signed: Signedness::Unsigned,
                },
            ),
            (
                "u16",
                BuiltinTypes::U16,
                TypeKind::Integer {
                    width: IntWidth::I16,
                    signed: Signedness::Unsigned,
                },
            ),
            (
                "u32",
                BuiltinTypes::U32,
                TypeKind::Integer {
                    width: IntWidth::I32,
                    signed: Signedness::Unsigned,
                },
            ),
            (
                "u64",
                BuiltinTypes::U64,
                TypeKind::Integer {
                    width: IntWidth::I64,
                    signed: Signedness::Unsigned,
                },
            ),
            (
                "s8",
                BuiltinTypes::S8,
                TypeKind::Integer {
                    width: IntWidth::I8,
                    signed: Signedness::Signed,
                },
            ),
            (
                "s16",
                BuiltinTypes::S16,
                TypeKind::Integer {
                    width: IntWidth::I16,
                    signed: Signedness::Signed,
                },
            ),
            (
                "s32",
                BuiltinTypes::S32,
                TypeKind::Integer {
                    width: IntWidth::I32,
                    signed: Signedness::Signed,
                },
            ),
            (
                "s64",
                BuiltinTypes::S64,
                TypeKind::Integer {
                    width: IntWidth::I64,
                    signed: Signedness::Signed,
                },
            ),
            ("bool", BuiltinTypes::Bool, TypeKind::Bool),
        ];

        for (name_str, builtin, kind) in builtins {
            let name = interner.intern_lexeme(name_str);
            let id = self.add_type(name, None, kind);
            self.builtins[builtin as usize] = id;

            // A couple parts of the compiler need to construct pointers to basic types.
            self.get_pointer(interner, id);
        }
    }

    pub fn add_type(
        &mut self,
        name: Spur,
        location: impl Into<Option<SourceLocation>>,
        kind: TypeKind,
    ) -> TypeId {
        let id = self.kinds.len().to_u16().map(TypeId).unwrap();

        self.kinds.insert(
            id,
            TypeInfo {
                id,
                name,
                location: location.into(),
                kind,
            },
        );

        if let TypeKind::Struct(struct_id) = kind {
            self.struct_id_map.insert(struct_id, id);
        }

        id
    }

    pub fn resolve_type(
        &mut self,
        interner: &mut Interners,
        tp: &UnresolvedType,
    ) -> Result<TypeInfo, Token> {
        match tp {
            UnresolvedType::Simple(_) => panic!("ICE: All idents should be resolved"),
            UnresolvedType::SimpleCustom { id, token } => self
                .struct_id_map
                .get(id)
                .map(|id| self.kinds[id])
                .ok_or(*token),
            UnresolvedType::SimpleBuiltin(builtin) => Ok(self.get_builtin(*builtin)),
            UnresolvedType::Array(_, at, length) => {
                let inner = self.resolve_type(interner, at)?;
                Ok(self.get_array(interner, inner.id, *length))
            }
            UnresolvedType::Pointer(_, pt) => {
                let pointee = self.resolve_type(interner, pt)?;
                Ok(self.get_pointer(interner, pointee.id))
            }
        }
    }

    pub fn get_pointer(&mut self, interner: &mut Interners, pointee_id: TypeId) -> TypeInfo {
        let pointee = self.get_type_info(pointee_id);

        if let Some(pi) = self.pointer_map.get(&pointee.id) {
            self.kinds[&pi.ptr_id]
        } else {
            let pointee_name = interner.resolve_lexeme(pointee.name);
            let name = format!("ptr({pointee_name})");
            let name = interner.intern_lexeme(&name);

            let pointer_info = self.add_type(name, None, TypeKind::Pointer(pointee.id));
            self.pointer_map.insert(
                pointee.id,
                PointerInfo {
                    ptr_id: pointer_info,
                },
            );

            self.kinds[&pointer_info]
        }
    }

    pub fn get_array(
        &mut self,
        interner: &mut Interners,
        content_type_id: TypeId,
        length: usize,
    ) -> TypeInfo {
        let kind_info = self.get_type_info(content_type_id);

        if let Some(&array_id) = self.array_map.get(&(kind_info.id, length)) {
            self.kinds[&array_id]
        } else {
            let pointee_name = interner.resolve_lexeme(kind_info.name);
            let name = format!("{pointee_name}[{length}]");
            let name = interner.intern_lexeme(&name);

            let array_info = self.add_type(
                name,
                None,
                TypeKind::Array {
                    type_id: content_type_id,
                    length,
                },
            );
            self.array_map.insert((content_type_id, length), array_info);

            self.kinds[&array_info]
        }
    }

    pub fn get_type_info(&self, id: TypeId) -> TypeInfo {
        self.kinds[&id]
    }

    pub fn get_builtin(&self, id: BuiltinTypes) -> TypeInfo {
        self.kinds[&self.builtins[id as usize]]
    }

    pub fn get_builtin_ptr(&self, id: BuiltinTypes) -> TypeInfo {
        let id = &self.pointer_map[&self.builtins[id as usize]];
        self.kinds[&id.ptr_id]
    }

    pub fn define_struct(
        &mut self,
        interner: &mut Interners,
        struct_id: ItemId,
        def: &UnresolvedStruct,
    ) -> Result<TypeId, Token> {
        let mut resolved_fields = Vec::new();

        for field in &def.fields {
            let kind = self
                .resolve_type(interner, &field.kind)
                .map_err(|_| field.name)?;
            resolved_fields.push(ResolvedField {
                name: field.name,
                kind: kind.id,
            });
        }

        let def = ResolvedStruct {
            name: def.name,
            fields: resolved_fields,
        };

        let type_id = self.struct_id_map[&struct_id];
        self.struct_defs.insert(type_id, def);
        Ok(type_id)
    }

    #[track_caller]
    pub fn get_struct_def(&self, id: TypeId) -> &ResolvedStruct {
        &self.struct_defs[&id]
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
