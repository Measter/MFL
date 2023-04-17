use std::ops::RangeInclusive;

use ariadne::{Color, Label};
use hashbrown::{HashMap, HashSet};
use intcast::IntCast;
use lasso::Spur;
use num::Integer;

use crate::{
    diagnostics,
    interners::Interners,
    program::ItemId,
    source_file::{SourceLocation, SourceStorage, Spanned},
};

pub const STRING_DEF: &str = "
struct String is
    field len u64
    field data ptr(u8)
end
";

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

    fn byte_width(self) -> u64 {
        match self {
            IntWidth::I8 => 1,
            IntWidth::I16 => 2,
            IntWidth::I32 => 4,
            IntWidth::I64 => 8,
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
    GenericStructBase(ItemId),
    GenericStructInstance(ItemId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    String,
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
            "String" => BuiltinTypes::String,
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
pub struct FixedResolvedStruct {
    pub name: Spanned<Spur>,
    pub fields: Vec<FixedResolvedField>,
}

#[derive(Debug, Clone)]
pub struct FixedResolvedField {
    pub name: Spanned<Spur>,
    pub kind: TypeId,
}

#[derive(Debug, Clone)]
pub struct GenericPartiallyResolvedStruct {
    pub name: Spanned<Spur>,
    pub fields: Vec<GenericPartiallyResolvedField>,
    pub generic_params: Vec<Spanned<Spur>>,
}

#[derive(Debug, Clone)]
pub struct GenericPartiallyResolvedField {
    pub name: Spanned<Spur>,
    pub kind: GenericPartiallyResolvedFieldKind,
}

#[derive(Debug, Clone)]
pub enum GenericPartiallyResolvedFieldKind {
    Fixed(TypeId),
    GenericParamSimple(Spanned<Spur>),   // T
    GenericParamPointer(Box<Self>),      // ptr(T)
    GenericParamArray(Box<Self>, usize), // T[N]
    GenericStruct(ItemId, Vec<Self>),    // Bar(u32), Bar(T), Bar(Baz(T))
}

impl GenericPartiallyResolvedFieldKind {
    pub fn match_generic_type(
        &self,
        param: Spur,
        input_id: TypeId,
        input_kind: TypeKind,
    ) -> Option<TypeId> {
        match (self, input_kind) {
            (GenericPartiallyResolvedFieldKind::GenericParamSimple(s), _) if s.inner == param => {
                Some(input_id)
            }
            (
                GenericPartiallyResolvedFieldKind::GenericParamPointer(t),
                TypeKind::Pointer(ptr_type),
            ) if matches!(&**t, GenericPartiallyResolvedFieldKind::GenericParamSimple(t) if t.inner == param) => {
                Some(ptr_type)
            }

            (
                GenericPartiallyResolvedFieldKind::GenericParamArray(t, ..),
                TypeKind::Array { type_id, .. },
            ) if matches!(&**t, GenericPartiallyResolvedFieldKind::GenericParamSimple(t) if t.inner == param) => {
                Some(type_id)
            }

            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct UnresolvedStruct {
    pub name: Spanned<Spur>,
    pub fields: Vec<UnresolvedField>,
    pub generic_params: Option<Vec<Spanned<Spur>>>,
}

#[derive(Debug, Clone)]
pub struct UnresolvedField {
    pub name: Spanned<Spur>,
    pub kind: UnresolvedType,
}

// Used prior to ident resolution
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnresolvedTypeTokens {
    Simple(Vec<Spanned<Spur>>),
    Array(Box<UnresolvedTypeTokens>, usize),
    Pointer(Box<UnresolvedTypeTokens>),
    GenericInstance {
        type_name: Vec<Spanned<Spur>>,
        params: Vec<UnresolvedTypeTokens>,
    },
}

// Used after ident resolution
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnresolvedTypeIds {
    SimpleCustom {
        id: ItemId,
        token: Spanned<Spur>,
    },
    SimpleBuiltin(BuiltinTypes),
    SimpleGenericParam(Spanned<Spur>),
    Array(Box<UnresolvedTypeIds>, usize),
    Pointer(Box<UnresolvedTypeIds>),
    GenericInstance {
        id: ItemId,
        id_token: Spanned<Spur>,
        params: Vec<UnresolvedTypeIds>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnresolvedType {
    Tokens(UnresolvedTypeTokens),
    Id(UnresolvedTypeIds),
}

impl UnresolvedType {
    pub fn as_id(&self) -> &UnresolvedTypeIds {
        match self {
            UnresolvedType::Tokens(_) => panic!("ICE: called as_id on Tokens"),
            UnresolvedType::Id(id) => id,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TypeInfo {
    pub id: TypeId,
    pub name: Spur,
    pub location: Option<SourceLocation>,
    pub kind: TypeKind,
}

#[derive(Debug, Clone, Copy)]
pub struct TypeSize {
    pub byte_width: u64,
    pub alignement: u64,
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
    builtins: [TypeId; 10],

    // Maps ItemIds to TypeIds of non-generic structs.
    struct_id_map: HashMap<ItemId, TypeId>,
    fixed_struct_defs: HashMap<TypeId, FixedResolvedStruct>,
    builtin_struct_item_ids: HashSet<ItemId>,
    generic_struct_id_map: HashMap<TypeId, GenericPartiallyResolvedStruct>,
    generic_struct_instance_map: HashMap<(TypeId, Vec<TypeId>), TypeId>,

    type_sizes: HashMap<TypeId, TypeSize>,
}

impl TypeStore {
    pub fn new(interner: &mut Interners) -> Self {
        let mut s = Self {
            kinds: HashMap::new(),
            pointer_map: HashMap::new(),
            array_map: HashMap::new(),
            builtins: [TypeId(0); 10],
            struct_id_map: HashMap::new(),
            fixed_struct_defs: HashMap::new(),
            builtin_struct_item_ids: HashSet::new(),
            generic_struct_id_map: HashMap::new(),
            generic_struct_instance_map: HashMap::new(),
            type_sizes: HashMap::new(),
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

    pub fn update_builtins(&mut self, struct_map: &HashMap<ItemId, UnresolvedStruct>) {
        for id in struct_map.keys() {
            self.builtin_struct_item_ids.insert(*id);
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

        if let TypeKind::Struct(struct_id) | TypeKind::GenericStructBase(struct_id) = kind {
            self.struct_id_map.insert(struct_id, id);
        }

        id
    }

    pub fn resolve_type(
        &mut self,
        interner: &mut Interners,
        tp: &UnresolvedTypeIds,
    ) -> Result<TypeInfo, Spanned<Spur>> {
        match tp {
            UnresolvedTypeIds::SimpleCustom { id, token } => self
                .struct_id_map
                .get(id)
                .map(|id| self.kinds[id])
                .ok_or(*token),
            UnresolvedTypeIds::SimpleBuiltin(builtin) => Ok(self.get_builtin(*builtin)),
            UnresolvedTypeIds::Array(at, length) => {
                let inner = self.resolve_type(interner, at)?;
                Ok(self.get_array(interner, inner.id, *length))
            }
            UnresolvedTypeIds::Pointer(pt) => {
                let pointee = self.resolve_type(interner, pt)?;
                Ok(self.get_pointer(interner, pointee.id))
            }
            UnresolvedTypeIds::GenericInstance { id, params, .. } => {
                let base_struct_id = self.struct_id_map[id];
                let param_type_ids: Vec<_> = params
                    .iter()
                    .map(|p| self.resolve_type(interner, p).map(|ti| ti.id))
                    .collect::<Result<_, _>>()?;

                Ok(self.instantiate_generic_struct(interner, *id, base_struct_id, param_type_ids))
            }
            UnresolvedTypeIds::SimpleGenericParam(f) => Err(*f),
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

    fn partially_resolve_generic_field(
        &mut self,
        interner: &mut Interners,
        kind: &UnresolvedTypeIds,
    ) -> GenericPartiallyResolvedFieldKind {
        match kind {
            UnresolvedTypeIds::SimpleCustom { .. } => {
                let resolved = self.resolve_type(interner, kind).unwrap();
                GenericPartiallyResolvedFieldKind::Fixed(resolved.id)
            }
            UnresolvedTypeIds::SimpleBuiltin(bi) => {
                GenericPartiallyResolvedFieldKind::Fixed(self.get_builtin(*bi).id)
            }
            UnresolvedTypeIds::SimpleGenericParam(n) => {
                GenericPartiallyResolvedFieldKind::GenericParamSimple(*n)
            }
            UnresolvedTypeIds::Array(sub_type, length) => {
                let inner_kind = self.partially_resolve_generic_field(interner, sub_type);
                GenericPartiallyResolvedFieldKind::GenericParamArray(Box::new(inner_kind), *length)
            }
            UnresolvedTypeIds::Pointer(sub_type) => {
                let inner_kind = self.partially_resolve_generic_field(interner, sub_type);
                GenericPartiallyResolvedFieldKind::GenericParamPointer(Box::new(inner_kind))
            }
            UnresolvedTypeIds::GenericInstance { id, params, .. } => {
                let generic_params = params
                    .iter()
                    .map(|gp| self.partially_resolve_generic_field(interner, gp))
                    .collect();
                GenericPartiallyResolvedFieldKind::GenericStruct(*id, generic_params)
            }
        }
    }

    pub fn partially_resolve_generic_struct(
        &mut self,
        interner: &mut Interners,
        base_item_id: ItemId,
        def: &UnresolvedStruct,
    ) {
        let Some(generic_params) = def.generic_params.clone() else {
            panic!("ICE: Tried to define generic struct for a non-generic definition");
        };

        let mut resolved_fields = Vec::new();

        for field in &def.fields {
            let field_kind = self.partially_resolve_generic_field(interner, field.kind.as_id());

            resolved_fields.push(GenericPartiallyResolvedField {
                name: field.name,
                kind: field_kind,
            });
        }

        let generic_base = GenericPartiallyResolvedStruct {
            name: def.name,
            fields: resolved_fields,
            generic_params,
        };

        let type_id = self.struct_id_map[&base_item_id];

        self.generic_struct_id_map.insert(type_id, generic_base);
    }

    fn resolve_generic_field(
        &mut self,
        interner: &mut Interners,
        kind: &GenericPartiallyResolvedFieldKind,
        type_params: &HashMap<Spur, TypeId>,
    ) -> TypeId {
        match kind {
            GenericPartiallyResolvedFieldKind::Fixed(id) => *id,
            GenericPartiallyResolvedFieldKind::GenericParamSimple(n) => type_params[&n.inner],
            GenericPartiallyResolvedFieldKind::GenericParamPointer(sub_type) => {
                let pointee_id = self.resolve_generic_field(interner, sub_type, type_params);
                self.get_pointer(interner, pointee_id).id
            }
            GenericPartiallyResolvedFieldKind::GenericParamArray(sub_type, length) => {
                let content_type_id = self.resolve_generic_field(interner, sub_type, type_params);
                self.get_array(interner, content_type_id, *length).id
            }
            GenericPartiallyResolvedFieldKind::GenericStruct(base_struct_id, sub_params) => {
                let base_struct_type_id = self.struct_id_map[base_struct_id];

                let sub_params: Vec<_> = sub_params
                    .iter()
                    .map(|sp| self.resolve_generic_field(interner, sp, type_params))
                    .collect();

                self.instantiate_generic_struct(
                    interner,
                    *base_struct_id,
                    base_struct_type_id,
                    sub_params,
                )
                .id
            }
        }
    }

    pub fn instantiate_generic_struct(
        &mut self,
        interner: &mut Interners,
        base_item_id: ItemId,
        base_type_id: TypeId,
        type_params: Vec<TypeId>,
    ) -> TypeInfo {
        if let Some(id) = self
            .generic_struct_instance_map
            .get(&(base_type_id, type_params.clone()))
        {
            return self.kinds[id];
        }

        let base_type_info = self.get_type_info(base_type_id);
        let base_def = &self.generic_struct_id_map[&base_type_id].clone();

        let param_lookup: HashMap<_, _> = base_def
            .generic_params
            .iter()
            .map(|s| s.inner)
            .zip(type_params.iter().copied())
            .collect();

        let mut resolved_fields = Vec::new();

        for field in &base_def.fields {
            let new_kind = self.resolve_generic_field(interner, &field.kind, &param_lookup);
            resolved_fields.push(FixedResolvedField {
                name: field.name,
                kind: new_kind,
            });
        }

        let new_def = FixedResolvedStruct {
            name: base_def.name,
            fields: resolved_fields,
        };

        let mut name = interner.resolve_lexeme(base_def.name.inner).to_owned();
        name += "(";

        match type_params.as_slice() {
            [] => unreachable!(),
            [n] => {
                let ti = self.get_type_info(*n);
                let t_name = interner.resolve_lexeme(ti.name);
                name += t_name;
            }
            [n, xs @ ..] => {
                use std::fmt::Write;
                let ti = self.get_type_info(*n);
                let t_name = interner.resolve_lexeme(ti.name);
                let _ = write!(&mut name, "{t_name}");

                for t in xs {
                    let ti = self.get_type_info(*t);
                    let t_name = interner.resolve_lexeme(ti.name);
                    let _ = write!(&mut name, " {t_name}");
                }
            }
        }

        name += ")";

        let name = interner.intern_lexeme(&name);

        let type_id = self.add_type(
            name,
            base_type_info.location,
            TypeKind::GenericStructInstance(base_item_id),
        );
        self.fixed_struct_defs.insert(type_id, new_def);
        self.generic_struct_instance_map
            .insert((base_type_id, type_params), type_id);

        self.kinds[&type_id]
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

    pub fn get_size_info(&mut self, id: TypeId) -> TypeSize {
        if let Some(info) = self.type_sizes.get(&id) {
            return *info;
        }

        let type_info = *self.kinds.get(&id).unwrap();
        let size_info = match type_info.kind {
            TypeKind::Array { type_id, length } => {
                let mut inner_size = self.get_size_info(type_id);
                inner_size.byte_width =
                    Integer::next_multiple_of(&inner_size.byte_width, &inner_size.alignement)
                        * length.to_u64();
                inner_size
            }
            TypeKind::Integer { width, .. } => TypeSize {
                byte_width: width.byte_width(),
                alignement: width.byte_width(),
            },
            TypeKind::Pointer(_) => TypeSize {
                byte_width: 8,
                alignement: 8,
            },
            TypeKind::Bool => TypeSize {
                byte_width: 1,
                alignement: 1,
            },
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let mut size_info = TypeSize {
                    byte_width: 0,
                    alignement: 0,
                };

                let struct_info = self.fixed_struct_defs.get(&id).unwrap().clone();
                for field in &struct_info.fields {
                    let field_size = self.get_size_info(field.kind);
                    size_info.alignement = size_info.alignement.max(field_size.alignement);
                    size_info.byte_width =
                        Integer::next_multiple_of(&size_info.byte_width, &field_size.alignement)
                            + field_size.byte_width;
                }

                size_info
            }
            TypeKind::GenericStructBase(_) => {
                panic!("ICE: Tried to get size of generic struct base")
            }
        };

        self.type_sizes.insert(id, size_info);
        size_info
    }

    pub fn define_fixed_struct(
        &mut self,
        interner: &mut Interners,
        struct_id: ItemId,
        def: &UnresolvedStruct,
    ) -> Result<TypeId, Spanned<Spur>> {
        if def.generic_params.is_some() {
            panic!("ICE: Tried to define fixed struct for a generic definition");
        }

        let mut resolved_fields = Vec::new();

        for field in &def.fields {
            let kind = self
                .resolve_type(interner, field.kind.as_id())
                .map_err(|_| field.name)?
                .id;
            resolved_fields.push(FixedResolvedField {
                name: field.name,
                kind,
            });
        }

        let def = FixedResolvedStruct {
            name: def.name,
            fields: resolved_fields,
        };

        let type_id = self.struct_id_map[&struct_id];

        if interner.resolve_lexeme(def.name.inner) == "String"
            && self.builtin_struct_item_ids.contains(&struct_id)
        {
            self.builtins[BuiltinTypes::String as usize] = type_id;
        }

        self.fixed_struct_defs.insert(type_id, def);

        Ok(type_id)
    }

    #[track_caller]
    pub fn get_struct_def(&self, id: TypeId) -> &FixedResolvedStruct {
        &self.fixed_struct_defs[&id]
    }

    #[track_caller]
    pub fn get_generic_base_def(&self, id: TypeId) -> &GenericPartiallyResolvedStruct {
        &self.generic_struct_id_map[&id]
    }
}

pub fn emit_type_error_diag(
    token: Spanned<Spur>,
    interner: &Interners,
    source_store: &SourceStorage,
) {
    diagnostics::emit_error(
        token.location,
        format!("unknown type `{}`", interner.resolve_lexeme(token.inner)),
        [Label::new(token.location).with_color(Color::Red)],
        None,
        source_store,
    );
}
