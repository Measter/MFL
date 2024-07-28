use std::{hash::Hash, ops::RangeInclusive};

use ariadne::{Color, Label};
use hashbrown::HashMap;
use intcast::IntCast;
use lasso::Spur;

use crate::{
    context::{ItemId, LangItem},
    diagnostics,
    ir::{NameResolvedType, StructDef, StructDefField},
    stores::{
        self,
        source::{SourceLocation, Spanned},
        strings::StringStore,
    },
    Stores,
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
pub struct Integer {
    pub width: IntWidth,
    pub signed: Signedness,
}

impl Integer {
    pub const U64: Self = Self {
        width: IntWidth::I64,
        signed: Signedness::Unsigned,
    };

    pub fn is_unsigned(self) -> bool {
        self.signed == Signedness::Unsigned
    }
}

impl From<(IntWidth, Signedness)> for Integer {
    fn from(value: (IntWidth, Signedness)) -> Self {
        Self {
            width: value.0,
            signed: value.1,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeKind {
    Array { type_id: TypeId, length: usize },
    Integer(Integer),
    Pointer(TypeId),
    Bool,
    Struct(ItemId),
    GenericStructBase(ItemId),
    GenericStructInstance(ItemId),
}

impl TypeKind {
    pub fn is_unsigned_int(self) -> bool {
        let TypeKind::Integer(int) = self else {
            return false;
        };
        int.is_unsigned()
    }
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
            _ => return None,
        };
        Some(builtin)
    }
}

impl From<Integer> for BuiltinTypes {
    fn from(value: Integer) -> Self {
        match (value.signed, value.width) {
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
pub struct GenericPartiallyResolvedStruct {
    pub name: Spanned<Spur>,
    pub fields: Vec<GenericPartiallyResolvedField>,
    pub generic_params: Vec<Spanned<Spur>>,
    pub is_union: bool,
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
    GenericParamPointer(Box<Self>),      // T&
    GenericParamArray(Box<Self>, usize), // T[N]
    GenericStruct(ItemId, Vec<Self>),    // Bar(u32), Bar(T), Bar(Baz(T))
}

impl GenericPartiallyResolvedFieldKind {
    pub fn match_generic_type(
        &self,
        stores: &Stores,
        param: Spur,
        input_type_info: TypeInfo,
    ) -> Option<TypeId> {
        match (self, input_type_info.kind) {
            (GenericPartiallyResolvedFieldKind::GenericParamSimple(s), _) if s.inner == param => {
                Some(input_type_info.id)
            }
            (
                GenericPartiallyResolvedFieldKind::GenericParamPointer(t),
                TypeKind::Pointer(ptr_type),
            ) => {
                let inner_info = stores.types.get_type_info(ptr_type);
                t.match_generic_type(stores, param, inner_info)
            }

            (
                GenericPartiallyResolvedFieldKind::GenericParamArray(t, ..),
                TypeKind::Array { type_id, .. },
            ) => {
                let inner_info = stores.types.get_type_info(type_id);
                t.match_generic_type(stores, param, inner_info)
            }

            (
                GenericPartiallyResolvedFieldKind::GenericStruct(struct_id, params),
                TypeKind::GenericStructInstance(input_struct_id),
            ) if input_struct_id == *struct_id => {
                // We know the input struct is the same as the field struct.

                let input_struct_def = stores.types.get_struct_def(input_type_info.id);
                let input_type_params = input_struct_def.generic_params.as_ref().unwrap();
                params
                    .iter()
                    .zip(input_type_params)
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
pub struct TypeInfo {
    pub id: TypeId,
    pub friendly_name: Spur,
    pub mangled_name: Spur,
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
    lang_item_ids: HashMap<ItemId, LangItem>,
    fixed_struct_defs: HashMap<TypeId, StructDef<TypeId>>,
    generic_struct_id_map: HashMap<TypeId, GenericPartiallyResolvedStruct>,
    generic_struct_instance_map: HashMap<(TypeId, Vec<TypeId>), TypeId>,

    type_sizes: HashMap<TypeId, TypeSize>,
}

impl TypeStore {
    pub fn new(string_store: &mut StringStore) -> Self {
        let mut s = Self {
            kinds: HashMap::new(),
            pointer_map: HashMap::new(),
            array_map: HashMap::new(),
            builtins: [TypeId(0); 10],
            struct_id_map: HashMap::new(),
            lang_item_ids: HashMap::new(),
            fixed_struct_defs: HashMap::new(),
            generic_struct_id_map: HashMap::new(),
            generic_struct_instance_map: HashMap::new(),
            type_sizes: HashMap::new(),
        };
        s.init_builtins(string_store);
        s
    }

    fn init_builtins(&mut self, string_store: &mut StringStore) {
        let builtins = [
            (
                "u8",
                BuiltinTypes::U8,
                TypeKind::Integer((IntWidth::I8, Signedness::Unsigned).into()),
            ),
            (
                "u16",
                BuiltinTypes::U16,
                TypeKind::Integer((IntWidth::I16, Signedness::Unsigned).into()),
            ),
            (
                "u32",
                BuiltinTypes::U32,
                TypeKind::Integer((IntWidth::I32, Signedness::Unsigned).into()),
            ),
            (
                "u64",
                BuiltinTypes::U64,
                TypeKind::Integer((IntWidth::I64, Signedness::Unsigned).into()),
            ),
            (
                "s8",
                BuiltinTypes::S8,
                TypeKind::Integer((IntWidth::I8, Signedness::Signed).into()),
            ),
            (
                "s16",
                BuiltinTypes::S16,
                TypeKind::Integer((IntWidth::I16, Signedness::Signed).into()),
            ),
            (
                "s32",
                BuiltinTypes::S32,
                TypeKind::Integer((IntWidth::I32, Signedness::Signed).into()),
            ),
            (
                "s64",
                BuiltinTypes::S64,
                TypeKind::Integer((IntWidth::I64, Signedness::Signed).into()),
            ),
            ("bool", BuiltinTypes::Bool, TypeKind::Bool),
        ];

        for (name_str, builtin, kind) in builtins {
            let name = string_store.intern(name_str);
            let id = self.add_type(name, name, None, kind);
            self.builtins[builtin as usize] = id;

            // A couple parts of the compiler need to construct pointers to basic types.
            self.get_pointer(string_store, id);
        }
    }

    pub fn update_builtins(&mut self, lang_items: &HashMap<LangItem, ItemId>) {
        let string_item_id = lang_items
            .get(&LangItem::String)
            .expect("string lang_item missing");

        self.lang_item_ids.insert(*string_item_id, LangItem::String);
    }

    pub fn add_type(
        &mut self,
        friendly_name: Spur,
        mangled_name: Spur,
        location: impl Into<Option<SourceLocation>>,
        kind: TypeKind,
    ) -> TypeId {
        let id = self.kinds.len().to_u16().map(TypeId).unwrap();

        self.kinds.insert(
            id,
            TypeInfo {
                id,
                friendly_name,
                mangled_name,
                location: location.into(),
                kind,
            },
        );

        if let TypeKind::Struct(struct_id) | TypeKind::GenericStructBase(struct_id) = kind {
            self.struct_id_map.insert(struct_id, id);
            if self.lang_item_ids.get(&struct_id) == Some(&LangItem::String) {
                self.builtins[BuiltinTypes::String as usize] = id;
            }
        }

        id
    }

    pub fn resolve_type(
        &mut self,
        string_store: &mut StringStore,
        tp: &NameResolvedType,
    ) -> Result<TypeInfo, Spanned<Spur>> {
        match tp {
            NameResolvedType::SimpleCustom { id, token } => self
                .struct_id_map
                .get(id)
                .map(|id| self.kinds[id])
                .ok_or(*token),
            NameResolvedType::SimpleBuiltin(builtin) => Ok(self.get_builtin(*builtin)),
            NameResolvedType::Array(at, length) => {
                let inner = self.resolve_type(string_store, at)?;
                Ok(self.get_array(string_store, inner.id, *length))
            }
            NameResolvedType::Pointer(pt) => {
                let pointee = self.resolve_type(string_store, pt)?;
                Ok(self.get_pointer(string_store, pointee.id))
            }
            NameResolvedType::GenericInstance { id, params, .. } => {
                let base_struct_id = self.struct_id_map[id];
                let param_type_ids: Vec<_> = params
                    .iter()
                    .map(|p| self.resolve_type(string_store, p).map(|ti| ti.id))
                    .collect::<Result<_, _>>()?;

                Ok(self.instantiate_generic_struct(
                    string_store,
                    *id,
                    base_struct_id,
                    param_type_ids,
                ))
            }
            NameResolvedType::SimpleGenericParam(f) => Err(*f),
        }
    }

    pub fn get_pointer(&mut self, string_store: &mut StringStore, pointee_id: TypeId) -> TypeInfo {
        let pointee = self.get_type_info(pointee_id);

        if let Some(pi) = self.pointer_map.get(&pointee.id) {
            self.kinds[&pi.ptr_id]
        } else {
            let pointee_friendly_name = string_store.resolve(pointee.friendly_name);
            let friendly_name = format!("{pointee_friendly_name}{}", stores::FRENDLY_PTR);
            let friendly_name = string_store.intern(&friendly_name);

            let pointee_mangled_name = string_store.resolve(pointee.mangled_name);
            let mangled_name = format!("{pointee_mangled_name}{}", stores::MANGLED_PTR);
            let mangled_name = string_store.intern(&mangled_name);

            let pointer_info = self.add_type(
                friendly_name,
                mangled_name,
                None,
                TypeKind::Pointer(pointee.id),
            );
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
        string_store: &mut StringStore,
        content_type_id: TypeId,
        length: usize,
    ) -> TypeInfo {
        let kind_info = self.get_type_info(content_type_id);

        if let Some(&array_id) = self.array_map.get(&(kind_info.id, length)) {
            self.kinds[&array_id]
        } else {
            let inner_friendly_name = string_store.resolve(kind_info.friendly_name);
            let friendly_name = format!(
                "{inner_friendly_name}{}{length}{}",
                stores::FRENDLY_ARRAY_OPEN,
                stores::FRENDLY_ARRAY_CLOSE
            );
            let friendly_name = string_store.intern(&friendly_name);

            let inner_mangled_name = string_store.resolve(kind_info.mangled_name);
            let mangled_name = format!(
                "{inner_mangled_name}{}{length}{}",
                stores::MANGLED_ARRAY_OPEN,
                stores::MANGLED_ARRAY_CLOSE
            );
            let mangled_name = string_store.intern(&mangled_name);

            let array_info = self.add_type(
                friendly_name,
                mangled_name,
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
        string_store: &mut StringStore,
        kind: &NameResolvedType,
    ) -> GenericPartiallyResolvedFieldKind {
        match kind {
            NameResolvedType::SimpleCustom { .. } => {
                let resolved = self.resolve_type(string_store, kind).unwrap();
                GenericPartiallyResolvedFieldKind::Fixed(resolved.id)
            }
            NameResolvedType::SimpleBuiltin(bi) => {
                GenericPartiallyResolvedFieldKind::Fixed(self.get_builtin(*bi).id)
            }
            NameResolvedType::SimpleGenericParam(n) => {
                GenericPartiallyResolvedFieldKind::GenericParamSimple(*n)
            }
            NameResolvedType::Array(sub_type, length) => {
                let inner_kind = self.partially_resolve_generic_field(string_store, sub_type);
                GenericPartiallyResolvedFieldKind::GenericParamArray(Box::new(inner_kind), *length)
            }
            NameResolvedType::Pointer(sub_type) => {
                let inner_kind = self.partially_resolve_generic_field(string_store, sub_type);
                GenericPartiallyResolvedFieldKind::GenericParamPointer(Box::new(inner_kind))
            }
            NameResolvedType::GenericInstance { id, params, .. } => {
                let generic_params = params
                    .iter()
                    .map(|gp| self.partially_resolve_generic_field(string_store, gp))
                    .collect();
                GenericPartiallyResolvedFieldKind::GenericStruct(*id, generic_params)
            }
        }
    }

    pub fn partially_resolve_generic_struct(
        &mut self,
        string_store: &mut StringStore,
        base_item_id: ItemId,
        def: &StructDef<NameResolvedType>,
    ) {
        let Some(generic_params) = def.generic_params.clone() else {
            panic!("ICE: Tried to define generic struct for a non-generic definition");
        };

        let mut resolved_fields = Vec::new();

        for field in &def.fields {
            let field_kind = self.partially_resolve_generic_field(string_store, &field.kind);

            resolved_fields.push(GenericPartiallyResolvedField {
                name: field.name,
                kind: field_kind,
            });
        }

        let generic_base = GenericPartiallyResolvedStruct {
            name: def.name,
            fields: resolved_fields,
            generic_params,
            is_union: def.is_union,
        };

        let type_id = self.struct_id_map[&base_item_id];

        self.generic_struct_id_map.insert(type_id, generic_base);
    }

    fn resolve_generic_field(
        &mut self,
        string_store: &mut StringStore,
        kind: &GenericPartiallyResolvedFieldKind,
        type_params: &HashMap<Spur, TypeId>,
    ) -> TypeId {
        match kind {
            GenericPartiallyResolvedFieldKind::Fixed(id) => *id,
            GenericPartiallyResolvedFieldKind::GenericParamSimple(n) => type_params[&n.inner],
            GenericPartiallyResolvedFieldKind::GenericParamPointer(sub_type) => {
                let pointee_id = self.resolve_generic_field(string_store, sub_type, type_params);
                self.get_pointer(string_store, pointee_id).id
            }
            GenericPartiallyResolvedFieldKind::GenericParamArray(sub_type, length) => {
                let content_type_id =
                    self.resolve_generic_field(string_store, sub_type, type_params);
                self.get_array(string_store, content_type_id, *length).id
            }
            GenericPartiallyResolvedFieldKind::GenericStruct(base_struct_id, sub_params) => {
                let base_struct_type_id = self.struct_id_map[base_struct_id];

                let sub_params: Vec<_> = sub_params
                    .iter()
                    .map(|sp| self.resolve_generic_field(string_store, sp, type_params))
                    .collect();

                self.instantiate_generic_struct(
                    string_store,
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
        string_store: &mut StringStore,
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
            let new_kind = self.resolve_generic_field(string_store, &field.kind, &param_lookup);
            resolved_fields.push(StructDefField {
                name: field.name,
                kind: new_kind,
            });
        }

        let new_def = StructDef {
            name: base_def.name,
            fields: resolved_fields,
            generic_params: Some(type_params.clone()),
            is_union: base_def.is_union,
        };

        let mut friendly_name = string_store.get_friendly_name(base_item_id).to_owned();
        let mut mangled_name = string_store.get_mangled_name(base_item_id).to_owned();
        friendly_name += stores::FRENDLY_GENERIC_OPEN;
        mangled_name += stores::MANGLED_GENERIC_OPEN;

        match type_params.as_slice() {
            [] => unreachable!(),
            [n] => {
                let ti = self.get_type_info(*n);
                let friendly_name_part = string_store.resolve(ti.friendly_name);
                let mangled_name_part = string_store.resolve(ti.mangled_name);
                friendly_name += friendly_name_part;
                mangled_name += mangled_name_part;
            }
            [n, xs @ ..] => {
                use std::fmt::Write;
                let ti = self.get_type_info(*n);
                let friendly_name_part = string_store.resolve(ti.friendly_name);
                let mangled_name_part = string_store.resolve(ti.mangled_name);
                let _ = write!(&mut friendly_name, "{friendly_name_part}");
                let _ = write!(&mut mangled_name, "{mangled_name_part}");

                for t in xs {
                    let ti = self.get_type_info(*t);
                    let friendly_name_part = string_store.resolve(ti.friendly_name);
                    let mangled_name_part = string_store.resolve(ti.mangled_name);
                    let _ = write!(
                        &mut friendly_name,
                        "{}{friendly_name_part}",
                        stores::FRENDLY_GENERIC_SEP
                    );
                    let _ = write!(
                        &mut mangled_name,
                        "{}{mangled_name_part}",
                        stores::MANGLED_GENERIC_SEP
                    );
                }
            }
        }

        friendly_name += stores::FRENDLY_GENERIC_CLOSE;
        mangled_name += stores::MANGLED_GENERIC_CLOSE;

        let friendly_name = string_store.intern(&friendly_name);
        let mangled_name = string_store.intern(&mangled_name);

        let type_id = self.add_type(
            friendly_name,
            mangled_name,
            base_type_info.location,
            TypeKind::GenericStructInstance(base_item_id),
        );
        self.fixed_struct_defs.insert(type_id, new_def);
        self.generic_struct_instance_map
            .insert((base_type_id, type_params), type_id);

        self.kinds[&type_id]
    }

    #[inline]
    pub fn get_type_info(&self, id: TypeId) -> TypeInfo {
        self.kinds[&id]
    }

    #[inline]
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
            // TODO: Integrate with PassContext
            TypeKind::Array { type_id, length } => {
                let mut inner_size = self.get_size_info(type_id);
                inner_size.byte_width =
                    next_multiple_of(inner_size.byte_width, inner_size.alignement)
                        * length.to_u64();
                inner_size
            }
            TypeKind::Integer(int) => TypeSize {
                byte_width: int.width.byte_width(),
                alignement: int.width.byte_width(),
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
                if struct_info.is_union {
                    // We just take the biggest size and biggest alignment here.
                    for field in &struct_info.fields {
                        let field_size = self.get_size_info(field.kind);
                        size_info.alignement = size_info.alignement.max(field_size.alignement);
                        size_info.byte_width = size_info.byte_width.max(field_size.byte_width);
                    }
                } else {
                    for field in &struct_info.fields {
                        let field_size = self.get_size_info(field.kind);
                        size_info.alignement = size_info.alignement.max(field_size.alignement);
                        size_info.byte_width =
                            next_multiple_of(size_info.byte_width, field_size.alignement)
                                + field_size.byte_width;
                    }
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
        string_store: &mut StringStore,
        struct_id: ItemId,
        def: &StructDef<NameResolvedType>,
    ) -> Result<TypeId, Spanned<Spur>> {
        if def.generic_params.is_some() {
            panic!("ICE: Tried to define fixed struct for a generic definition");
        }

        let mut resolved_fields = Vec::new();

        for field in &def.fields {
            let kind = self
                .resolve_type(string_store, &field.kind)
                .map_err(|_| field.name)?
                .id;
            resolved_fields.push(StructDefField {
                name: field.name,
                kind,
            });
        }

        let def = StructDef {
            name: def.name,
            fields: resolved_fields,
            generic_params: None,
            is_union: def.is_union,
        };

        let type_id = self.struct_id_map[&struct_id];
        self.fixed_struct_defs.insert(type_id, def);

        Ok(type_id)
    }

    #[track_caller]
    #[inline]
    pub fn get_struct_def(&self, id: TypeId) -> &StructDef<TypeId> {
        &self.fixed_struct_defs[&id]
    }

    #[track_caller]
    #[inline]
    pub fn get_generic_base_def(&self, id: TypeId) -> &GenericPartiallyResolvedStruct {
        &self.generic_struct_id_map[&id]
    }
}

pub fn emit_type_error_diag(stores: &Stores, token: Spanned<Spur>) {
    diagnostics::emit_error(
        stores,
        token.location,
        format!("unknown type `{}`", stores.strings.resolve(token.inner)),
        [Label::new(token.location).with_color(Color::Red)],
        None,
    );
}

fn next_multiple_of(a: u64, b: u64) -> u64 {
    let m = a & b;
    a + if m == 0 { 0 } else { b - m }
}
