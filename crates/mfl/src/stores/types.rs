use std::{hash::Hash, ops::RangeInclusive};

use ::stores::{
    items::ItemId,
    source::{SourceLocation, Spanned, WithSpan},
    strings::StringStore,
};
use hashbrown::HashMap;
use intcast::IntCast;
use lasso::Spur;
use smallvec::SmallVec;
use tracing::{debug_span, trace};

use crate::{
    ir::{NameResolvedType, PartiallyResolvedType, StructDef, StructDefField},
    stores::{self, item::ItemKind},
};

use super::{item::LangItem, Stores};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(u16);

impl std::fmt::Debug for TypeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypeId({})", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Integer {
    Signed(i64),
    Unsigned(u64),
}

impl Integer {
    pub fn is_zero(self) -> bool {
        matches!(self, Integer::Signed(0) | Integer::Unsigned(0))
    }

    pub fn to_signedness(self) -> IntSignedness {
        match self {
            Integer::Signed(_) => IntSignedness::Signed,
            Integer::Unsigned(_) => IntSignedness::Unsigned,
        }
    }

    // The cast has already been typechecked, so we know it's valid.
    pub fn cast(self, to: IntKind) -> Integer {
        match (self, to.signed) {
            (Integer::Signed(v), IntSignedness::Signed) if to.width == IntWidth::I64 => {
                Integer::Signed(v)
            }
            (Integer::Signed(v), IntSignedness::Signed) => {
                let (min, max) = to.width.bounds_signed().into_inner();
                let full_range = to.width.bounds_unsigned().into_inner().1 as i64;
                let v = if v < min {
                    v + full_range
                } else if v > max {
                    v - full_range
                } else {
                    v
                };
                Integer::Signed(v)
            }

            (Integer::Unsigned(v), IntSignedness::Unsigned) => {
                Integer::Unsigned(v & to.width.mask())
            }

            (Integer::Signed(v), IntSignedness::Unsigned) => {
                Integer::Unsigned((v & to.width.mask() as i64) as u64)
            }
            (Integer::Unsigned(v), IntSignedness::Signed) => {
                Integer::Signed((v & to.width.mask()) as i64)
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntWidth {
    I8,
    I16,
    I32,
    I64,
}

impl IntWidth {
    pub fn name(self, sign: IntSignedness) -> &'static str {
        match (self, sign) {
            (IntWidth::I8, IntSignedness::Signed) => "s8",
            (IntWidth::I16, IntSignedness::Signed) => "s16",
            (IntWidth::I32, IntSignedness::Signed) => "s32",
            (IntWidth::I64, IntSignedness::Signed) => "s64",
            (IntWidth::I8, IntSignedness::Unsigned) => "u8",
            (IntWidth::I16, IntSignedness::Unsigned) => "u16",
            (IntWidth::I32, IntSignedness::Unsigned) => "u32",
            (IntWidth::I64, IntSignedness::Unsigned) => "u64",
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
pub enum IntSignedness {
    Signed,
    Unsigned,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntKind {
    pub width: IntWidth,
    pub signed: IntSignedness,
}

impl IntKind {
    pub const U64: Self = Self {
        width: IntWidth::I64,
        signed: IntSignedness::Unsigned,
    };

    pub fn is_unsigned(self) -> bool {
        self.signed == IntSignedness::Unsigned
    }
}

impl From<(IntWidth, IntSignedness)> for IntKind {
    fn from(value: (IntWidth, IntSignedness)) -> Self {
        Self {
            width: value.0,
            signed: value.1,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum FloatWidth {
    F32,
    F64,
}

impl FloatWidth {
    pub fn name(self) -> &'static str {
        match self {
            FloatWidth::F32 => "f32",
            FloatWidth::F64 => "f64",
        }
    }

    pub fn bounds(self) -> RangeInclusive<f64> {
        match self {
            FloatWidth::F32 => f32::MIN as f64..=f32::MAX as f64,
            FloatWidth::F64 => f64::MIN..=f64::MAX,
        }
    }

    pub fn byte_width(self) -> u64 {
        match self {
            FloatWidth::F32 => 4,
            FloatWidth::F64 => 8,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Float(pub f64);
impl Float {
    pub(crate) fn cast(&self, output_float: FloatWidth) -> Float {
        match output_float {
            // Looks a bit dumb, but properly truncates the float.
            FloatWidth::F32 => Float(self.0 as f32 as f64),
            FloatWidth::F64 => Float(self.0),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionPointerArgs {
    pub inputs: SmallVec<[TypeId; 8]>,
    pub outputs: SmallVec<[TypeId; 8]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeKind {
    Array { type_id: TypeId, length: usize },
    Integer(IntKind),
    Float(FloatWidth),
    FunctionPointer,
    MultiPointer(TypeId),
    SinglePointer(TypeId),
    Bool,
    Enum(ItemId),
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
    F32,
    F64,
    Bool,
    String,
}

impl From<IntKind> for BuiltinTypes {
    fn from(value: IntKind) -> Self {
        match (value.signed, value.width) {
            (IntSignedness::Signed, IntWidth::I8) => BuiltinTypes::S8,
            (IntSignedness::Signed, IntWidth::I16) => BuiltinTypes::S16,
            (IntSignedness::Signed, IntWidth::I32) => BuiltinTypes::S32,
            (IntSignedness::Signed, IntWidth::I64) => BuiltinTypes::S64,
            (IntSignedness::Unsigned, IntWidth::I8) => BuiltinTypes::U8,
            (IntSignedness::Unsigned, IntWidth::I16) => BuiltinTypes::U16,
            (IntSignedness::Unsigned, IntWidth::I32) => BuiltinTypes::U32,
            (IntSignedness::Unsigned, IntWidth::I64) => BuiltinTypes::U64,
        }
    }
}

impl From<FloatWidth> for BuiltinTypes {
    fn from(width: FloatWidth) -> Self {
        match width {
            FloatWidth::F32 => BuiltinTypes::F32,
            FloatWidth::F64 => BuiltinTypes::F64,
        }
    }
}

impl Stores<'_, '_, '_, '_, '_, '_, '_, '_, '_, '_> {
    pub fn define_fixed_struct(
        &mut self,
        struct_id: ItemId,
        def: &StructDef<NameResolvedType>,
    ) -> Result<TypeId, Spanned<Spur>> {
        if !def.generic_params.is_empty() {
            panic!("ICE: Tried to define fixed struct for a generic definition");
        }

        let mut resolved_fields = Vec::new();

        for field in &def.fields {
            let kind = self
                .resolve_type(&field.kind.inner)
                .map_err(|_| field.name)?
                .id;
            resolved_fields.push(StructDefField {
                name: field.name,
                kind: kind.with_span(field.kind.location),
            });
        }

        let def = StructDef {
            name: def.name,
            fields: resolved_fields,
            generic_params: Vec::new(),
            is_union: def.is_union,
        };

        let type_id = self.types.custom_id_map[&struct_id];
        self.types.fixed_struct_defs.insert(type_id, def);

        Ok(type_id)
    }

    pub fn resolve_type(&mut self, tp: &NameResolvedType) -> Result<TypeInfo, Spanned<Spur>> {
        match tp {
            NameResolvedType::SimpleCustom { id, token } => {
                let item_header = self.items.get_item_header(*id);
                match item_header.kind {
                    ItemKind::StructDef | ItemKind::Enum => self
                        .types
                        .custom_id_map
                        .get(id)
                        .map(|id| self.types.kinds[id])
                        .ok_or(*token),
                    ItemKind::Primitive(type_id) => Ok(self.types.get_type_info(type_id)),

                    ItemKind::Assert
                    | ItemKind::Const
                    | ItemKind::Variable
                    | ItemKind::Function
                    | ItemKind::FunctionDecl
                    | ItemKind::GenericFunction
                    | ItemKind::Module => unreachable!(),
                }
            }
            NameResolvedType::FunctionPointer { inputs, outputs } => {
                let mut new_inputs = Vec::new();
                for kind in inputs {
                    let inner = self.resolve_type(kind)?;
                    new_inputs.push(inner.id);
                }

                let mut new_outputs = Vec::new();
                for kind in outputs {
                    let inner = self.resolve_type(kind)?;
                    new_outputs.push(inner.id);
                }

                Ok(self
                    .types
                    .get_function_pointer(self.strings, new_inputs, new_outputs))
            }
            NameResolvedType::Array(at, length) => {
                let inner = self.resolve_type(at)?;
                Ok(self.types.get_array(self.strings, inner.id, *length))
            }
            NameResolvedType::MultiPointer(pt) => {
                let pointee = self.resolve_type(pt)?;
                Ok(self.types.get_multi_pointer(self.strings, pointee.id))
            }
            NameResolvedType::SinglePointer(pt) => {
                let pointee = self.resolve_type(pt)?;
                Ok(self.types.get_single_pointer(self.strings, pointee.id))
            }
            NameResolvedType::GenericInstance { id, params, .. } => {
                let base_struct_id = self.types.custom_id_map[id];
                let param_type_ids: Vec<_> = params
                    .iter()
                    .map(|p| self.resolve_type(p).map(|ti| ti.id))
                    .collect::<Result<_, _>>()?;

                Ok(self.types.instantiate_generic_struct(
                    self.strings,
                    *id,
                    base_struct_id,
                    param_type_ids,
                ))
            }
            NameResolvedType::SimpleGenericParam(f) => Err(*f),
        }
    }

    pub fn partially_resolve_generic_type(
        &mut self,
        kind: &NameResolvedType,
    ) -> Result<PartiallyResolvedType, Spanned<Spur>> {
        let res = match kind {
            NameResolvedType::SimpleCustom { .. } => {
                let resolved = self.resolve_type(kind)?;
                PartiallyResolvedType::Fixed(resolved.id)
            }
            NameResolvedType::SimpleGenericParam(n) => {
                PartiallyResolvedType::GenericParamSimple(*n)
            }
            NameResolvedType::FunctionPointer { inputs, outputs } => {
                let mut new_inputs = Vec::new();
                for kind in inputs {
                    let inner = self.partially_resolve_generic_type(kind)?;
                    new_inputs.push(inner);
                }

                let mut new_outputs = Vec::new();
                for kind in outputs {
                    let inner = self.partially_resolve_generic_type(kind)?;
                    new_outputs.push(inner);
                }

                PartiallyResolvedType::GenericParamFunctionPointer {
                    inputs: new_inputs,
                    outputs: new_outputs,
                }
            }
            NameResolvedType::Array(sub_type, length) => {
                let inner_kind = self.partially_resolve_generic_type(sub_type)?;
                PartiallyResolvedType::GenericParamArray(Box::new(inner_kind), *length)
            }
            NameResolvedType::MultiPointer(sub_type) => {
                let inner_kind = self.partially_resolve_generic_type(sub_type)?;
                PartiallyResolvedType::GenericParamMultiPointer(Box::new(inner_kind))
            }
            NameResolvedType::SinglePointer(sub_type) => {
                let inner_kind = self.partially_resolve_generic_type(sub_type)?;
                PartiallyResolvedType::GenericParamSinglePointer(Box::new(inner_kind))
            }
            NameResolvedType::GenericInstance { id, params, .. } => {
                let generic_params = params
                    .iter()
                    .map(|gp| self.partially_resolve_generic_type(gp))
                    .collect::<Result<_, _>>()?;
                PartiallyResolvedType::GenericStruct(*id, generic_params)
            }
        };

        Ok(res)
    }

    pub fn partially_resolve_generic_struct(
        &mut self,
        base_item_id: ItemId,
        def: &StructDef<NameResolvedType>,
    ) {
        if def.generic_params.is_empty() {
            panic!("ICE: Tried to define generic struct for a non-generic definition");
        };

        let mut resolved_fields = Vec::new();

        for field in &def.fields {
            let field_kind = self
                .partially_resolve_generic_type(&field.kind.inner)
                .unwrap();

            resolved_fields.push(StructDefField {
                name: field.name,
                kind: field_kind.with_span(field.kind.location),
            });
        }

        let generic_base = StructDef {
            name: def.name,
            fields: resolved_fields,
            generic_params: def.generic_params.clone(),
            is_union: def.is_union,
        };

        let type_id = self.types.custom_id_map[&base_item_id];

        self.types
            .generic_struct_id_map
            .insert(type_id, generic_base);
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

#[derive(Debug)]
pub struct TypeStore {
    kinds: HashMap<TypeId, TypeInfo>,
    function_pointer_args: HashMap<TypeId, FunctionPointerArgs>,
    function_pointer_instance_map: HashMap<FunctionPointerArgs, TypeId>,
    multi_pointer_map: HashMap<TypeId, TypeId>,
    single_pointer_map: HashMap<TypeId, TypeId>,
    array_map: HashMap<(TypeId, usize), TypeId>,
    builtins: [TypeId; 12],

    // Maps ItemIds to TypeIds of non-generic structs.
    custom_id_map: HashMap<ItemId, TypeId>,
    lang_item_ids: HashMap<ItemId, LangItem>,
    fixed_struct_defs: HashMap<TypeId, StructDef<TypeId>>,
    generic_struct_id_map: HashMap<TypeId, StructDef<PartiallyResolvedType>>,
    generic_struct_instance_map: HashMap<(TypeId, Vec<TypeId>), TypeId>,

    type_sizes: HashMap<TypeId, TypeSize>,
}

impl TypeStore {
    pub fn new(string_store: &mut StringStore) -> Self {
        let mut s = Self {
            kinds: HashMap::new(),
            function_pointer_args: HashMap::new(),
            function_pointer_instance_map: HashMap::new(),
            multi_pointer_map: HashMap::new(),
            single_pointer_map: HashMap::new(),
            array_map: HashMap::new(),
            builtins: [TypeId(0); 12],
            custom_id_map: HashMap::new(),
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
                TypeKind::Integer((IntWidth::I8, IntSignedness::Unsigned).into()),
            ),
            (
                "u16",
                BuiltinTypes::U16,
                TypeKind::Integer((IntWidth::I16, IntSignedness::Unsigned).into()),
            ),
            (
                "u32",
                BuiltinTypes::U32,
                TypeKind::Integer((IntWidth::I32, IntSignedness::Unsigned).into()),
            ),
            (
                "u64",
                BuiltinTypes::U64,
                TypeKind::Integer((IntWidth::I64, IntSignedness::Unsigned).into()),
            ),
            (
                "s8",
                BuiltinTypes::S8,
                TypeKind::Integer((IntWidth::I8, IntSignedness::Signed).into()),
            ),
            (
                "s16",
                BuiltinTypes::S16,
                TypeKind::Integer((IntWidth::I16, IntSignedness::Signed).into()),
            ),
            (
                "s32",
                BuiltinTypes::S32,
                TypeKind::Integer((IntWidth::I32, IntSignedness::Signed).into()),
            ),
            (
                "s64",
                BuiltinTypes::S64,
                TypeKind::Integer((IntWidth::I64, IntSignedness::Signed).into()),
            ),
            ("f32", BuiltinTypes::F32, TypeKind::Float(FloatWidth::F32)),
            ("f64", BuiltinTypes::F64, TypeKind::Float(FloatWidth::F64)),
            ("bool", BuiltinTypes::Bool, TypeKind::Bool),
        ];

        for (name_str, builtin, kind) in builtins {
            let name = string_store.intern(name_str);
            let id = self.add_type(name, name, None, kind);
            self.builtins[builtin as usize] = id;

            // A couple parts of the compiler need to construct pointers to basic types.
            self.get_multi_pointer(string_store, id);
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
            self.custom_id_map.insert(struct_id, id);
            if self.lang_item_ids.get(&struct_id) == Some(&LangItem::String) {
                self.builtins[BuiltinTypes::String as usize] = id;
            }
        } else if let TypeKind::Enum(enum_id) = kind {
            self.custom_id_map.insert(enum_id, id);
        }

        id
    }

    pub fn get_function_pointer(
        &mut self,
        string_store: &mut StringStore,
        inputs: Vec<TypeId>,
        outputs: Vec<TypeId>,
    ) -> TypeInfo {
        let args = FunctionPointerArgs {
            inputs: inputs.into(),
            outputs: outputs.into(),
        };

        if let Some(id) = self.function_pointer_instance_map.get(&args) {
            return self.get_type_info(*id);
        }

        let _span = debug_span!(stringify!(get_function_pointer)).entered();
        trace!(?args);

        let mut friendly_name = "proc".to_owned();
        let mut mangled_name = "proc".to_owned();
        friendly_name += stores::FRENDLY_ARRAY_OPEN;
        mangled_name += stores::MANGLED_ARRAY_OPEN;

        self.mangle_type_list(
            &args.inputs,
            string_store,
            &mut friendly_name,
            &mut mangled_name,
        );

        friendly_name += stores::FRENDLY_ARRAY_CLOSE;
        mangled_name += stores::MANGLED_ARRAY_CLOSE;

        friendly_name += " to ";

        friendly_name += stores::FRENDLY_ARRAY_OPEN;
        mangled_name += stores::MANGLED_ARRAY_OPEN;

        self.mangle_type_list(
            &args.outputs,
            string_store,
            &mut friendly_name,
            &mut mangled_name,
        );

        friendly_name += stores::FRENDLY_ARRAY_CLOSE;
        mangled_name += stores::MANGLED_ARRAY_CLOSE;

        let friendly_name = string_store.intern(&friendly_name);
        let mangled_name = string_store.intern(&mangled_name);

        let new_type_id =
            self.add_type(friendly_name, mangled_name, None, TypeKind::FunctionPointer);
        trace!(?new_type_id);

        self.function_pointer_args.insert(new_type_id, args.clone());
        self.function_pointer_instance_map.insert(args, new_type_id);

        self.kinds[&new_type_id]
    }

    pub fn get_multi_pointer(
        &mut self,
        string_store: &mut StringStore,
        pointee_id: TypeId,
    ) -> TypeInfo {
        let pointee = self.get_type_info(pointee_id);

        if let Some(pi) = self.multi_pointer_map.get(&pointee.id) {
            self.kinds[pi]
        } else {
            let pointer_id = self.make_pointer_impl(
                string_store,
                pointee,
                TypeKind::MultiPointer,
                stores::FRENDLY_PTR_MULTI,
                stores::MANGLED_PTR_MULTI,
            );
            self.multi_pointer_map.insert(pointee.id, pointer_id);

            self.kinds[&pointer_id]
        }
    }

    pub fn get_single_pointer(
        &mut self,
        string_store: &mut StringStore,
        pointee_id: TypeId,
    ) -> TypeInfo {
        let pointee = self.get_type_info(pointee_id);

        if let Some(pi) = self.single_pointer_map.get(&pointee.id) {
            self.kinds[pi]
        } else {
            let pointer_id = self.make_pointer_impl(
                string_store,
                pointee,
                TypeKind::SinglePointer,
                stores::FRENDLY_PTR_SINGLE,
                stores::MANGLED_PTR_SINGLE,
            );
            self.single_pointer_map.insert(pointee.id, pointer_id);

            self.kinds[&pointer_id]
        }
    }

    fn make_pointer_impl(
        &mut self,
        string_store: &mut StringStore,
        pointee: TypeInfo,
        cons: fn(TypeId) -> TypeKind,
        friendly_part: &str,
        mangle_part: &str,
    ) -> TypeId {
        let pointee_friendly_name = string_store.resolve(pointee.friendly_name);
        let friendly_name = format!("{pointee_friendly_name}{friendly_part}");
        let friendly_name = string_store.intern(&friendly_name);

        let pointee_mangled_name = string_store.resolve(pointee.mangled_name);
        let mangled_name = format!("{pointee_mangled_name}{mangle_part}");
        let mangled_name = string_store.intern(&mangled_name);

        self.add_type(friendly_name, mangled_name, None, cons(pointee.id))
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

    // FIXME: This sholud return Option.
    pub fn resolve_generic_type(
        &mut self,
        string_store: &mut StringStore,
        kind: &PartiallyResolvedType,
        type_params: &HashMap<Spur, TypeId>,
    ) -> TypeId {
        match kind {
            PartiallyResolvedType::Fixed(id) => *id,
            PartiallyResolvedType::GenericParamSimple(n) => type_params[&n.inner],
            PartiallyResolvedType::GenericParamFunctionPointer { inputs, outputs } => {
                let new_inputs = inputs
                    .iter()
                    .map(|sub_type| self.resolve_generic_type(string_store, sub_type, type_params))
                    .collect();
                let new_outputs = outputs
                    .iter()
                    .map(|sub_type| self.resolve_generic_type(string_store, sub_type, type_params))
                    .collect();

                self.get_function_pointer(string_store, new_inputs, new_outputs)
                    .id
            }
            PartiallyResolvedType::GenericParamMultiPointer(sub_type) => {
                let pointee_id = self.resolve_generic_type(string_store, sub_type, type_params);
                self.get_multi_pointer(string_store, pointee_id).id
            }
            PartiallyResolvedType::GenericParamSinglePointer(sub_type) => {
                let pointee_id = self.resolve_generic_type(string_store, sub_type, type_params);
                self.get_single_pointer(string_store, pointee_id).id
            }
            PartiallyResolvedType::GenericParamArray(sub_type, length) => {
                let content_type_id =
                    self.resolve_generic_type(string_store, sub_type, type_params);
                self.get_array(string_store, content_type_id, *length).id
            }
            PartiallyResolvedType::GenericStruct(base_struct_id, sub_params) => {
                let base_struct_type_id = self.custom_id_map[base_struct_id];

                let sub_params: Vec<_> = sub_params
                    .iter()
                    .map(|sp| self.resolve_generic_type(string_store, sp, type_params))
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

        let _span = debug_span!(stringify!(instantiate_generic_struct)).entered();
        trace!(?base_item_id, ?base_type_id, ?type_params,);

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
            let new_kind =
                self.resolve_generic_type(string_store, &field.kind.inner, &param_lookup);
            resolved_fields.push(StructDefField {
                name: field.name,
                kind: new_kind.with_span(field.kind.location),
            });
        }

        let new_def = StructDef {
            name: base_def.name,
            fields: resolved_fields,
            generic_params: type_params.clone(),
            is_union: base_def.is_union,
        };

        let mut friendly_name = string_store.get_friendly_name(base_item_id).to_owned();
        let mut mangled_name = string_store.get_mangled_name(base_item_id).to_owned();
        friendly_name += stores::FRENDLY_GENERIC_OPEN;
        mangled_name += stores::MANGLED_GENERIC_OPEN;

        self.mangle_type_list(
            &type_params,
            string_store,
            &mut friendly_name,
            &mut mangled_name,
        );

        friendly_name += stores::FRENDLY_GENERIC_CLOSE;
        mangled_name += stores::MANGLED_GENERIC_CLOSE;

        let friendly_name = string_store.intern(&friendly_name);
        let mangled_name = string_store.intern(&mangled_name);

        let new_type_id = self.add_type(
            friendly_name,
            mangled_name,
            base_type_info.location,
            TypeKind::GenericStructInstance(base_item_id),
        );
        trace!(?new_type_id);
        self.fixed_struct_defs.insert(new_type_id, new_def);
        self.generic_struct_instance_map
            .insert((base_type_id, type_params), new_type_id);

        self.kinds[&new_type_id]
    }

    fn mangle_type_list(
        &mut self,
        type_params: &[TypeId],
        string_store: &mut StringStore,
        friendly_name: &mut String,
        mangled_name: &mut String,
    ) {
        match type_params {
            [] => {}
            [n] => {
                let ti = self.get_type_info(*n);
                let friendly_name_part = string_store.resolve(ti.friendly_name);
                let mangled_name_part = string_store.resolve(ti.mangled_name);
                *friendly_name += friendly_name_part;
                *mangled_name += mangled_name_part;
            }
            [n, xs @ ..] => {
                use std::fmt::Write;
                let ti = self.get_type_info(*n);
                let friendly_name_part = string_store.resolve(ti.friendly_name);
                let mangled_name_part = string_store.resolve(ti.mangled_name);
                let _ = write!(friendly_name, "{friendly_name_part}");
                let _ = write!(mangled_name, "{mangled_name_part}");

                for t in xs {
                    let ti = self.get_type_info(*t);
                    let friendly_name_part = string_store.resolve(ti.friendly_name);
                    let mangled_name_part = string_store.resolve(ti.mangled_name);
                    let _ = write!(
                        friendly_name,
                        "{}{friendly_name_part}",
                        stores::FRENDLY_GENERIC_SEP
                    );
                    let _ = write!(
                        mangled_name,
                        "{}{mangled_name_part}",
                        stores::MANGLED_GENERIC_SEP
                    );
                }
            }
        }
    }

    #[inline]
    pub fn get_type_info(&self, id: TypeId) -> TypeInfo {
        self.kinds[&id]
    }

    #[inline]
    pub fn get_builtin(&self, id: BuiltinTypes) -> TypeInfo {
        self.kinds[&self.builtins[id as usize]]
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
            TypeKind::Float(float) => TypeSize {
                byte_width: float.byte_width(),
                alignement: float.byte_width(),
            },
            TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) | TypeKind::FunctionPointer => {
                TypeSize {
                    byte_width: 8,
                    alignement: 8,
                }
            }
            TypeKind::Bool => TypeSize {
                byte_width: 1,
                alignement: 1,
            },
            // Just represent as a u16 for now.
            TypeKind::Enum(_) => TypeSize {
                byte_width: 2,
                alignement: 2,
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
                        let field_size = self.get_size_info(field.kind.inner);
                        size_info.alignement = size_info.alignement.max(field_size.alignement);
                        size_info.byte_width = size_info.byte_width.max(field_size.byte_width);
                    }
                } else {
                    for field in &struct_info.fields {
                        let field_size = self.get_size_info(field.kind.inner);
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

    #[track_caller]
    #[inline]
    pub fn get_struct_def(&self, id: TypeId) -> &StructDef<TypeId> {
        &self.fixed_struct_defs[&id]
    }

    #[track_caller]
    #[inline]
    pub fn get_generic_base_def(&self, id: TypeId) -> &StructDef<PartiallyResolvedType> {
        &self.generic_struct_id_map[&id]
    }

    #[track_caller]
    #[inline]
    pub fn get_function_pointer_args(&self, id: TypeId) -> &FunctionPointerArgs {
        &self.function_pointer_args[&id]
    }
}

fn next_multiple_of(a: u64, b: u64) -> u64 {
    let m = a & b;
    a + if m == 0 { 0 } else { b - m }
}
