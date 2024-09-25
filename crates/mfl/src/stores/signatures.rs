use hashbrown::HashMap;
use lasso::Spur;
use stores::{
    items::ItemId,
    source::{SourceLocation, Spanned, WithSpan},
};

use crate::{
    ir::{
        EnumDef, NameResolvedType, PartiallyResolvedType, StructDef, UnresolvedIdent,
        UnresolvedType,
    },
    option::OptionExt,
    stores::types::TypeId,
};

pub struct SigStore {
    pub urir: UnresolvedIr,
    pub nrir: NameResolvedIr,
    pub trir: TypeResolvedIr,
}

impl SigStore {
    pub fn new() -> Self {
        Self {
            urir: UnresolvedIr::new(),
            nrir: NameResolvedIr::new(),
            trir: TypeResolvedIr::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum StackDefItemUnresolved {
    Var {
        name: Spanned<Spur>,
        kind: Spanned<UnresolvedType>,
    },
    Stack(Spanned<UnresolvedType>),
}

#[derive(Debug, Clone)]
pub struct UnresolvedItemSignature {
    pub exit: Spanned<Vec<Spanned<UnresolvedType>>>,
    pub entry: Spanned<Vec<StackDefItemUnresolved>>,
}

pub struct UnresolvedIr {
    item_signatures: HashMap<ItemId, UnresolvedItemSignature>,
    variable_type: HashMap<ItemId, Spanned<UnresolvedType>>,
    structs: HashMap<ItemId, StructDef<UnresolvedType>>,
    enums: HashMap<ItemId, EnumDef>,
    scopes: HashMap<ItemId, UnresolvedScope>,
}

impl UnresolvedIr {
    #[inline]
    #[track_caller]
    pub fn set_item_signature(&mut self, id: ItemId, sig: UnresolvedItemSignature) {
        self.item_signatures
            .insert(id, sig)
            .expect_none("ICE: Overwrote signature")
    }

    #[inline]
    #[track_caller]
    pub fn get_item_signature(&self, id: ItemId) -> &UnresolvedItemSignature {
        &self.item_signatures[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_variable_type(&mut self, id: ItemId, ty: Spanned<UnresolvedType>) {
        self.variable_type
            .insert(id, ty)
            .expect_none("ICE: Overwrote variable type");
    }

    #[inline]
    #[track_caller]
    pub fn get_variable_type(&self, id: ItemId) -> Spanned<&UnresolvedType> {
        let v = &self.variable_type[&id];
        (&v.inner).with_span(v.location)
    }

    #[inline]
    #[track_caller]
    pub fn new_scope(&mut self, id: ItemId) {
        self.scopes
            .insert(id, UnresolvedScope::new())
            .expect_none("ICE: Overwrite scope");
    }

    #[inline]
    #[track_caller]
    pub fn get_scope(&self, id: ItemId) -> &UnresolvedScope {
        &self.scopes[&id]
    }

    #[inline]
    #[track_caller]
    pub fn get_scope_mut(&mut self, id: ItemId) -> &mut UnresolvedScope {
        self.scopes.get_mut(&id).unwrap()
    }

    #[inline]
    #[track_caller]
    pub fn set_enum(&mut self, id: ItemId, def: EnumDef) {
        self.enums
            .insert(id, def)
            .expect_none("ICE: Overwrote enum def")
    }

    #[inline]
    #[track_caller]
    pub fn get_enum(&self, id: ItemId) -> &EnumDef {
        &self.enums[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_struct(&mut self, id: ItemId, def: StructDef<UnresolvedType>) {
        self.structs
            .insert(id, def)
            .expect_none("ICE: Overwrote struct def")
    }

    #[inline]
    #[track_caller]
    pub fn get_struct(&self, id: ItemId) -> &StructDef<UnresolvedType> {
        &self.structs[&id]
    }
}

impl UnresolvedIr {
    pub fn new() -> Self {
        UnresolvedIr {
            item_signatures: HashMap::new(),
            variable_type: HashMap::new(),
            structs: HashMap::new(),
            enums: HashMap::new(),
            scopes: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum StackDefItemNameResolved {
    Var {
        name: ItemId,
        kind: NameResolvedType,
    },
    Stack(NameResolvedType),
}

#[derive(Debug, Clone)]
pub struct NameResolvedItemSignature {
    pub exit: Vec<NameResolvedType>,
    pub entry: Vec<StackDefItemNameResolved>,
    // While it seems odd, this will only be populated when instantiating a generic function,
    // which has the resolved TypeIds of the parameters.
    pub generic_params: Vec<TypeId>,
}

pub struct NameResolvedIr {
    item_signatures: HashMap<ItemId, NameResolvedItemSignature>,
    variable_type: HashMap<ItemId, NameResolvedType>,
    structs: HashMap<ItemId, StructDef<NameResolvedType>>,
    scopes: HashMap<ItemId, NameResolvedScope>,
}

impl NameResolvedIr {
    #[inline]
    #[track_caller]
    pub fn get_item_signature(&self, id: ItemId) -> &NameResolvedItemSignature {
        &self.item_signatures[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_item_signature(&mut self, id: ItemId, sig: NameResolvedItemSignature) {
        self.item_signatures
            .insert(id, sig)
            .expect_none("Redefined item signature");
    }

    #[inline]
    #[track_caller]
    pub fn get_variable_type(&self, id: ItemId) -> &NameResolvedType {
        &self.variable_type[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_variable_type(&mut self, id: ItemId, def: NameResolvedType) {
        self.variable_type
            .insert(id, def)
            .expect_none("Redefined variable type");
    }

    #[inline]
    #[track_caller]
    pub fn new_scope(&mut self, id: ItemId) {
        self.scopes
            .insert(id, NameResolvedScope::new())
            .expect_none("ICE: Overwrote scope");
    }

    #[inline]
    #[track_caller]
    pub fn get_scope(&self, id: ItemId) -> &NameResolvedScope {
        &self.scopes[&id]
    }

    #[inline]
    #[track_caller]
    pub fn get_scope_mut(&mut self, id: ItemId) -> &mut NameResolvedScope {
        self.scopes.get_mut(&id).unwrap()
    }

    #[inline]
    #[track_caller]
    pub fn get_struct(&self, id: ItemId) -> &StructDef<NameResolvedType> {
        &self.structs[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_struct(&mut self, id: ItemId, def: StructDef<NameResolvedType>) {
        self.structs.insert(id, def).expect_none("Redefined struct");
    }
}

impl NameResolvedIr {
    pub fn new() -> Self {
        NameResolvedIr {
            item_signatures: HashMap::new(),
            variable_type: HashMap::new(),
            structs: HashMap::new(),
            scopes: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeResolvedItemSignature {
    pub exit: Vec<TypeId>,
    pub entry: Vec<TypeId>,
    pub generic_params: Vec<TypeId>,
}

pub struct PartiallyTypeResolvedItemSignature {
    pub exit: Vec<PartiallyResolvedType>,
    pub entry: Vec<PartiallyResolvedType>,
}

pub struct TypeResolvedIr {
    partial_item_signatures: HashMap<ItemId, PartiallyTypeResolvedItemSignature>,
    item_signatures: HashMap<ItemId, TypeResolvedItemSignature>,
    partial_variable_types: HashMap<ItemId, PartiallyResolvedType>,
    variable_type: HashMap<ItemId, TypeId>,
}

impl TypeResolvedIr {
    #[inline]
    #[track_caller]
    pub fn get_item_signature(&self, id: ItemId) -> &TypeResolvedItemSignature {
        &self.item_signatures[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_item_signature(&mut self, id: ItemId, sig: TypeResolvedItemSignature) {
        self.item_signatures
            .insert(id, sig)
            .expect_none("Redefined item signature");
    }

    #[inline]
    #[track_caller]
    pub fn get_partial_item_signature(&self, id: ItemId) -> &PartiallyTypeResolvedItemSignature {
        &self.partial_item_signatures[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_partial_item_signature(
        &mut self,
        id: ItemId,
        sig: PartiallyTypeResolvedItemSignature,
    ) {
        self.partial_item_signatures
            .insert(id, sig)
            .expect_none("Redefined item signature");
    }

    #[inline]
    #[track_caller]
    pub fn get_variable_type(&self, id: ItemId) -> TypeId {
        self.variable_type[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_variable_type(&mut self, id: ItemId, mem_type: TypeId) {
        self.variable_type
            .insert(id, mem_type)
            .expect_none("Redefined variable type");
    }

    #[inline]
    #[track_caller]
    pub fn get_partial_variable_type(&self, id: ItemId) -> &PartiallyResolvedType {
        &self.partial_variable_types[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_partial_variable_type(&mut self, id: ItemId, mem_type: PartiallyResolvedType) {
        self.partial_variable_types
            .insert(id, mem_type)
            .expect_none("Redefined variable type");
    }
}

impl TypeResolvedIr {
    pub fn new() -> Self {
        TypeResolvedIr {
            partial_item_signatures: HashMap::new(),
            item_signatures: HashMap::new(),
            partial_variable_types: HashMap::new(),
            variable_type: HashMap::new(),
        }
    }
}

pub struct UnresolvedScope {
    imports: Vec<UnresolvedIdent>,
}

impl UnresolvedScope {
    pub fn add_unresolved_import(&mut self, path: UnresolvedIdent) {
        self.imports.push(path);
    }

    pub fn imports(&self) -> &[UnresolvedIdent] {
        &self.imports
    }

    pub fn new() -> UnresolvedScope {
        UnresolvedScope {
            imports: Vec::new(),
        }
    }
}

// Defines how strongly an item is imported.
// A weak import can be overwritten by later imports, while a strong one cannot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportStrength {
    Strong,
    Weak,
}

#[derive(Debug, Clone, Copy)]
struct Import {
    id: Spanned<ItemId>,
    strength: ImportStrength,
}

#[derive(Debug, Clone)]
pub struct NameResolvedScope {
    child_items: Vec<ItemId>,
    visible_symbols: HashMap<Spur, Import>,
}

impl NameResolvedScope {
    #[inline]
    pub fn get_symbol(&self, name: Spur) -> Option<ItemId> {
        self.visible_symbols.get(&name).map(|id| id.id.inner)
    }

    #[inline]
    pub fn get_child_items(&self) -> &[ItemId] {
        &self.child_items
    }

    pub fn add_child(&mut self, id: ItemId) {
        self.child_items.push(id);
    }

    pub fn add_visible_symbol(
        &mut self,
        symbol: Spanned<Spur>,
        id: ItemId,
        strength: ImportStrength,
    ) -> Result<(), SourceLocation> {
        use hashbrown::hash_map::Entry;

        match self.visible_symbols.entry(symbol.inner) {
            Entry::Occupied(mut a) => {
                if a.get().strength == ImportStrength::Weak {
                    a.get_mut().id = id.with_span(symbol.location);
                } else {
                    return Err(a.get().id.location);
                }
            }
            Entry::Vacant(a) => {
                a.insert(Import {
                    id: id.with_span(symbol.location),
                    strength,
                });
            }
        }

        Ok(())
    }

    pub fn new() -> NameResolvedScope {
        NameResolvedScope {
            child_items: Vec::new(),
            visible_symbols: HashMap::new(),
        }
    }
}
