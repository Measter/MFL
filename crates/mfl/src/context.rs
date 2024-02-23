use ariadne::{Color, Label};
use hashbrown::HashMap;
use intcast::IntCast;
use lasso::Spur;

use crate::{
    diagnostics,
    ir::UnresolvedIdent,
    option::OptionExt,
    pass_manager::static_analysis::Analyzer,
    simulate::SimulatorValue,
    source_file::{SourceLocation, Spanned, WithSpan},
    type_store::{TypeId, UnresolvedStruct, UnresolvedTypeIds, UnresolvedTypeTokens},
    Stores,
};

use super::ir::{NameResolvedOp, Op, TypeResolvedOp, UnresolvedOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangItem {
    String,
    Alloc,
    Free,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ItemId(u16);

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ItemKind {
    Assert,
    Const,
    Memory,
    Function,
    GenericFunction,
    StructDef,
    Module,
}

#[derive(Debug, Clone, Copy)]
pub struct ItemHeader {
    pub name: Spanned<Spur>,
    pub id: ItemId,
    pub parent: Option<ItemId>,
    pub kind: ItemKind,
    pub lang_item: Option<LangItem>,
}

pub struct UnresolvedItemSignature {
    pub exit: Spanned<Vec<Spanned<UnresolvedTypeTokens>>>,
    pub entry: Spanned<Vec<Spanned<UnresolvedTypeTokens>>>,
}

pub struct UnresolvedIr {
    item_signatures: HashMap<ItemId, UnresolvedItemSignature>,
    memory_type: HashMap<ItemId, Spanned<UnresolvedTypeTokens>>,
    item_bodies: HashMap<ItemId, Vec<Op<UnresolvedOp>>>,
    structs: HashMap<ItemId, UnresolvedStruct>,
    scopes: Vec<UnresolvedScope>,
}

impl UnresolvedIr {
    #[inline]
    #[track_caller]
    pub fn get_item_signature(&self, id: ItemId) -> &UnresolvedItemSignature {
        &self.item_signatures[&id]
    }

    #[inline]
    #[track_caller]
    pub fn get_memory_type(&self, id: ItemId) -> Spanned<&UnresolvedTypeTokens> {
        let v = &self.memory_type[&id];
        (&v.inner).with_span(v.location)
    }

    #[inline]
    #[track_caller]
    pub fn get_item_body(&self, id: ItemId) -> &[Op<UnresolvedOp>] {
        &self.item_bodies[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_item_body(&mut self, id: ItemId, body: Vec<Op<UnresolvedOp>>) {
        self.item_bodies.insert(id, body);
    }

    #[inline]
    #[track_caller]
    pub fn get_scope(&self, id: ItemId) -> &UnresolvedScope {
        &self.scopes[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_scope_mut(&mut self, id: ItemId) -> &mut UnresolvedScope {
        &mut self.scopes[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_struct(&self, id: ItemId) -> &UnresolvedStruct {
        &self.structs[&id]
    }
}

impl UnresolvedIr {
    fn new() -> Self {
        UnresolvedIr {
            item_signatures: HashMap::new(),
            memory_type: HashMap::new(),
            item_bodies: HashMap::new(),
            structs: HashMap::new(),
            scopes: Vec::new(),
        }
    }
}

pub struct NameResolvedItemSignature {
    pub exit: Vec<UnresolvedTypeIds>,
    pub entry: Vec<UnresolvedTypeIds>,
}

pub struct NameResolvedIr {
    item_signatures: HashMap<ItemId, NameResolvedItemSignature>,
    memory_type: HashMap<ItemId, UnresolvedTypeIds>,
    item_bodies: HashMap<ItemId, Vec<Op<NameResolvedOp>>>,
    // Need to split this UnresolvedStruct business.
    structs: HashMap<ItemId, UnresolvedStruct>,
    scopes: Vec<NameResolvedScope>,
}

impl NameResolvedIr {
    #[inline]
    #[track_caller]
    pub fn get_item_signature(&self, id: ItemId) -> &NameResolvedItemSignature {
        &self.item_signatures[&id]
    }

    #[inline]
    #[track_caller]
    pub fn get_memory_type(&self, id: ItemId) -> &UnresolvedTypeIds {
        &self.memory_type[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_memory_type(&mut self, id: ItemId, def: UnresolvedTypeIds) {
        self.memory_type
            .insert(id, def)
            .expect_none("Redefined memory type");
    }

    #[inline]
    #[track_caller]
    pub fn get_item_body(&self, id: ItemId) -> &[Op<NameResolvedOp>] {
        &self.item_bodies[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_item_body(&mut self, id: ItemId, body: Vec<Op<NameResolvedOp>>) {
        self.item_bodies.insert(id, body);
    }

    #[inline]
    #[track_caller]
    pub fn get_scope(&self, id: ItemId) -> &NameResolvedScope {
        &self.scopes[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_scope_mut(&mut self, id: ItemId) -> &mut NameResolvedScope {
        &mut self.scopes[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn set_struct(&mut self, id: ItemId, def: UnresolvedStruct) {
        self.structs.insert(id, def).expect_none("Redefined struct");
    }
}

impl NameResolvedIr {
    fn new() -> Self {
        NameResolvedIr {
            item_signatures: HashMap::new(),
            memory_type: HashMap::new(),
            item_bodies: HashMap::new(),
            structs: HashMap::new(),
            scopes: Vec::new(),
        }
    }
}

pub struct TypeResolvedItemSignature {
    pub exit: Vec<TypeId>,
    pub entry: Vec<TypeId>,
}

pub struct TypeResolvedIr {
    item_signatures: HashMap<ItemId, TypeResolvedItemSignature>,
    memory_type: HashMap<ItemId, TypeId>,
    item_bodies: HashMap<ItemId, Vec<Op<TypeResolvedOp>>>,
}

impl TypeResolvedIr {
    #[inline]
    #[track_caller]
    pub fn get_item_signature(&self, id: ItemId) -> &TypeResolvedItemSignature {
        &self.item_signatures[&id]
    }

    #[inline]
    #[track_caller]
    pub fn get_memory_type(&self, id: ItemId) -> TypeId {
        self.memory_type[&id]
    }

    #[inline]
    #[track_caller]
    pub fn get_item_body(&self, id: ItemId) -> &[Op<TypeResolvedOp>] {
        &self.item_bodies[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_item_body(&mut self, id: ItemId, body: Vec<Op<TypeResolvedOp>>) {
        self.item_bodies.insert(id, body);
    }
}

impl TypeResolvedIr {
    fn new() -> Self {
        TypeResolvedIr {
            item_signatures: HashMap::new(),
            memory_type: HashMap::new(),
            item_bodies: HashMap::new(),
        }
    }
}

pub struct Context {
    top_level_modules: HashMap<Spur, ItemId>,
    lang_items: HashMap<LangItem, ItemId>,

    headers: Vec<ItemHeader>,
    analyzers: HashMap<ItemId, Analyzer>,
    const_vals: HashMap<ItemId, Vec<(TypeId, SimulatorValue)>>,

    urir: UnresolvedIr,
    nrir: NameResolvedIr,
    trir: TypeResolvedIr,

    // Bit of a hacky workaround for how I've done the struct resolution.
    generic_structs: Vec<ItemId>,
    generic_function_cache: HashMap<(ItemId, String), ItemId>,
    generic_template_parameters: HashMap<ItemId, Vec<Spanned<Spur>>>,
}

impl Context {
    #[inline]
    pub fn get_all_items(&self) -> impl Iterator<Item = ItemHeader> + '_ {
        self.headers.iter().copied()
    }

    pub fn get_lang_items(&self) -> &HashMap<LangItem, ItemId> {
        &self.lang_items
    }

    #[inline]
    pub fn urir(&self) -> &UnresolvedIr {
        &self.urir
    }

    #[inline]
    pub fn urir_mut(&mut self) -> &mut UnresolvedIr {
        &mut self.urir
    }

    #[inline]
    pub fn nrir(&self) -> &NameResolvedIr {
        &self.nrir
    }

    #[inline]
    pub fn nrir_mut(&mut self) -> &mut NameResolvedIr {
        &mut self.nrir
    }

    #[inline]
    pub fn trir(&self) -> &TypeResolvedIr {
        &self.trir
    }

    #[inline]
    pub fn trir_mut(&mut self) -> &mut TypeResolvedIr {
        &mut self.trir
    }

    #[inline]
    pub fn get_top_level_module(&self, name: Spur) -> Option<ItemId> {
        self.top_level_modules.get(&name).copied()
    }

    #[inline]
    pub fn get_item_header(&self, id: ItemId) -> ItemHeader {
        self.headers[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_analyzer(&self, id: ItemId) -> &Analyzer {
        &self.analyzers[&id]
    }

    #[inline]
    #[track_caller]
    pub fn get_consts(&self, id: ItemId) -> Option<&[(TypeId, SimulatorValue)]> {
        self.const_vals.get(&id).map(|v| &**v)
    }

    pub fn get_generic_structs(&self) -> &[ItemId] {
        &self.generic_structs
    }

    #[inline]
    #[track_caller]
    pub fn get_function_template_paramaters(&self, id: ItemId) -> &[Spanned<Spur>] {
        &self.generic_template_parameters[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_new_function_instance(
        &mut self,
        base_id: ItemId,
        new_name: String,
        instance_id: ItemId,
    ) {
        self.generic_function_cache
            .insert((base_id, new_name), instance_id);
    }
}

impl Context {
    pub fn new() -> Self {
        Context {
            top_level_modules: HashMap::new(),
            lang_items: HashMap::new(),
            headers: Vec::new(),
            analyzers: HashMap::new(),
            const_vals: HashMap::new(),
            urir: UnresolvedIr::new(),
            nrir: NameResolvedIr::new(),
            trir: TypeResolvedIr::new(),
            generic_structs: Vec::new(),
            generic_function_cache: HashMap::new(),
            generic_template_parameters: HashMap::new(),
        }
    }

    fn add_to_parent(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        parent_id: ItemId,
        child_name: Spanned<Spur>,
        child_id: ItemId,
    ) {
        let parent_scope = &mut self.nrir.scopes[parent_id.0.to_usize()];
        if let Err(prev_loc) = parent_scope.add_child(child_name, child_id) {
            *had_error = true;
            make_symbol_redef_error(stores, child_name.location, prev_loc);
        }
    }

    fn new_header(
        &mut self,
        name: Spanned<Spur>,
        parent: Option<ItemId>,
        kind: ItemKind,
    ) -> ItemHeader {
        let new_id = self.headers.len();
        let new_id = ItemId(new_id.to_u16().unwrap());

        let item_header = ItemHeader {
            name,
            id: new_id,
            parent,
            kind,
            lang_item: None,
        };

        self.headers.push(item_header);
        self.urir.scopes.push(UnresolvedScope::new());
        self.nrir.scopes.push(NameResolvedScope::new());
        item_header
    }

    pub fn new_module(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: Option<ItemId>,
        is_top_level: bool,
    ) -> ItemId {
        let header = self.new_header(name, parent, ItemKind::Module);

        if let Some(parent_id) = parent {
            self.add_to_parent(stores, had_error, parent_id, name, header.id);
        }

        if is_top_level {
            self.top_level_modules.insert(name.inner, header.id);
        }

        header.id
    }

    pub fn new_function(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
        entry_stack: Spanned<Vec<Spanned<UnresolvedTypeTokens>>>,
        exit_stack: Spanned<Vec<Spanned<UnresolvedTypeTokens>>>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Function);
        self.urir.item_signatures.insert(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: entry_stack,
            },
        );

        self.add_to_parent(stores, had_error, parent, name, header.id);
        header.id
    }

    pub fn new_assert(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Assert);

        // Hardcode a bool output type
        let bool_symbol = stores.strings.get("bool");
        self.urir.item_signatures.insert(
            header.id,
            UnresolvedItemSignature {
                exit: vec![UnresolvedTypeTokens::Simple(UnresolvedIdent {
                    span: name.location,
                    is_from_root: false,
                    path: vec![bool_symbol.with_span(name.location)],
                    generic_params: None,
                })
                .with_span(name.location)]
                .with_span(name.location),
                entry: Vec::new().with_span(name.location),
            },
        );

        self.add_to_parent(stores, had_error, parent, name, header.id);
        header.id
    }

    pub fn new_const(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
        exit_stack: Spanned<Vec<Spanned<UnresolvedTypeTokens>>>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Const);

        self.urir.item_signatures.insert(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: Vec::new().with_span(name.location),
            },
        );

        self.add_to_parent(stores, had_error, parent, name, header.id);
        header.id
    }

    pub fn new_generic_function(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
        entry_stack: Spanned<Vec<Spanned<UnresolvedTypeTokens>>>,
        exit_stack: Spanned<Vec<Spanned<UnresolvedTypeTokens>>>,
        params: Vec<Spanned<Spur>>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::GenericFunction);

        self.urir.item_signatures.insert(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: entry_stack,
            },
        );

        self.generic_template_parameters.insert(header.id, params);
        self.add_to_parent(stores, had_error, parent, name, header.id);
        header.id
    }

    pub fn new_struct(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        module: ItemId,
        def: UnresolvedStruct,
    ) -> ItemId {
        let name = def.name;
        let header = self.new_header(name, Some(module), ItemKind::StructDef);

        if def.generic_params.is_some() {
            self.generic_structs.push(header.id);
        }

        self.urir.structs.insert(header.id, def);
        self.add_to_parent(stores, had_error, module, name, header.id);
        header.id
    }

    pub fn new_memory(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
        memory_type: Spanned<UnresolvedTypeTokens>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Memory);
        self.urir.memory_type.insert(header.id, memory_type);
        self.add_to_parent(stores, had_error, parent, name, header.id);
        header.id
    }

    pub fn set_lang_item(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        lang_item_token: Spanned<Spur>,
        item_id: ItemId,
    ) {
        let token_string = stores.strings.resolve(lang_item_token.inner);
        let kind = match token_string {
            "string" => LangItem::String,
            "alloc" => LangItem::Alloc,
            "free" => LangItem::Free,
            _ => {
                diagnostics::emit_error(
                    stores,
                    lang_item_token.location,
                    format!("Unknown lang item `{token_string}`"),
                    [Label::new(lang_item_token.location).with_color(Color::Red)],
                    None,
                );
                *had_error = true;
                return;
            }
        };

        self.lang_items.insert(kind, item_id);
        self.headers[item_id.0 as usize].lang_item = Some(kind);
    }

    pub fn get_visible_symbol(&self, from: ItemHeader, symbol: Spur) -> Option<ItemId> {
        // 1. Check ourselves
        if from.name.inner == symbol {
            return Some(from.id);
        }

        // 2. Check our children
        let own_scope = self.nrir.get_scope(from.id);
        if let Some(child) = own_scope.get_symbol(symbol) {
            return Some(child);
        }

        // 3. If we're not a module traverse up the tree checking siblings until we hit a module.
        if from.kind != ItemKind::Module {
            let mut parent = from.parent;
            while let Some(parent_id) = parent {
                let parent_scope = self.nrir.get_scope(parent_id);
                if let Some(child) = parent_scope.get_symbol(symbol) {
                    return Some(child);
                }

                let parent_header = self.get_item_header(parent_id);
                if parent_header.kind == ItemKind::Module {
                    break;
                }
                parent = parent_header.parent;
            }
        }

        // 4. Check top level modules
        self.top_level_modules.get(&symbol).copied()
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

    fn new() -> UnresolvedScope {
        UnresolvedScope {
            imports: Vec::new(),
        }
    }
}

pub struct NameResolvedScope {
    child_items: HashMap<Spur, Spanned<ItemId>>,
    visible_symbols: HashMap<Spur, Spanned<ItemId>>,
}

impl NameResolvedScope {
    #[inline]
    pub fn get_symbol(&self, name: Spur) -> Option<ItemId> {
        self.visible_symbols.get(&name).map(|id| id.inner)
    }

    #[inline]
    pub fn get_child_items(&self) -> &HashMap<Spur, Spanned<ItemId>> {
        &self.child_items
    }

    fn add_child(&mut self, name: Spanned<Spur>, id: ItemId) -> Result<(), SourceLocation> {
        use hashbrown::hash_map::Entry;
        match self.child_items.entry(name.inner) {
            Entry::Occupied(a) => return Err(a.get().location),
            Entry::Vacant(a) => a.insert(id.with_span(name.location)),
        };

        // Children are added before imports are resolved, so this should never fail.
        self.visible_symbols
            .insert(name.inner, id.with_span(name.location))
            .expect_none("ICE: Name collision when adding child");
        Ok(())
    }

    pub fn add_visible_symbol(
        &mut self,
        symbol: Spanned<Spur>,
        id: ItemId,
    ) -> Result<(), SourceLocation> {
        use hashbrown::hash_map::Entry;
        match self.visible_symbols.entry(symbol.inner) {
            Entry::Occupied(a) => return Err(a.get().location),
            Entry::Vacant(a) => a.insert(id.with_span(symbol.location)),
        };
        Ok(())
    }

    fn new() -> NameResolvedScope {
        NameResolvedScope {
            child_items: HashMap::new(),
            visible_symbols: HashMap::new(),
        }
    }
}

pub fn make_symbol_redef_error(stores: &Stores, new_def: SourceLocation, prev_def: SourceLocation) {
    diagnostics::emit_error(
        stores,
        new_def,
        "item of that name already exists",
        [
            Label::new(new_def).with_color(Color::Red),
            Label::new(prev_def)
                .with_color(Color::Cyan)
                .with_message("previously defined here"),
        ],
        None,
    );
}
