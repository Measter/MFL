use flagset::{flags, FlagSet};
use hashbrown::HashMap;
use intcast::IntCast;
use lasso::Spur;
use smallvec::SmallVec;
use stores::{
    items::ItemId,
    source::{Spanned, WithSpan},
    strings::StringStore,
};

use crate::{
    diagnostics::NameCollision,
    error_signal::ErrorSignal,
    ir::{IdentPathRoot, UnresolvedIdent, UnresolvedType},
    option::OptionExt,
    simulate::SimulatorValue,
};

use super::{
    block::BlockId,
    signatures::{SigStore, StackDefItemUnresolved, UnresolvedItemSignature},
    types::TypeId,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangItem {
    String,
    Alloc,
    Free,
}

impl LangItem {
    pub fn kind_str(self) -> &'static str {
        match self {
            LangItem::String => "String",
            LangItem::Alloc => "Alloc",
            LangItem::Free => "Free",
        }
    }

    pub fn from_str(s: &str) -> Result<Self, ()> {
        let li = match s {
            "string" => LangItem::String,
            "alloc" => LangItem::Alloc,
            "free" => LangItem::Free,
            _ => return Err(()),
        };

        Ok(li)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ItemKind {
    Assert,
    Const,
    Variable,
    Function,
    FunctionDecl,
    GenericFunction,
    StructDef,
    Module,
    Enum,
}

impl ItemKind {
    pub fn kind_str(self) -> &'static str {
        match self {
            ItemKind::Assert => "assert",
            ItemKind::Const => "const",
            ItemKind::Variable => "variable",
            ItemKind::Function => "function",
            ItemKind::FunctionDecl => "extern function",
            ItemKind::GenericFunction => "generic function",
            ItemKind::StructDef => "struct",
            ItemKind::Module => "module",
            ItemKind::Enum => "enum",
        }
    }
}

flags! {
    pub enum ItemAttribute: u8 {
        Extern
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ItemHeader {
    pub name: Spanned<Spur>,
    pub id: ItemId,
    pub parent: Option<ItemId>,
    pub kind: ItemKind,
    pub attributes: FlagSet<ItemAttribute>,
    pub lang_item: Option<LangItem>,
}

pub struct ItemStore {
    bool_spur: Spur,
    core_module_id: Option<ItemId>,
    top_level_modules: HashMap<Spur, ItemId>,
    lang_items: HashMap<LangItem, ItemId>,

    headers: Vec<ItemHeader>,
    const_vals: HashMap<ItemId, Vec<SimulatorValue>>,
    item_body: HashMap<ItemId, BlockId>,

    // Bit of a hacky workaround for how I've done the struct resolution.
    generic_structs: Vec<ItemId>,
    generic_function_cache: HashMap<(ItemId, SmallVec<[TypeId; 4]>), ItemId>,
    generic_template_parameters: HashMap<ItemId, Vec<Spanned<Spur>>>,
}

impl ItemStore {
    #[inline]
    pub fn get_all_items(&self) -> impl Iterator<Item = ItemHeader> + '_ {
        self.headers.iter().copied()
    }

    pub fn get_lang_items(&self) -> &HashMap<LangItem, ItemId> {
        &self.lang_items
    }

    pub fn set_core_module(&mut self, id: ItemId) {
        self.core_module_id = Some(id);
    }

    pub fn update_core_symbols(&mut self, sigs: &mut SigStore) {
        let core_module_id = self.core_module_id.expect("ICE: Core module not set");
        // For now this is just String.
        let core_scope = sigs.nrir.get_scope_mut(core_module_id);

        let string_item_id = self.lang_items[&LangItem::String];
        let string_header = self.headers[string_item_id.to_usize()];
        core_scope
            .add_visible_symbol(string_header.name, string_item_id)
            .expect("ICE: Core already contains String");
    }

    #[inline]
    pub fn get_top_level_module(&self, name: Spur) -> Option<ItemId> {
        self.top_level_modules.get(&name).copied()
    }

    #[inline]
    pub fn get_item_header(&self, id: ItemId) -> ItemHeader {
        self.headers[id.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_item_body(&self, id: ItemId) -> BlockId {
        self.item_body[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_item_body(&mut self, id: ItemId, block_id: BlockId) {
        self.item_body
            .insert(id, block_id)
            .expect_none("ICE: Set same item body multiple times");
    }

    #[inline]
    #[track_caller]
    pub fn get_consts(&self, id: ItemId) -> Option<&[SimulatorValue]> {
        self.const_vals.get(&id).map(|v| &**v)
    }

    #[inline]
    #[track_caller]
    pub fn set_consts(&mut self, id: ItemId, consts: Vec<SimulatorValue>) {
        self.const_vals
            .insert(id, consts)
            .expect_none("ICE: replaced existing const values");
    }

    pub fn get_generic_structs(&self) -> &[ItemId] {
        &self.generic_structs
    }

    #[inline]
    #[track_caller]
    pub fn get_function_template_paramaters(&self, id: ItemId) -> &[Spanned<Spur>] {
        // &self.generic_template_parameters[&id]
        self.generic_template_parameters
            .get(&id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn get_cached_generic_function(
        &self,
        base_id: ItemId,
        generic_params: &[TypeId],
    ) -> Option<ItemId> {
        let generic_params = generic_params.into();
        self.generic_function_cache
            .get(&(base_id, generic_params))
            .copied()
    }

    pub fn set_cached_generic_function(
        &mut self,
        base_id: ItemId,
        generic_params: SmallVec<[TypeId; 4]>,
        new_id: ItemId,
    ) {
        self.generic_function_cache
            .insert((base_id, generic_params), new_id)
            .expect_none("ICE: Reinserted already-cached generic function");
    }
}

impl ItemStore {
    pub fn new(strings: &mut StringStore) -> Self {
        let bool_spur = strings.intern("bool");
        ItemStore {
            bool_spur,
            core_module_id: None,
            top_level_modules: HashMap::new(),
            lang_items: HashMap::new(),
            headers: Vec::new(),
            item_body: HashMap::new(),
            const_vals: HashMap::new(),
            generic_structs: Vec::new(),
            generic_function_cache: HashMap::new(),
            generic_template_parameters: HashMap::new(),
        }
    }

    fn add_to_parent(
        &mut self,
        sigs: &mut SigStore,
        had_error: &mut ErrorSignal,
        parent_id: ItemId,
        child_name: Spanned<Spur>,
        child_id: ItemId,
    ) -> Result<(), NameCollision> {
        let parent_scope = sigs.nrir.get_scope_mut(parent_id);
        if let Err(prev_loc) = parent_scope.add_child(child_name, child_id) {
            had_error.set();
            return Err(NameCollision {
                new: child_name.location,
                prev: prev_loc,
            });
        }
        Ok(())
    }

    fn new_header(
        &mut self,
        sigs: &mut SigStore,
        name: Spanned<Spur>,
        parent: Option<ItemId>,
        kind: ItemKind,
        attributes: FlagSet<ItemAttribute>,
    ) -> ItemHeader {
        let new_id = self.headers.len();
        let new_id = ItemId::new(new_id.to_u16().unwrap());

        let item_header = ItemHeader {
            name,
            id: new_id,
            parent,
            kind,
            lang_item: None,
            attributes,
        };

        self.headers.push(item_header);
        sigs.urir.new_scope(new_id);
        sigs.nrir.new_scope(new_id);
        item_header
    }

    pub fn new_module(
        &mut self,
        sigs: &mut SigStore,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: Option<ItemId>,
        is_top_level: bool,
    ) -> (ItemId, Option<NameCollision>) {
        let header = self.new_header(sigs, name, parent, ItemKind::Module, FlagSet::default());

        let prev_loc = if let Some(parent_id) = parent {
            self.add_to_parent(sigs, had_error, parent_id, name, header.id)
                .err()
        } else {
            None
        };

        if is_top_level {
            self.top_level_modules.insert(name.inner, header.id);
        }

        (header.id, prev_loc)
    }

    pub fn new_function(
        &mut self,
        sigs: &mut SigStore,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
        attributes: FlagSet<ItemAttribute>,
        entry_stack: Spanned<Vec<StackDefItemUnresolved>>,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
    ) -> (ItemId, Option<NameCollision>) {
        let header = self.new_header(sigs, name, Some(parent), ItemKind::Function, attributes);
        sigs.urir.set_item_signature(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: entry_stack,
            },
        );

        (
            header.id,
            self.add_to_parent(sigs, had_error, parent, name, header.id)
                .err(),
        )
    }

    pub fn new_function_decl(
        &mut self,
        sigs: &mut SigStore,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
        attributes: FlagSet<ItemAttribute>,
        entry_stack: Spanned<Vec<StackDefItemUnresolved>>,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
    ) -> (ItemId, Option<NameCollision>) {
        let header = self.new_header(
            sigs,
            name,
            Some(parent),
            ItemKind::FunctionDecl,
            attributes | ItemAttribute::Extern,
        );
        sigs.urir.set_item_signature(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: entry_stack,
            },
        );

        (
            header.id,
            self.add_to_parent(sigs, had_error, parent, name, header.id)
                .err(),
        )
    }

    // This is because we don't want the new function to be added to the scope.
    // Resolution should go through the generic form.
    pub fn new_function_generic_instance(
        &mut self,
        sigs: &mut SigStore,
        name: Spanned<Spur>,
        parent: ItemId,
        attributes: FlagSet<ItemAttribute>,
        entry_stack: Spanned<Vec<StackDefItemUnresolved>>,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
    ) -> ItemId {
        let header = self.new_header(sigs, name, Some(parent), ItemKind::Function, attributes);
        sigs.urir.set_item_signature(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: entry_stack,
            },
        );

        header.id
    }

    pub fn new_assert(
        &mut self,
        sigs: &mut SigStore,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
    ) -> (ItemId, Option<NameCollision>) {
        let header = self.new_header(
            sigs,
            name,
            Some(parent),
            ItemKind::Assert,
            FlagSet::default(),
        );

        let bool_spur = self.bool_spur;
        sigs.urir.set_item_signature(
            header.id,
            UnresolvedItemSignature {
                exit: vec![UnresolvedType::Simple(UnresolvedIdent {
                    span: name.location,
                    path_root: IdentPathRoot::CurrentScope,
                    path: vec![bool_spur.with_span(name.location)],
                    generic_params: Vec::new(),
                })
                .with_span(name.location)]
                .with_span(name.location),
                entry: Vec::new().with_span(name.location),
            },
        );

        (
            header.id,
            self.add_to_parent(sigs, had_error, parent, name, header.id)
                .err(),
        )
    }

    pub fn new_const(
        &mut self,
        sigs: &mut SigStore,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
    ) -> (ItemId, Option<NameCollision>) {
        let header = self.new_header(
            sigs,
            name,
            Some(parent),
            ItemKind::Const,
            FlagSet::default(),
        );

        sigs.urir.set_item_signature(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: Vec::new().with_span(name.location),
            },
        );

        (
            header.id,
            self.add_to_parent(sigs, had_error, parent, name, header.id)
                .err(),
        )
    }

    pub fn new_generic_function(
        &mut self,
        sigs: &mut SigStore,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
        attributes: FlagSet<ItemAttribute>,
        entry_stack: Spanned<Vec<StackDefItemUnresolved>>,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
        params: Vec<Spanned<Spur>>,
    ) -> (ItemId, Option<NameCollision>) {
        let header = self.new_header(
            sigs,
            name,
            Some(parent),
            ItemKind::GenericFunction,
            attributes,
        );

        sigs.urir.set_item_signature(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: entry_stack,
            },
        );

        self.generic_template_parameters.insert(header.id, params);
        (
            header.id,
            self.add_to_parent(sigs, had_error, parent, name, header.id)
                .err(),
        )
    }

    pub fn new_struct(
        &mut self,
        sigs: &mut SigStore,
        had_error: &mut ErrorSignal,
        module: ItemId,
        name: Spanned<Spur>,
        is_generic: bool,
        attributes: FlagSet<ItemAttribute>,
    ) -> (ItemId, Option<NameCollision>) {
        let header = self.new_header(sigs, name, Some(module), ItemKind::StructDef, attributes);

        if is_generic {
            self.generic_structs.push(header.id);
        }

        (
            header.id,
            self.add_to_parent(sigs, had_error, module, name, header.id)
                .err(),
        )
    }

    pub fn new_enum(
        &mut self,
        sigs: &mut SigStore,
        had_error: &mut ErrorSignal,
        module: ItemId,
        name: Spanned<Spur>,
        attributes: FlagSet<ItemAttribute>,
    ) -> (ItemId, Option<NameCollision>) {
        let header = self.new_header(sigs, name, Some(module), ItemKind::Enum, attributes);

        (
            header.id,
            self.add_to_parent(sigs, had_error, module, name, header.id)
                .err(),
        )
    }

    pub fn new_variable(
        &mut self,
        sigs: &mut SigStore,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
        attributes: FlagSet<ItemAttribute>,
        variable_type: Spanned<UnresolvedType>,
    ) -> (ItemId, Option<NameCollision>) {
        let header = self.new_header(sigs, name, Some(parent), ItemKind::Variable, attributes);
        sigs.urir.set_variable_type(header.id, variable_type);

        (
            header.id,
            self.add_to_parent(sigs, had_error, parent, name, header.id)
                .err(),
        )
    }

    pub fn set_lang_item(&mut self, lang_item: LangItem, item_id: ItemId) {
        self.lang_items.insert(lang_item, item_id);
        self.headers[item_id.to_usize()].lang_item = Some(lang_item);
    }

    pub fn get_visible_symbol(
        &self,
        sigs: &mut SigStore,
        from: ItemHeader,
        symbol: Spur,
    ) -> Option<ItemId> {
        // 1. Check ourselves
        if from.name.inner == symbol {
            return Some(from.id);
        }

        // 2. Check our children
        let own_scope = sigs.nrir.get_scope(from.id);
        if let Some(child) = own_scope.get_symbol(symbol) {
            return Some(child);
        }

        // 3. If we're not a module traverse up the tree checking siblings until we hit a module.
        if from.kind != ItemKind::Module {
            let mut parent = from.parent;
            while let Some(parent_id) = parent {
                let parent_scope = sigs.nrir.get_scope(parent_id);
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
