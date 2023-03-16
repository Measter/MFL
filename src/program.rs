use std::{
    collections::{HashMap, HashSet},
    ffi::OsStr,
    ops::Not,
    path::Path,
};

use ariadne::{Color, Label};
use color_eyre::eyre::{eyre, Context, Result};
use intcast::IntCast;
use lasso::Spur;
use smallvec::SmallVec;
use tracing::{debug_span, trace, trace_span};

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{self, Token},
    opcode::{If, Op, OpCode, OpId, While},
    program::static_analysis::ConstVal,
    simulate::{simulate_execute_program, SimulationError, SimulatorValue},
    source_file::{SourceLocation, SourceStorage},
    type_store::{BuiltinTypes, TypeId, TypeKind, TypeStore, UnresolvedType},
};

mod parser;
pub mod static_analysis;
use static_analysis::Analyzer;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ItemId(u16);
impl ItemId {
    // This is only used during parse failure, so it shouldn't cause problems?
    pub fn dud() -> Self {
        Self(u16::MAX)
    }
}

#[derive(Debug, Default)]
pub struct FunctionData {
    pub allocs: HashMap<Spur, ItemId>,
    pub consts: HashMap<Spur, ItemId>,
}

// TODO: Add compile-time asserts
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ItemKind {
    Assert,
    Const,
    Macro,
    Memory,
    Function,
}

#[derive(Debug, Clone, Copy)]
pub struct ItemHeader {
    name: Token,
    module: ModuleId,
    id: ItemId,
    parent: Option<ItemId>,
    kind: ItemKind,
    new_op_id: u32,
}

impl ItemHeader {
    pub fn name(&self) -> Token {
        self.name
    }

    pub fn module(&self) -> ModuleId {
        self.module
    }

    pub fn id(&self) -> ItemId {
        self.id
    }

    pub fn parent(&self) -> Option<ItemId> {
        self.parent
    }

    pub fn kind(&self) -> ItemKind {
        self.kind
    }
}

#[derive(Debug)]
pub struct ItemSignatureUnresolved {
    exit_stack: Vec<UnresolvedType>,
    exit_stack_location: SourceLocation,
    entry_stack: Vec<UnresolvedType>,
    entry_stack_location: SourceLocation,
    memory_type: Option<UnresolvedType>,
    memory_type_location: SourceLocation,
}

impl ItemSignatureUnresolved {
    pub fn exit_stack(&self) -> &[UnresolvedType] {
        &self.exit_stack
    }

    pub fn exit_stack_location(&self) -> SourceLocation {
        self.exit_stack_location
    }

    pub fn entry_stack(&self) -> &[UnresolvedType] {
        &self.entry_stack
    }

    pub fn entry_stack_location(&self) -> SourceLocation {
        self.entry_stack_location
    }

    pub fn memory_type(&self) -> &UnresolvedType {
        self.memory_type.as_ref().unwrap()
    }

    pub fn memory_type_location(&self) -> SourceLocation {
        self.memory_type_location
    }
}
pub struct ItemSignatureResolved {
    exit_stack: SmallVec<[TypeId; 8]>,
    entry_stack: SmallVec<[TypeId; 8]>,
    memory_type: Option<TypeId>,
}

impl ItemSignatureResolved {
    pub fn exit_stack(&self) -> &[TypeId] {
        &self.exit_stack
    }

    pub fn entry_stack(&self) -> &[TypeId] {
        &self.entry_stack
    }

    pub fn memory_type(&self) -> TypeId {
        self.memory_type.unwrap()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(u16);

pub struct Program {
    modules: HashMap<ModuleId, Module>,
    module_ident_map: HashMap<Spur, ModuleId>,

    item_headers: HashMap<ItemId, ItemHeader>,
    item_signatures_unresolved: HashMap<ItemId, ItemSignatureUnresolved>,
    item_signatures_resolved: HashMap<ItemId, ItemSignatureResolved>,
    item_bodies: HashMap<ItemId, Vec<Op>>,
    function_data: HashMap<ItemId, FunctionData>,
    const_vals: HashMap<ItemId, Vec<(TypeId, SimulatorValue)>>,
    analyzers: HashMap<ItemId, Analyzer>,
}

impl Program {
    pub fn get_all_items(&self) -> impl Iterator<Item = (ItemId, ItemHeader)> + '_ {
        self.item_headers.iter().map(|(id, item)| (*id, *item))
    }

    pub fn get_module(&self, id: ModuleId) -> &Module {
        &self.modules[&id]
    }

    pub fn get_item_header(&self, id: ItemId) -> ItemHeader {
        self.item_headers[&id]
    }

    pub fn get_item_header_mut(&mut self, id: ItemId) -> &mut ItemHeader {
        self.item_headers.get_mut(&id).unwrap()
    }

    pub fn get_item_signature_unresolved(&self, id: ItemId) -> &ItemSignatureUnresolved {
        &self.item_signatures_unresolved[&id]
    }

    #[track_caller]
    pub fn get_item_signature_resolved(&self, id: ItemId) -> &ItemSignatureResolved {
        &self.item_signatures_resolved[&id]
    }

    #[track_caller]
    pub fn get_item_body(&self, id: ItemId) -> &[Op] {
        &self.item_bodies[&id]
    }

    pub fn set_item_body(&mut self, id: ItemId, body: Vec<Op>) {
        self.item_bodies.insert(id, body);
    }

    pub fn get_analyzer(&self, id: ItemId) -> &Analyzer {
        &self.analyzers[&id]
    }

    #[track_caller]
    pub fn get_function_data(&self, id: ItemId) -> &FunctionData {
        self.function_data
            .get(&id)
            .expect("ICE: tried to get function data for non-function item")
    }

    #[track_caller]
    pub fn get_function_data_mut(&mut self, id: ItemId) -> &mut FunctionData {
        self.function_data
            .get_mut(&id)
            .expect("ICE: tried to get function data for non-function item")
    }

    pub fn get_consts(&self, id: ItemId) -> Option<&[(TypeId, SimulatorValue)]> {
        self.const_vals.get(&id).map(|v| &**v)
    }
}

impl Program {
    pub fn new() -> Self {
        Program {
            modules: Default::default(),
            module_ident_map: Default::default(),
            item_headers: HashMap::new(),
            item_signatures_unresolved: HashMap::new(),
            item_signatures_resolved: HashMap::new(),
            item_bodies: HashMap::new(),
            function_data: HashMap::new(),
            const_vals: HashMap::new(),
            analyzers: HashMap::new(),
        }
    }

    fn new_module(&mut self, name: Spur) -> ModuleId {
        let new_id = self.modules.len();
        let new_id = ModuleId(new_id.to_u16().unwrap());

        let module = Module {
            name,
            top_level_symbols: HashMap::new(),
        };
        self.module_ident_map.insert(name, new_id);
        self.modules.insert(new_id, module);

        new_id
    }

    pub fn load_program(
        &mut self,
        file: &str,
        interner: &mut Interners,
        source_store: &mut SourceStorage,
        type_store: &mut TypeStore,
        library_paths: &[String],
    ) -> Result<ModuleId> {
        let _span = debug_span!(stringify!(Program::load_program)).entered();

        let module_name = Path::new(file).file_stem().and_then(OsStr::to_str).unwrap();
        let module_name = interner.intern_lexeme(module_name);

        let mut loaded_modules = HashSet::new();
        let mut include_queue = Vec::new();

        let entry_module_id = self.new_module(module_name);

        Module::load(
            self,
            entry_module_id,
            source_store,
            interner,
            file,
            &mut include_queue,
        )?;

        loaded_modules.insert(module_name);

        let mut had_error = false;
        while let Some(token) = include_queue.pop() {
            if loaded_modules.contains(&token.lexeme) {
                continue;
            }

            let mut filename = Path::new(interner.resolve_lexeme(token.lexeme)).to_owned();
            filename.set_extension("mfl");

            let full_path = match search_includes(library_paths, &filename) {
                Some(path) => path,
                None => {
                    diagnostics::emit_error(
                        token.location,
                        "unable to find module",
                        Some(
                            Label::new(token.location)
                                .with_color(Color::Red)
                                .with_message("here"),
                        ),
                        None,
                        source_store,
                    );

                    had_error = true;
                    continue;
                }
            };

            let new_module_id = self.new_module(token.lexeme);

            match Module::load(
                self,
                new_module_id,
                source_store,
                interner,
                &full_path,
                &mut include_queue,
            ) {
                Ok(module) => module,
                Err(e) => {
                    diagnostics::emit_error(
                        token.location,
                        "error loading module",
                        Some(
                            Label::new(token.location)
                                .with_color(Color::Red)
                                .with_message("here"),
                        ),
                        format!("{e}"),
                        source_store,
                    );

                    had_error = true;
                    continue;
                }
            };

            loaded_modules.insert(token.lexeme);
        }

        if had_error {
            return Err(eyre!("failed to load program"));
        }

        self.post_process_items(interner, source_store, type_store)?;

        Ok(entry_module_id)
    }

    fn resolve_idents_in_block(
        &self,
        item: ItemHeader,
        mut body: Vec<Op>,
        had_error: &mut bool,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Vec<Op> {
        for op in &mut body {
            match &mut op.code {
                OpCode::While(while_op) => {
                    let temp_body = std::mem::take(&mut while_op.condition);
                    while_op.condition = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut while_op.body_block);
                    while_op.body_block = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                }
                OpCode::If(if_op) => {
                    // Mmmm.. repetition...
                    let temp_body = std::mem::take(&mut if_op.condition);
                    if_op.condition = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut if_op.then_block);
                    if_op.then_block = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut if_op.else_block);
                    if_op.else_block = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                }
                // Symbol in own module.
                OpCode::UnresolvedIdent {
                    item: item_token,
                    module: None,
                } => {
                    // Obviously a symbol is visible to itself.
                    let visible_id = if item_token.lexeme == item.name.lexeme {
                        Some(item.id())
                    } else {
                        self.get_visible_symbol(item, item_token.lexeme)
                    };
                    if let Some(id) = visible_id {
                        op.code = OpCode::ResolvedIdent { item_id: id };
                    } else {
                        let module = &self.modules[&item.module];
                        let token_lexeme = interner.resolve_lexeme(item_token.lexeme);
                        let module_lexeme = interner.resolve_lexeme(module.name);
                        *had_error = true;
                        diagnostics::emit_error(
                            item_token.location,
                            format!(
                                "symbol `{token_lexeme}` not found in module `{module_lexeme}`"
                            ),
                            Some(
                                Label::new(item_token.location)
                                    .with_color(Color::Red)
                                    .with_message("not found"),
                            ),
                            None,
                            source_store,
                        );
                    }
                }
                // Symbol in other module.
                OpCode::UnresolvedIdent {
                    item: item_token,
                    module: Some(module_token),
                } => {
                    let module_id = match self.module_ident_map.get(&module_token.lexeme) {
                        Some(id) => *id,
                        None => {
                            let module_name = interner.resolve_lexeme(module_token.lexeme);
                            diagnostics::emit_error(
                                item_token.location,
                                format!("module `{module_name}` not found"),
                                Some(
                                    Label::new(item_token.location)
                                        .with_color(Color::Red)
                                        .with_message("not found"),
                                ),
                                None,
                                source_store,
                            );
                            *had_error = true;
                            continue;
                        }
                    };

                    let module = &self.modules[&module_id];
                    match module.top_level_symbols.get(&item_token.lexeme) {
                        Some(item_id) => {
                            op.code = OpCode::ResolvedIdent { item_id: *item_id };
                        }
                        None => {
                            let item_name = interner.resolve_lexeme(item_token.lexeme);
                            let module_name = interner.resolve_lexeme(module_token.lexeme);
                            diagnostics::emit_error(
                                item_token.location,
                                format!("symbol `{item_name}` not found in module `{module_name}`"),
                                Some(
                                    Label::new(item_token.location)
                                        .with_color(Color::Red)
                                        .with_message("not found"),
                                ),
                                None,
                                source_store,
                            );
                            *had_error = true;
                            continue;
                        }
                    }
                }

                _ => {}
            }
        }

        body
    }

    fn resolve_idents(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::resolve_idents)).entered();
        let mut had_error = false;
        let items: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, item)| item.kind() != ItemKind::Memory)
            .map(|(id, item)| (*id, *item))
            .collect();

        for (item_id, item) in items {
            trace!(name = interner.get_symbol_name(self, item_id));
            let body = self.item_bodies.remove(&item_id).unwrap();

            self.item_bodies.insert(
                item_id,
                self.resolve_idents_in_block(item, body, &mut had_error, interner, source_store),
            );
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error during ident resolation"))
    }

    // The self parameter is the source of this, but it makes more sense for it to be a method.
    #[allow(clippy::only_used_in_recursion)]
    fn resolve_types_in_block(
        &self,
        mut body: Vec<Op>,
        had_error: &mut bool,
        interner: &mut Interners,
        source_store: &SourceStorage,
        type_store: &mut TypeStore,
    ) -> Vec<Op> {
        for op in &mut body {
            match &mut op.code {
                OpCode::While(while_op) => {
                    let temp_body = std::mem::take(&mut while_op.condition);
                    while_op.condition = self.resolve_types_in_block(
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        type_store,
                    );
                    let temp_body = std::mem::take(&mut while_op.body_block);
                    while_op.body_block = self.resolve_types_in_block(
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        type_store,
                    );
                }
                OpCode::If(if_op) => {
                    // Mmmm.. repetition...
                    let temp_body = std::mem::take(&mut if_op.condition);
                    if_op.condition = self.resolve_types_in_block(
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        type_store,
                    );
                    let temp_body = std::mem::take(&mut if_op.then_block);
                    if_op.then_block = self.resolve_types_in_block(
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        type_store,
                    );
                    let temp_body = std::mem::take(&mut if_op.else_block);
                    if_op.else_block = self.resolve_types_in_block(
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        type_store,
                    );
                }

                OpCode::UnresolvedCast { unresolved_type } => {
                    let Some(type_info) = type_store.resolve_type(interner, source_store, unresolved_type) else {
                        *had_error = true;
                        continue;
                    };

                    op.code = OpCode::ResolvedCast { id: type_info.id };
                }

                _ => {}
            }
        }

        body
    }

    fn resolve_types(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
        type_store: &mut TypeStore,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::resolve_types)).entered();
        let mut had_error = false;

        for (item_id, item) in self.item_headers.iter().map(|(id, item)| (*id, *item)) {
            trace!(name = interner.get_symbol_name(self, item_id));

            let unresolved_sig = &self.item_signatures_unresolved[&item_id];

            let mut resolved_entry = SmallVec::with_capacity(unresolved_sig.entry_stack.len());
            let mut resolved_exit = SmallVec::with_capacity(unresolved_sig.exit_stack.len());
            let mut resolved_memory_type = None;

            if item.kind == ItemKind::Memory {
                resolved_exit.push(type_store.get_builtin(BuiltinTypes::U64).id);
                let Some(info) = type_store.resolve_type(interner, source_store, unresolved_sig.memory_type()) else {
                    had_error = true;
                    continue;
                };
                resolved_memory_type = Some(info.id);
            } else {
                for input_sig in unresolved_sig.entry_stack() {
                    let Some(info) = type_store.resolve_type(interner, source_store, input_sig) else {
                        had_error = true;
                        continue;
                    };
                    resolved_entry.push(info.id);
                }

                for input_sig in unresolved_sig.exit_stack() {
                    let Some(info) = type_store.resolve_type(interner, source_store, input_sig) else {
                        had_error = true;
                        continue;
                    };
                    resolved_exit.push(info.id);
                }
            }

            self.item_signatures_resolved.insert(
                item_id,
                ItemSignatureResolved {
                    entry_stack: resolved_entry,
                    exit_stack: resolved_exit,
                    memory_type: resolved_memory_type,
                },
            );

            if item.kind != ItemKind::Memory {
                let body = self.item_bodies.remove(&item_id).unwrap();
                self.item_bodies.insert(
                    item_id,
                    self.resolve_types_in_block(
                        body,
                        &mut had_error,
                        interner,
                        source_store,
                        type_store,
                    ),
                );
            }
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error during type resolution"))
    }

    fn expand_macros_in_block(
        &self,
        block: &mut Vec<Op>,
        id: ItemId,
        new_op_id: &mut impl FnMut() -> OpId,
    ) {
        let mut i = 0;
        while i < block.len() {
            match block[i].code {
                OpCode::While(ref mut while_op) => {
                    self.expand_macros_in_block(&mut while_op.condition, id, new_op_id);
                    self.expand_macros_in_block(&mut while_op.body_block, id, new_op_id);
                }
                OpCode::If(ref mut if_op) => {
                    self.expand_macros_in_block(&mut if_op.condition, id, new_op_id);
                    self.expand_macros_in_block(&mut if_op.then_block, id, new_op_id);
                    self.expand_macros_in_block(&mut if_op.else_block, id, new_op_id);
                }
                OpCode::ResolvedIdent { item_id, .. } if item_id != id => {
                    let found_item = self.item_headers[&item_id];
                    if found_item.kind() == ItemKind::Macro {
                        let token = block[i].token;
                        let expansions = block[i].expansions.clone();
                        let new_ops = self.get_item_body(item_id).iter().map(|new_op| {
                            let mut new_op = new_op.clone();
                            new_op.id = new_op_id();
                            new_op.expansions.push(token.location);
                            new_op.expansions.extend_from_slice(&expansions);
                            new_op
                        });

                        block.splice(i..i + 1, new_ops);

                        // Want to continue with the current op index
                        continue;
                    }
                }
                _ => {}
            }

            i += 1;
        }
        //
    }

    fn expand_macros(&mut self, interner: &mut Interners) {
        let _span = debug_span!(stringify!(Program::expand_macros)).entered();
        let non_macro_items: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, i)| i.kind() != ItemKind::Macro && i.kind() != ItemKind::Memory)
            .map(|(id, item)| (*id, *item))
            .collect();

        for (item_id, item) in non_macro_items {
            trace!(name = interner.get_symbol_name(self, item_id));
            let mut new_op_id = item.new_op_id;

            let mut op_id_gen = || {
                let id = new_op_id;
                new_op_id += 1;
                OpId(id)
            };

            let mut body = self.item_bodies.remove(&item_id).unwrap();
            self.expand_macros_in_block(&mut body, item_id, &mut op_id_gen);
            self.item_bodies.insert(item_id, body);
        }
    }

    fn check_invalid_cyclic_refs_in_block(
        &self,
        root_item: ItemHeader,
        block: &[Op],
        cur_item: ItemHeader,
        kind: &str,
        already_checked: &mut HashSet<ItemId>,
        check_queue: &mut Vec<ItemHeader>,
        had_error: &mut bool,
        source_store: &SourceStorage,
    ) {
        for op in block {
            match op.code {
                OpCode::While(ref while_op) => {
                    self.check_invalid_cyclic_refs_in_block(
                        root_item,
                        &while_op.condition,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        root_item,
                        &while_op.body_block,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    //
                }
                OpCode::If(ref if_op) => {
                    self.check_invalid_cyclic_refs_in_block(
                        root_item,
                        &if_op.condition,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        root_item,
                        &if_op.then_block,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        root_item,
                        &if_op.else_block,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                }
                OpCode::ResolvedIdent { item_id, .. } => {
                    // False means that there was already a value in the set with this item_id
                    #[allow(clippy::bool_comparison)]
                    if already_checked.insert(item_id) == false {
                        continue;
                    }

                    if item_id == root_item.id() {
                        *had_error = true;
                        diagnostics::emit_error(
                            cur_item.name.location,
                            format!("cyclic {kind} detected"),
                            [
                                Label::new(root_item.name.location)
                                    .with_color(Color::Red)
                                    .with_message(format!("in this {kind}")),
                                Label::new(op.token.location)
                                    .with_color(Color::Cyan)
                                    .with_message("cyclic reference"),
                            ],
                            None,
                            source_store,
                        );
                    } else {
                        check_queue.push(self.get_item_header(item_id));
                    }
                }
                _ => (),
            }
        }
    }

    fn check_invalid_cyclic_refs(
        &self,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::check_invalid_cyclic_refs)).entered();
        let mut had_error = false;

        let mut check_queue = Vec::new();
        let mut already_checked = HashSet::new();
        for root_item in self.item_headers.values().copied() {
            trace!(name = interner.get_symbol_name(self, root_item.id()));

            let kind = match root_item.kind() {
                ItemKind::Const => "const",
                ItemKind::Macro => "macro",
                ItemKind::Assert => "assert",
                ItemKind::Memory | ItemKind::Function => continue,
            };

            check_queue.clear();
            check_queue.push(root_item);
            already_checked.clear();

            while let Some(item) = check_queue.pop() {
                self.check_invalid_cyclic_refs_in_block(
                    root_item,
                    &self.item_bodies[&item.id],
                    item,
                    kind,
                    &mut already_checked,
                    &mut check_queue,
                    &mut had_error,
                    source_store,
                );
            }
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("failed const self-check"))
    }

    // The self parameter is the source of this, but it makes more sense for it to be a method.
    #[allow(clippy::only_used_in_recursion)]
    fn determine_terminal_blocks_in_block(&self, block: &mut [Op]) -> bool {
        for op in block {
            match &mut op.code {
                OpCode::If(if_block) => {
                    if_block.is_condition_terminal =
                        self.determine_terminal_blocks_in_block(&mut if_block.condition);
                    if_block.is_then_terminal =
                        self.determine_terminal_blocks_in_block(&mut if_block.then_block);
                    if_block.is_else_terminal =
                        self.determine_terminal_blocks_in_block(&mut if_block.else_block);
                }
                OpCode::While(while_block) => {
                    self.determine_terminal_blocks_in_block(&mut while_block.condition);
                    self.determine_terminal_blocks_in_block(&mut while_block.body_block);
                }
                OpCode::Return => return true,
                _ => {}
            }
        }

        false
    }

    fn determine_terminal_blocks(&mut self, interner: &mut Interners) -> Result<()> {
        let _span = debug_span!(stringify!(Program::determine_terminal_blocks)).entered();
        let items: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, i)| i.kind() != ItemKind::Macro && i.kind() != ItemKind::Memory)
            .map(|(id, _)| *id)
            .collect();

        for item_id in items {
            trace!(name = interner.get_symbol_name(self, item_id));

            let mut body = self.item_bodies.remove(&item_id).unwrap();
            self.determine_terminal_blocks_in_block(&mut body);
            self.item_bodies.insert(item_id, body);
        }

        Ok(())
    }

    fn analyze_data_flow(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
        type_store: &mut TypeStore,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::analyze_data_flow)).entered();
        let mut had_error = false;
        let items: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, i)| i.kind() != ItemKind::Macro && i.kind() != ItemKind::Memory)
            .map(|(id, _)| *id)
            .collect();

        for id in items {
            let _span =
                trace_span!("Analyzing item", name = interner.get_symbol_name(self, id)).entered();
            let mut analyzer = Analyzer::default();
            had_error |= static_analysis::analyze_item(
                self,
                id,
                &mut analyzer,
                interner,
                source_store,
                type_store,
            )
            .is_err();

            self.analyzers.insert(id, analyzer);
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("data analysis error"))
    }

    fn evaluate_const_items(
        &mut self,
        interner: &Interners,
        source_store: &SourceStorage,
        type_store: &mut TypeStore,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::evaluate_const_items)).entered();
        let mut had_error = false;

        let mut const_queue: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, item)| item.kind() == ItemKind::Const)
            .map(|(id, _)| *id)
            .collect();
        let mut next_run_queue = Vec::with_capacity(const_queue.len());

        loop {
            for const_id in const_queue.drain(..) {
                let item_sig = self.get_item_signature_resolved(const_id);
                match simulate_execute_program(self, const_id, interner, source_store) {
                    Ok(stack) => {
                        let const_vals = stack
                            .into_iter()
                            .zip(&item_sig.exit_stack)
                            .map(|(val, ty)| {
                                let expected_type = type_store.get_type_info(*ty);
                                let val = match val {
                                    SimulatorValue::Int { kind, .. } => {
                                        let TypeKind::Integer { width: to_width, signed: to_signed } = expected_type.kind else {
                                            unreachable!()
                                        };

                                        SimulatorValue::Int { width: to_width, kind: kind.cast(to_width, to_signed) }
                                    },
                                    SimulatorValue::Bool(_) => val,
                                };

                                (*ty, val)
                            })
                            .collect();

                        self.const_vals.insert(const_id, const_vals);
                    }
                    Err(SimulationError::UnsupportedOp) => {
                        had_error = true;
                    }
                    Err(SimulationError::UnreadyConst) => {
                        next_run_queue.push(const_id);
                    }
                }
            }

            if next_run_queue.is_empty() {
                break;
            }

            std::mem::swap(&mut const_queue, &mut next_run_queue);
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("failed during const evaluation"))
    }

    fn process_idents_in_block(
        &mut self,
        own_item_id: ItemId,
        block: Vec<Op>,
        had_error: &mut bool,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Vec<Op> {
        let mut new_ops: Vec<Op> = Vec::with_capacity(block.len());
        for op in block {
            match op.code {
                OpCode::While(while_op) => {
                    new_ops.push(Op {
                        code: OpCode::While(Box::new(While {
                            condition: self.process_idents_in_block(
                                own_item_id,
                                while_op.condition,
                                had_error,
                                interner,
                                source_store,
                            ),
                            body_block: self.process_idents_in_block(
                                own_item_id,
                                while_op.body_block,
                                had_error,
                                interner,
                                source_store,
                            ),
                            ..*while_op
                        })),
                        id: op.id,
                        token: op.token,
                        expansions: op.expansions,
                    });
                }
                OpCode::If(if_op) => {
                    let new_condition = self.process_idents_in_block(
                        own_item_id,
                        if_op.condition,
                        had_error,
                        interner,
                        source_store,
                    );
                    let new_then_block = self.process_idents_in_block(
                        own_item_id,
                        if_op.then_block,
                        had_error,
                        interner,
                        source_store,
                    );
                    let new_else_block = self.process_idents_in_block(
                        own_item_id,
                        if_op.else_block,
                        had_error,
                        interner,
                        source_store,
                    );

                    new_ops.push(Op {
                        code: OpCode::If(Box::new(If {
                            condition: new_condition,
                            then_block: new_then_block,
                            else_block: new_else_block,
                            ..*if_op
                        })),
                        id: op.id,
                        token: op.token,
                        expansions: op.expansions,
                    });
                }

                OpCode::ResolvedIdent { item_id } => {
                    let found_item = self.item_headers[&item_id];

                    match found_item.kind() {
                        ItemKind::Const => {
                            let Some(vals) = self.const_vals.get( &found_item.id ) else {
                                let own_item = self.item_headers[&own_item_id];
                                let name = interner.resolve_lexeme(own_item.name.lexeme);
                                panic!("ICE: Encountered un-evaluated const during ident processing {name}");
                            };
                            for (_, val) in vals {
                                let (code, const_val) = match val {
                                    SimulatorValue::Int { kind, width } => (
                                        OpCode::PushInt {
                                            width: *width,
                                            value: *kind,
                                        },
                                        ConstVal::Int(*kind),
                                    ),
                                    SimulatorValue::Bool(val) => {
                                        (OpCode::PushBool(*val), ConstVal::Bool(*val))
                                    }
                                };
                                new_ops.push(Op {
                                    code,
                                    id: op.id,
                                    token: op.token,
                                    expansions: op.expansions.clone(),
                                });

                                let analyzer = self.analyzers.get_mut(&own_item_id).unwrap();
                                let op_io = analyzer.get_op_io(op.id);
                                let out_id = op_io.outputs()[0];
                                analyzer.set_value_const(out_id, const_val);
                            }
                        }
                        ItemKind::Memory => {
                            new_ops.push(Op {
                                code: OpCode::Memory {
                                    item_id,
                                    global: found_item.parent().is_none(),
                                },
                                id: op.id,
                                token: op.token,
                                expansions: op.expansions,
                            });
                        }
                        ItemKind::Function => {
                            new_ops.push(Op {
                                code: OpCode::CallFunction { item_id },
                                id: op.id,
                                token: op.token,
                                expansions: op.expansions,
                            });
                        }
                        ItemKind::Macro => {
                            let own_item = self.item_headers[&own_item_id];
                            let name = interner.resolve_lexeme(own_item.name.lexeme);
                            panic!(
                                "ICE: Encountered assert, or macro during ident processing {name}"
                            );
                        }

                        ItemKind::Assert => {
                            *had_error = true;
                            diagnostics::emit_error(
                                op.token.location,
                                "asserts cannot be used in operations",
                                Some(
                                    Label::new(op.token.location)
                                        .with_color(Color::Red)
                                        .with_message("here"),
                                ),
                                None,
                                source_store,
                            );
                            continue;
                        }
                    }
                }
                _ => new_ops.push(op),
            }
        }
        new_ops
    }

    fn process_idents(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::process_idents)).entered();
        let mut had_error = false;

        // Macros should already have been expanded.
        let all_item_ids: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, i)| i.kind() != ItemKind::Macro && i.kind() != ItemKind::Memory)
            .map(|(id, _)| *id)
            .collect();

        for own_item_id in all_item_ids {
            trace!("Processing {}", interner.get_symbol_name(self, own_item_id));

            let old_body = self.item_bodies.remove(&own_item_id).unwrap();
            let new_body = self.process_idents_in_block(
                own_item_id,
                old_body,
                &mut had_error,
                interner,
                source_store,
            );
            self.item_bodies.insert(own_item_id, new_body);
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error processing idents"))
    }

    fn check_asserts(&self, interner: &Interners, source_store: &SourceStorage) -> Result<()> {
        let _span = debug_span!(stringify!(Program::check_asserts)).entered();
        let mut had_error = false;

        for (&id, &item) in self.item_headers.iter() {
            if item.kind() != ItemKind::Assert {
                continue;
            }

            let assert_result = match simulate_execute_program(self, id, interner, source_store) {
                // Type check says we'll have a value at this point.
                Ok(mut stack) => {
                    let Some(SimulatorValue::Bool(val)) = stack.pop() else {
                        panic!("ICE: Simulated assert returned non-bool");
                    };
                    val
                }
                Err(_) => {
                    had_error = true;
                    continue;
                }
            };

            if !assert_result {
                diagnostics::emit_error(
                    item.name.location,
                    "assert failure",
                    Some(
                        Label::new(item.name.location)
                            .with_color(Color::Red)
                            .with_message("evaluated to false"),
                    ),
                    None,
                    source_store,
                );
                had_error = true;
            }
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("failed assert check"))
    }

    fn post_process_items(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
        type_store: &mut TypeStore,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::post_process_items)).entered();
        self.resolve_idents(interner, source_store)?;
        self.resolve_types(interner, source_store, type_store)?;

        self.check_invalid_cyclic_refs(interner, source_store)?;
        self.expand_macros(interner);

        self.determine_terminal_blocks(interner)?;

        self.analyze_data_flow(interner, source_store, type_store)?;
        self.evaluate_const_items(interner, source_store, type_store)?;

        self.process_idents(interner, source_store)?;
        self.check_asserts(interner, source_store)?;

        Ok(())
    }

    pub fn new_item(
        &mut self,
        name: Token,
        module: ModuleId,
        kind: ItemKind,
        parent: Option<ItemId>,
        sig: ItemSignatureUnresolved,
    ) -> ItemId {
        let id = self.item_headers.len();
        let id = ItemId(id.to_u16().unwrap());

        let item = ItemHeader {
            name,
            module,
            id,
            kind,
            parent,
            new_op_id: 0,
        };

        self.item_headers.insert(id, item);
        self.item_signatures_unresolved.insert(id, sig);

        if kind == ItemKind::Function {
            self.function_data.insert(id, FunctionData::default());
        }

        if parent.is_none() {
            let module = self.modules.get_mut(&module).unwrap();
            module.top_level_symbols.insert(name.lexeme, id);
        }

        id
    }

    pub fn get_visible_symbol(&self, from: ItemHeader, symbol: Spur) -> Option<ItemId> {
        if from.name.lexeme == symbol {
            return Some(from.id);
        }

        // Check our own children.
        if from.kind == ItemKind::Function {
            let fd = self.get_function_data(from.id);
            if let Some(found_id) = fd.allocs.get(&symbol).or_else(|| fd.consts.get(&symbol)) {
                return Some(*found_id);
            }
        }

        // Check our parent's children.
        let mut cur_id = from.parent;
        while let Some(id) = cur_id {
            let item = self.get_item_header(id);

            if item.name.lexeme == symbol {
                return Some(item.id);
            }

            if item.kind == ItemKind::Function {
                let fd = self.get_function_data(item.id);
                if let Some(found_id) = fd.allocs.get(&symbol).or_else(|| fd.consts.get(&symbol)) {
                    return Some(*found_id);
                }
            }
            cur_id = item.parent;
        }

        let module = &self.modules[&from.module];
        module.top_level_symbols.get(&symbol).copied()
    }
}

pub struct Module {
    name: Spur,
    top_level_symbols: HashMap<Spur, ItemId>,
}

impl Module {
    pub fn load(
        program: &mut Program,
        module_id: ModuleId,
        source_store: &mut SourceStorage,
        interner: &mut Interners,
        file: &str,
        include_queue: &mut Vec<Token>,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Module::load), file).entered();

        let contents =
            std::fs::read_to_string(file).with_context(|| eyre!("Failed to open file {}", file))?;

        let file_id = source_store.add(file, &contents);

        let tokens = lexer::lex_file(&contents, file_id, interner, source_store)
            .map_err(|_| eyre!("error lexing file: {}", file))?;

        let file_stem = Path::new(file).file_stem().and_then(OsStr::to_str).unwrap();
        interner.intern_lexeme(file_stem);

        parser::parse_module(
            program,
            module_id,
            &tokens,
            interner,
            include_queue,
            source_store,
        )
        .map_err(|_| eyre!("error parsing file: {}", file))?;

        Ok(())
    }

    pub fn get_item_id(&self, name: Spur) -> Option<ItemId> {
        self.top_level_symbols.get(&name).copied()
    }

    pub fn name(&self) -> Spur {
        self.name
    }
}

fn search_includes(paths: &[String], file_name: &Path) -> Option<String> {
    // Stupidly innefficient, but whatever...

    for path in paths {
        let path = Path::new(path).join(file_name);
        if path.exists() {
            return Some(
                path.to_str()
                    .map(ToOwned::to_owned)
                    .expect("Mangled string"),
            );
        }
    }

    None
}
