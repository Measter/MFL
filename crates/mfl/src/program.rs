use std::{
    collections::{BTreeMap, VecDeque},
    ffi::OsStr,
    hash::Hash,
    ops::Not,
    path::Path,
};

use ariadne::{Color, Label};
use color_eyre::eyre::{eyre, Context, Result};
use hashbrown::{HashMap, HashSet};
use intcast::IntCast;
use lasso::Spur;
use smallvec::SmallVec;
use tracing::{debug_span, trace, trace_span};

use crate::{
    diagnostics,
    interners::Interners,
    lexer,
    opcode::{Op, OpCode},
    option::OptionExt,
    simulate::{simulate_execute_program, SimulationError, SimulatorValue},
    source_file::{FileId, SourceLocation, SourceStorage, Spanned, WithSpan},
    type_store::{TypeId, TypeKind, TypeStore, UnresolvedStruct, UnresolvedType},
    Args,
};

mod passes;
pub mod static_analysis;
use static_analysis::Analyzer;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
    pub generic_params: Vec<Spanned<Spur>>,
}

// TODO: Add compile-time asserts
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
    name: Spanned<Spur>,
    id: ItemId,
    parent: Option<ItemId>,
    kind: ItemKind,
}

impl ItemHeader {
    pub fn name(&self) -> Spanned<Spur> {
        self.name
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
    pub exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
    pub entry_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
}

impl ItemSignatureUnresolved {
    pub fn exit_stack(&self) -> &[Spanned<UnresolvedType>] {
        &self.exit_stack.inner
    }

    pub fn exit_stack_location(&self) -> SourceLocation {
        self.exit_stack.location
    }

    pub fn entry_stack(&self) -> &[Spanned<UnresolvedType>] {
        &self.entry_stack.inner
    }

    pub fn entry_stack_location(&self) -> SourceLocation {
        self.entry_stack.location
    }
}
pub struct ItemSignatureResolved {
    exit_stack: SmallVec<[TypeId; 8]>,
    entry_stack: SmallVec<[TypeId; 8]>,
}

impl ItemSignatureResolved {
    pub fn exit_stack(&self) -> &[TypeId] {
        &self.exit_stack
    }

    pub fn entry_stack(&self) -> &[TypeId] {
        &self.entry_stack
    }
}

pub struct Program {
    module_info: HashMap<ItemId, ModuleInfo>,
    top_level_modules: HashMap<Spur, ItemId>,

    item_headers: BTreeMap<ItemId, ItemHeader>,
    item_signatures_unresolved: HashMap<ItemId, ItemSignatureUnresolved>,
    item_signatures_resolved: HashMap<ItemId, ItemSignatureResolved>,
    memory_type_unresolved: HashMap<ItemId, Spanned<UnresolvedType>>,
    memory_type_resolved: HashMap<ItemId, TypeId>,
    item_bodies: HashMap<ItemId, Vec<Op>>,
    function_data: HashMap<ItemId, FunctionData>,
    const_vals: HashMap<ItemId, Vec<(TypeId, SimulatorValue)>>,
    analyzers: HashMap<ItemId, Analyzer>,

    structs_unresolved: HashMap<ItemId, UnresolvedStruct>,
    generic_functions_map: HashMap<(ItemId, String), ItemId>,
}

impl Program {
    pub fn get_all_items(&self) -> impl Iterator<Item = (ItemId, ItemHeader)> + '_ {
        self.item_headers.iter().map(|(id, item)| (*id, *item))
    }

    #[track_caller]
    pub fn get_module(&self, id: ItemId) -> &ModuleInfo {
        &self.module_info[&id]
    }

    #[track_caller]
    pub fn get_module_mut(&mut self, id: ItemId) -> &mut ModuleInfo {
        self.module_info.get_mut(&id).unwrap()
    }

    pub fn get_item_header(&self, id: ItemId) -> ItemHeader {
        self.item_headers[&id]
    }

    pub fn get_item_header_mut(&mut self, id: ItemId) -> &mut ItemHeader {
        self.item_headers.get_mut(&id).unwrap()
    }

    #[track_caller]
    pub fn get_item_signature_unresolved(&self, id: ItemId) -> &ItemSignatureUnresolved {
        &self.item_signatures_unresolved[&id]
    }

    #[track_caller]
    pub fn get_item_signature_resolved(&self, id: ItemId) -> &ItemSignatureResolved {
        &self.item_signatures_resolved[&id]
    }

    #[track_caller]
    pub fn get_memory_type_unresolved(&self, id: ItemId) -> Spanned<&UnresolvedType> {
        let v = &self.memory_type_unresolved[&id];

        (&v.inner).with_span(v.location)
    }

    #[track_caller]
    pub fn get_memory_type_resolved(&self, id: ItemId) -> TypeId {
        self.memory_type_resolved[&id]
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
            module_info: Default::default(),
            top_level_modules: Default::default(),
            item_headers: BTreeMap::new(),
            item_signatures_unresolved: HashMap::new(),
            item_signatures_resolved: HashMap::new(),
            memory_type_resolved: HashMap::new(),
            memory_type_unresolved: HashMap::new(),
            item_bodies: HashMap::new(),
            function_data: HashMap::new(),
            const_vals: HashMap::new(),
            analyzers: HashMap::new(),
            structs_unresolved: HashMap::new(),
            generic_functions_map: HashMap::new(),
        }
    }

    fn new_module(
        &mut self,
        source_store: &SourceStorage,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: Option<ItemId>,
    ) -> ItemId {
        let new_id = self.item_headers.len();
        let new_id = ItemId(new_id.to_u16().unwrap());

        let item_header = ItemHeader {
            name,
            id: new_id,
            parent,
            kind: ItemKind::Module,
        };
        self.item_headers.insert(new_id, item_header);

        let module = ModuleInfo {
            child_items: HashMap::new(),
            visible_symbols: HashMap::new(),
            unresolved_imports: Vec::new(),
        };
        self.module_info.insert(new_id, module);

        if let Some(parent_id) = parent {
            let parent_module = self.module_info.get_mut(&parent_id).unwrap();
            let res = parent_module.add_child(name.inner, name.location, new_id);
            if let Err(prev_loc) = res {
                *had_error = true;
                symbol_redef_error(name.location, prev_loc, source_store);
            }
        }

        new_id
    }

    pub fn load_program2(
        &mut self,
        interner: &mut Interners,
        source_store: &mut SourceStorage,
        type_store: &mut TypeStore,
        args: &Args,
    ) -> Result<ItemId> {
        let _span = debug_span!(stringify!(Program::load_program)).entered();
        let mut had_error = false;

        let builtin_structs_module_name = interner.intern_lexeme("builtins");
        let builtin_module = self.new_module(
            source_store,
            &mut had_error,
            builtin_structs_module_name.with_span(SourceLocation::new(FileId::dud(), 0..0)),
            None,
        );
        ModuleInfo::load(
            self,
            builtin_module,
            source_store,
            interner,
            Path::new("builtin"),
            crate::type_store::STRING_DEF,
            &mut VecDeque::new(),
        )?;
        type_store.update_builtins(&self.structs_unresolved);

        let module_name = args.file.file_stem().and_then(OsStr::to_str).unwrap();
        let main_lib_root = args.file.parent().unwrap();
        let root_file_name = args.file.file_name().unwrap();
        let entry_module = self.load_library(
            interner,
            source_store,
            &mut had_error,
            module_name,
            root_file_name,
            main_lib_root,
        );

        for lib in &args.library_paths {
            let module_name = lib.file_stem().and_then(OsStr::to_str).unwrap();
            had_error |= self
                .load_library(
                    interner,
                    source_store,
                    &mut had_error,
                    module_name,
                    OsStr::new("lib.mfl"),
                    lib,
                )
                .is_err();
        }

        if had_error {
            return Err(eyre!("Error loading program"));
        }

        self.post_process_items(interner, source_store, type_store, args.print_stack_depths)?;

        entry_module
    }

    fn load_library(
        &mut self,
        interner: &mut Interners,
        source_store: &mut SourceStorage,
        had_error: &mut bool,
        lib_name: &str,
        lib_filename: &OsStr,
        lib_path: &Path,
    ) -> Result<ItemId> {
        let mut loaded_modules = HashSet::new();
        let mut module_queue = VecDeque::new();

        let mut root = lib_path.to_owned();

        module_queue.push_back((ModuleQueueType::Root, None));

        let mut first_module = None;
        while let Some((module, parent)) = module_queue.pop_front() {
            let (contents, module_name) = match module {
                ModuleQueueType::Root => {
                    root.push(lib_filename);

                    let contents = match std::fs::read_to_string(&root) {
                        Ok(c) => c,
                        Err(e) => {
                            return Err(e)
                                .with_context(|| eyre!("failed to load `{}`", root.display()));
                        }
                    };
                    (
                        contents,
                        interner
                            .intern_lexeme(lib_name)
                            .with_span(SourceLocation::new(FileId::dud(), 0..0)),
                    )
                }
                ModuleQueueType::Include(token) => {
                    if loaded_modules.contains(&token.inner) {
                        continue;
                    }
                    loaded_modules.insert(token.inner);

                    let name = interner.resolve_lexeme(token.inner);
                    root.push(name);
                    root.set_extension("mfl");

                    let contents = match std::fs::read_to_string(&root) {
                        Ok(c) => c,
                        Err(e) => {
                            diagnostics::emit_error(
                                token.location,
                                format!("error loading module: {e}"),
                                [Label::new(token.location).with_color(Color::Red)],
                                None,
                                source_store,
                            );
                            *had_error = true;
                            root.pop();
                            continue;
                        }
                    };

                    (contents, token)
                }
            };

            let module_id = self.new_module(source_store, had_error, module_name, parent);
            if module == ModuleQueueType::Root {
                self.top_level_modules.insert(module_name.inner, module_id);
            }

            first_module = first_module.or(Some(module_id));

            let res = ModuleInfo::load(
                self,
                module_id,
                source_store,
                interner,
                &root,
                &contents,
                &mut module_queue,
            );

            *had_error |= res.is_err();

            root.pop();
        }

        Ok(first_module.unwrap())
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
                OpCode::Return | OpCode::Exit => return true,
                _ => {}
            }
        }

        false
    }

    fn determine_terminal_blocks(&mut self, interner: &mut Interners) {
        let _span = debug_span!(stringify!(Program::determine_terminal_blocks)).entered();
        let items: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, i)| {
                i.kind() != ItemKind::Memory
                    && i.kind() != ItemKind::StructDef
                    && i.kind() != ItemKind::Module
            })
            .map(|(id, _)| *id)
            .collect();

        for item_id in items {
            trace!(name = interner.get_symbol_name(self, item_id));

            let mut body = self.item_bodies.remove(&item_id).unwrap();
            self.determine_terminal_blocks_in_block(&mut body);
            self.item_bodies.insert(item_id, body);
        }
    }

    fn analyze_data_flow(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
        type_store: &mut TypeStore,
        print_stack_depths: bool,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::analyze_data_flow)).entered();
        let mut had_error = false;
        let items: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, i)| {
                i.kind() != ItemKind::Memory
                    && i.kind() != ItemKind::StructDef
                    && i.kind() != ItemKind::Module
                    && i.kind() != ItemKind::GenericFunction
            })
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
                print_stack_depths,
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
                match simulate_execute_program(self, type_store, const_id, interner, source_store) {
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

    fn check_asserts(
        &self,
        interner: &Interners,
        source_store: &SourceStorage,
        type_store: &mut TypeStore,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::check_asserts)).entered();
        let mut had_error = false;

        for (&id, &item) in &self.item_headers {
            if item.kind() != ItemKind::Assert {
                continue;
            }

            let assert_result =
                match simulate_execute_program(self, type_store, id, interner, source_store) {
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
        print_stack_depths: bool,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::post_process_items)).entered();
        self.resolve_idents(interner, source_store)?;
        self.instantiate_generic_functions(interner, source_store)?;
        self.resolve_struct_defs(interner, source_store, type_store)?;
        self.resolve_types(interner, source_store, type_store)?;

        self.check_invalid_cyclic_refs(interner, source_store)?;

        self.determine_terminal_blocks(interner);

        self.analyze_data_flow(interner, source_store, type_store, print_stack_depths)?;
        self.evaluate_const_items(interner, source_store, type_store)?;

        self.process_idents(interner, source_store)?;
        self.check_asserts(interner, source_store, type_store)?;

        Ok(())
    }

    pub fn new_item(
        &mut self,
        source_store: &SourceStorage,
        had_error: &mut bool,
        name: Spanned<Spur>,
        kind: ItemKind,
        parent: ItemId,
        sig: ItemSignatureUnresolved,
    ) -> ItemId {
        let id = self.item_headers.len();
        let id = ItemId(id.to_u16().unwrap());

        let item = ItemHeader {
            name,
            id,
            kind,
            parent: Some(parent),
        };

        self.item_headers.insert(id, item);
        self.item_signatures_unresolved.insert(id, sig);

        if kind == ItemKind::Function {
            self.function_data.insert(id, FunctionData::default());
        }

        let parent_info = self.item_headers[&parent];
        if parent_info.kind == ItemKind::Module {
            let module_info = self.module_info.get_mut(&parent).unwrap();
            let res = module_info.add_child(name.inner, name.location, id);
            if let Err(prev_loc) = res {
                *had_error = true;
                symbol_redef_error(name.location, prev_loc, source_store);
            }
        }

        id
    }

    pub fn new_const(
        &mut self,
        source_store: &SourceStorage,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
    ) -> ItemId {
        let id = self.item_headers.len();
        let id = ItemId(id.to_u16().unwrap());

        let item = ItemHeader {
            name,
            id,
            kind: ItemKind::Const,
            parent: Some(parent),
        };

        self.item_headers.insert(id, item);
        self.item_signatures_unresolved.insert(
            id,
            ItemSignatureUnresolved {
                exit_stack,
                entry_stack: Vec::new().with_span(name.location),
            },
        );

        let parent_info = self.item_headers[&parent];
        if parent_info.kind == ItemKind::Module {
            let module_info = self.module_info.get_mut(&parent).unwrap();
            let res = module_info.add_child(name.inner, name.location, id);
            if let Err(prev_loc) = res {
                *had_error = true;
                symbol_redef_error(name.location, prev_loc, source_store);
            }
        }

        id
    }

    pub fn new_generic_function(
        &mut self,
        source_store: &SourceStorage,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
        sig: ItemSignatureUnresolved,
        params: Vec<Spanned<Spur>>,
    ) -> ItemId {
        let id = self.item_headers.len();
        let id = ItemId(id.to_u16().unwrap());

        let item = ItemHeader {
            name,
            id,
            kind: ItemKind::GenericFunction,
            parent: Some(parent),
        };

        self.item_headers.insert(id, item);
        self.item_signatures_unresolved.insert(id, sig);

        self.function_data.insert(
            id,
            FunctionData {
                generic_params: params,
                ..Default::default()
            },
        );

        let parent_info = self.item_headers[&parent];
        if parent_info.kind == ItemKind::Module {
            let module_info = self.module_info.get_mut(&parent).unwrap();
            let res = module_info.add_child(name.inner, name.location, id);
            if let Err(prev_loc) = res {
                *had_error = true;
                symbol_redef_error(name.location, prev_loc, source_store);
            }
        }

        id
    }

    pub fn new_struct(
        &mut self,
        source_store: &SourceStorage,
        had_error: &mut bool,
        module: ItemId,
        def: UnresolvedStruct,
    ) {
        let id = self.item_headers.len();
        let id = ItemId(id.to_u16().unwrap());
        let name = def.name;

        let item = ItemHeader {
            name,
            id,
            kind: ItemKind::StructDef,
            parent: Some(module),
        };

        self.item_headers.insert(id, item);
        let name = def.name;
        self.structs_unresolved.insert(id, def);

        let module = self.module_info.get_mut(&module).unwrap();
        let res = module.add_child(name.inner, name.location, id);

        if let Err(prev_loc) = res {
            *had_error = true;
            symbol_redef_error(name.location, prev_loc, source_store);
        }
    }

    pub fn new_memory(
        &mut self,
        source_store: &SourceStorage,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
        memory_type: Spanned<UnresolvedType>,
    ) -> ItemId {
        let id = self.item_headers.len();
        let id = ItemId(id.to_u16().unwrap());

        let item = ItemHeader {
            name,
            id,
            kind: ItemKind::Memory,
            parent: Some(parent),
        };

        self.item_headers.insert(id, item);
        self.memory_type_unresolved.insert(id, memory_type);

        let parent_info = self.item_headers[&parent];
        if parent_info.kind == ItemKind::Module {
            let module_info = self.module_info.get_mut(&parent).unwrap();
            let res = module_info.add_child(name.inner, name.location, id);
            if let Err(prev_loc) = res {
                *had_error = true;
                symbol_redef_error(name.location, prev_loc, source_store);
            }
        }

        id
    }

    pub fn get_visible_symbol(&self, from: ItemHeader, symbol: Spur) -> Option<ItemId> {
        if from.name.inner == symbol {
            return Some(from.id);
        }

        // Check our own children.
        if from.kind == ItemKind::Function || from.kind == ItemKind::GenericFunction {
            let fd = self.get_function_data(from.id);
            if let Some(found_id) = fd.allocs.get(&symbol).or_else(|| fd.consts.get(&symbol)) {
                return Some(*found_id);
            }
        }
        // If we're a module, then we don't traverse up the tree.
        if from.kind == ItemKind::Module {
            let module = &self.module_info[&from.id];
            return module.get_visible_symbol(symbol);
        }

        // Check our parent's children.
        let mut prev_kind = from.kind;
        let mut cur_id = from.parent;
        while let Some(id) = cur_id {
            let item = self.get_item_header(id);

            if item.kind == ItemKind::Function || item.kind == ItemKind::GenericFunction {
                let fd = self.get_function_data(item.id);
                if let Some(found_id) = fd.allocs.get(&symbol).or_else(|| fd.consts.get(&symbol)) {
                    return Some(*found_id);
                }
            } else if item.kind == ItemKind::Module && prev_kind == ItemKind::Module {
                // Don't traverse up the module tree. We should only look within the current module.
                return None;
            } else if item.kind == ItemKind::Module {
                let module = &self.module_info[&id];
                if let Some(found_id) = module.get_visible_symbol(symbol) {
                    return Some(found_id);
                }
            }
            prev_kind = item.kind;
            cur_id = item.parent;
        }

        None
    }
}

pub struct ModuleInfo {
    child_items: HashMap<Spur, Spanned<ItemId>>,
    visible_symbols: HashMap<Spur, Spanned<ItemId>>,
    unresolved_imports: Vec<Spanned<Vec<Spanned<Spur>>>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ModuleQueueType {
    Root,
    Include(Spanned<Spur>),
}

impl ModuleInfo {
    pub fn load(
        program: &mut Program,
        module_id: ItemId,
        source_store: &mut SourceStorage,
        interner: &mut Interners,
        file: &Path,
        file_contents: &str,
        include_queue: &mut VecDeque<(ModuleQueueType, Option<ItemId>)>,
    ) -> Result<()> {
        let file_type = format!("{file:?}");
        let _span = debug_span!(stringify!(Module::load), file_type).entered();

        let file_id = source_store.add(file, file_contents);

        let tokens = lexer::lex_file(file_contents, file_id, interner, source_store)
            .map_err(|_| eyre!("error lexing file: {}", file.display()))?;

        let file_stem = Path::new(file).file_stem().and_then(OsStr::to_str).unwrap();
        interner.intern_lexeme(file_stem);

        crate::parser::parse_file(
            program,
            module_id,
            &tokens,
            interner,
            include_queue,
            source_store,
        )
        .map_err(|_| eyre!("error parsing file: {}", file.display()))?;

        Ok(())
    }

    pub fn get_visible_symbol(&self, name: Spur) -> Option<ItemId> {
        self.visible_symbols.get(&name).map(|id| id.inner)
    }

    pub fn get_child_items(&self) -> &HashMap<Spur, Spanned<ItemId>> {
        &self.child_items
    }

    fn add_child(
        &mut self,
        name: Spur,
        loc: SourceLocation,
        id: ItemId,
    ) -> Result<(), SourceLocation> {
        use hashbrown::hash_map::Entry;
        match self.child_items.entry(name) {
            Entry::Occupied(a) => return Err(a.get().location),
            Entry::Vacant(a) => a.insert(id.with_span(loc)),
        };

        // Children are added before imports are resolved, so this should never fail.
        self.visible_symbols
            .insert(name, id.with_span(loc))
            .expect_none("ICE: Name collision when adding child");
        Ok(())
    }

    pub fn add_visible_symbol(
        &mut self,
        name: Spur,
        loc: SourceLocation,
        id: ItemId,
    ) -> Result<(), SourceLocation> {
        use hashbrown::hash_map::Entry;
        match self.visible_symbols.entry(name) {
            Entry::Occupied(a) => return Err(a.get().location),
            Entry::Vacant(a) => a.insert(id.with_span(loc)),
        };
        Ok(())
    }

    pub fn add_unresolved_import(&mut self, path: Vec<Spanned<Spur>>) {
        let loc = path
            .iter()
            .map(|t| t.location)
            .reduce(SourceLocation::merge)
            .unwrap();
        self.unresolved_imports.push(path.with_span(loc));
    }
}

fn symbol_redef_error(
    new_def: SourceLocation,
    prev_def: SourceLocation,
    source_store: &SourceStorage,
) {
    diagnostics::emit_error(
        new_def,
        "item of that name already exists",
        [
            Label::new(new_def).with_color(Color::Red),
            Label::new(prev_def)
                .with_color(Color::Cyan)
                .with_message("previously defined here"),
        ],
        None,
        source_store,
    );
}