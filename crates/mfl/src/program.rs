use std::{collections::VecDeque, ffi::OsStr, hash::Hash, ops::Not, path::Path};

use ariadne::{Color, Label};
use color_eyre::eyre::{eyre, Context, Result};
use hashbrown::{HashMap, HashSet};
use intcast::IntCast;
use lasso::Spur;
use smallvec::SmallVec;
use tracing::{debug_span, trace, trace_span};

use crate::{
    diagnostics, lexer,
    opcode::{Op, OpCode, UnresolvedIdent},
    option::OptionExt,
    simulate::{simulate_execute_program, SimulationError, SimulatorValue},
    source_file::{FileId, SourceLocation, Spanned, WithSpan},
    type_store::{TypeId, TypeKind, UnresolvedStruct, UnresolvedType, UnresolvedTypeTokens},
    Args, Stores,
};

mod passes;
pub mod static_analysis;
use static_analysis::Analyzer;

const BUILTINS: &str = include_str!("builtins/builtins.mfl");

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ItemId(u16);

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
    #[inline]
    pub fn name(&self) -> Spanned<Spur> {
        self.name
    }

    #[inline]
    pub fn id(&self) -> ItemId {
        self.id
    }

    #[inline]
    pub fn parent(&self) -> Option<ItemId> {
        self.parent
    }

    #[inline]
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
    top_level_modules: HashMap<Spur, ItemId>,

    item_headers: Vec<ItemHeader>,
    scopes: Vec<Scope>,

    item_signatures_unresolved: HashMap<ItemId, ItemSignatureUnresolved>,
    item_signatures_resolved: HashMap<ItemId, ItemSignatureResolved>,
    memory_type_unresolved: HashMap<ItemId, Spanned<UnresolvedType>>,
    memory_type_resolved: HashMap<ItemId, TypeId>,
    item_bodies: HashMap<ItemId, Vec<Op>>,
    const_vals: HashMap<ItemId, Vec<(TypeId, SimulatorValue)>>,
    analyzers: HashMap<ItemId, Analyzer>,

    structs_unresolved: HashMap<ItemId, UnresolvedStruct>,
    generic_functions_map: HashMap<(ItemId, String), ItemId>,
    generic_template_parameters: HashMap<ItemId, Vec<Spanned<Spur>>>,
}

impl Program {
    #[inline]
    pub fn get_all_items(&self) -> impl Iterator<Item = ItemHeader> + '_ {
        self.item_headers.iter().copied()
    }

    #[track_caller]
    #[inline]
    pub fn get_scope(&self, id: ItemId) -> &Scope {
        &self.scopes[id.0.to_usize()]
    }

    #[track_caller]
    #[inline]
    pub fn get_scope_mut(&mut self, id: ItemId) -> &mut Scope {
        &mut self.scopes[id.0.to_usize()]
    }

    #[inline]
    pub fn get_item_header(&self, id: ItemId) -> ItemHeader {
        self.item_headers[id.0.to_usize()]
    }

    #[track_caller]
    #[inline]
    pub fn get_item_signature_unresolved(&self, id: ItemId) -> &ItemSignatureUnresolved {
        &self.item_signatures_unresolved[&id]
    }

    #[track_caller]
    #[inline]
    pub fn get_item_signature_resolved(&self, id: ItemId) -> &ItemSignatureResolved {
        &self.item_signatures_resolved[&id]
    }

    #[track_caller]
    #[inline]
    pub fn get_memory_type_unresolved(&self, id: ItemId) -> Spanned<&UnresolvedType> {
        let v = &self.memory_type_unresolved[&id];

        (&v.inner).with_span(v.location)
    }

    #[track_caller]
    #[inline]
    pub fn get_memory_type_resolved(&self, id: ItemId) -> TypeId {
        self.memory_type_resolved[&id]
    }

    #[track_caller]
    #[inline]
    pub fn get_item_body(&self, id: ItemId) -> &[Op] {
        &self.item_bodies[&id]
    }

    #[inline]
    pub fn set_item_body(&mut self, id: ItemId, body: Vec<Op>) {
        self.item_bodies.insert(id, body);
    }

    #[inline]
    pub fn get_analyzer(&self, id: ItemId) -> &Analyzer {
        &self.analyzers[&id]
    }

    #[inline]
    pub fn get_consts(&self, id: ItemId) -> Option<&[(TypeId, SimulatorValue)]> {
        self.const_vals.get(&id).map(|v| &**v)
    }
}

impl Program {
    pub fn new() -> Self {
        Program {
            top_level_modules: Default::default(),
            item_headers: Vec::new(),
            scopes: Vec::new(),
            item_signatures_unresolved: HashMap::new(),
            item_signatures_resolved: HashMap::new(),
            memory_type_resolved: HashMap::new(),
            memory_type_unresolved: HashMap::new(),
            item_bodies: HashMap::new(),
            const_vals: HashMap::new(),
            analyzers: HashMap::new(),
            structs_unresolved: HashMap::new(),
            generic_functions_map: HashMap::new(),
            generic_template_parameters: HashMap::new(),
        }
    }

    pub fn load_program2(&mut self, stores: &mut Stores, args: &Args) -> Result<ItemId> {
        let _span = debug_span!(stringify!(Program::load_program)).entered();
        let mut had_error = false;

        let builtin_structs_module_name = stores.strings.intern("builtins");
        let builtin_module = self.new_module(
            stores,
            &mut had_error,
            builtin_structs_module_name.with_span(SourceLocation::new(FileId::dud(), 0..0)),
            None,
        );
        self.top_level_modules
            .insert(builtin_structs_module_name, builtin_module);
        self.load_module(
            stores,
            builtin_module,
            Path::new("builtins"),
            BUILTINS,
            &mut VecDeque::new(),
        )?;
        stores.types.update_builtins(&self.structs_unresolved);

        let module_name = args.file.file_stem().and_then(OsStr::to_str).unwrap();
        let main_lib_root = args.file.parent().unwrap();
        let root_file_name = args.file.file_name().unwrap();
        let entry_module = self.load_library(
            stores,
            &mut had_error,
            module_name,
            root_file_name,
            main_lib_root,
        );

        for lib in &args.library_paths {
            let module_name = lib.file_stem().and_then(OsStr::to_str).unwrap();
            had_error |= self
                .load_library(
                    stores,
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

        self.post_process_items(stores, args.print_stack_depths)?;

        entry_module
    }

    fn load_library(
        &mut self,
        stores: &mut Stores,
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
                        stores
                            .strings
                            .intern(lib_name)
                            .with_span(SourceLocation::new(FileId::dud(), 0..0)),
                    )
                }
                ModuleQueueType::Include(token) => {
                    if loaded_modules.contains(&token.inner) {
                        continue;
                    }
                    loaded_modules.insert(token.inner);

                    let name = stores.strings.resolve(token.inner);
                    root.push(name);
                    root.set_extension("mfl");

                    let contents = match std::fs::read_to_string(&root) {
                        Ok(c) => c,
                        Err(e) => {
                            diagnostics::emit_error(
                                stores,
                                token.location,
                                format!("error loading module: {e}"),
                                [Label::new(token.location).with_color(Color::Red)],
                                None,
                            );
                            *had_error = true;
                            root.pop();
                            continue;
                        }
                    };

                    (contents, token)
                }
            };

            let module_id = self.new_module(stores, had_error, module_name, parent);
            if module == ModuleQueueType::Root {
                self.top_level_modules.insert(module_name.inner, module_id);
            }

            first_module = first_module.or(Some(module_id));

            let res = self.load_module(stores, module_id, &root, &contents, &mut module_queue);

            *had_error |= res.is_err();

            root.pop();
        }

        Ok(first_module.unwrap())
    }

    fn load_module(
        &mut self,
        stores: &mut Stores,
        module_id: ItemId,
        file: &Path,
        file_contents: &str,
        include_queue: &mut VecDeque<(ModuleQueueType, Option<ItemId>)>,
    ) -> Result<()> {
        let file_type = format!("{file:?}");
        let _span = debug_span!(stringify!(Module::load), file_type).entered();

        let file_id = stores.source.add(file, file_contents);

        let tokens = lexer::lex_file(stores, file_contents, file_id)
            .map_err(|_| eyre!("error lexing file: {}", file.display()))?;

        let file_stem = Path::new(file).file_stem().and_then(OsStr::to_str).unwrap();
        stores.strings.intern(file_stem);

        crate::parser::parse_file(self, stores, module_id, &tokens, include_queue)
            .map_err(|_| eyre!("error parsing file: {}", file.display()))?;

        Ok(())
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

    fn determine_terminal_blocks(&mut self, stores: &mut Stores) {
        let _span = debug_span!(stringify!(Program::determine_terminal_blocks)).entered();
        let items: Vec<_> = self
            .item_headers
            .iter()
            .filter(|i| {
                i.kind() != ItemKind::Memory
                    && i.kind() != ItemKind::StructDef
                    && i.kind() != ItemKind::Module
            })
            .map(|i| i.id)
            .collect();

        for item_id in items {
            trace!(name = stores.strings.get_symbol_name(self, item_id));

            let mut body = self.item_bodies.remove(&item_id).unwrap();
            self.determine_terminal_blocks_in_block(&mut body);
            self.item_bodies.insert(item_id, body);
        }
    }

    fn analyze_data_flow(&mut self, stores: &mut Stores, print_stack_depths: bool) -> Result<()> {
        let _span = debug_span!(stringify!(Program::analyze_data_flow)).entered();
        let mut had_error = false;
        let items: Vec<_> = self
            .item_headers
            .iter()
            .filter(|i| {
                i.kind() != ItemKind::Memory
                    && i.kind() != ItemKind::StructDef
                    && i.kind() != ItemKind::Module
                    && i.kind() != ItemKind::GenericFunction
            })
            .map(|i| i.id)
            .collect();

        for id in items {
            let _span = trace_span!(
                "Analyzing item",
                name = stores.strings.get_symbol_name(self, id)
            )
            .entered();
            let mut analyzer = Analyzer::default();
            had_error |=
                static_analysis::analyze_item(self, stores, &mut analyzer, id, print_stack_depths)
                    .is_err();

            self.analyzers.insert(id, analyzer);
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("data analysis error"))
    }

    fn evaluate_const_items(&mut self, stores: &mut Stores) -> Result<()> {
        let _span = debug_span!(stringify!(Program::evaluate_const_items)).entered();
        let mut had_error = false;

        let mut const_queue: Vec<_> = self
            .item_headers
            .iter()
            .filter(|item| item.kind() == ItemKind::Const)
            .map(|i| i.id)
            .collect();
        let mut next_run_queue = Vec::with_capacity(const_queue.len());

        loop {
            for const_id in const_queue.drain(..) {
                let item_sig = self.get_item_signature_resolved(const_id);
                match simulate_execute_program(self, stores, const_id) {
                    Ok(stack) => {
                        let const_vals = stack
                            .into_iter()
                            .zip(&item_sig.exit_stack)
                            .map(|(val, ty)| {
                                let expected_type = stores.types.get_type_info(*ty);
                                let val = match val {
                                    SimulatorValue::Int { kind, .. } => {
                                        let TypeKind::Integer {
                                            width: to_width,
                                            signed: to_signed,
                                        } = expected_type.kind
                                        else {
                                            unreachable!()
                                        };

                                        SimulatorValue::Int {
                                            width: to_width,
                                            kind: kind.cast(to_width, to_signed),
                                        }
                                    }
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

    fn check_asserts(&self, stores: &mut Stores) -> Result<()> {
        let _span = debug_span!(stringify!(Program::check_asserts)).entered();
        let mut had_error = false;

        for &item in &self.item_headers {
            if item.kind() != ItemKind::Assert {
                continue;
            }

            let assert_result = match simulate_execute_program(self, stores, item.id) {
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
                    stores,
                    item.name.location,
                    "assert failure",
                    Some(
                        Label::new(item.name.location)
                            .with_color(Color::Red)
                            .with_message("evaluated to false"),
                    ),
                    None,
                );
                had_error = true;
            }
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("failed assert check"))
    }

    fn post_process_items(&mut self, stores: &mut Stores, print_stack_depths: bool) -> Result<()> {
        let _span = debug_span!(stringify!(Program::post_process_items)).entered();
        self.resolve_idents(stores)?;
        self.instantiate_generic_functions(stores)?;
        self.resolve_struct_defs(stores)?;
        self.resolve_types(stores)?;

        self.check_invalid_cyclic_refs(stores)?;

        self.determine_terminal_blocks(stores);

        self.analyze_data_flow(stores, print_stack_depths)?;
        self.evaluate_const_items(stores)?;

        self.process_idents(stores)?;
        self.check_asserts(stores)?;

        Ok(())
    }
}

impl Program {
    fn add_to_parent(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        parent_id: ItemId,
        child_name: Spanned<Spur>,
        child_id: ItemId,
    ) {
        let parent_scope = &mut self.scopes[parent_id.0.to_usize()];
        if let Err(prev_loc) = parent_scope.add_child(child_name, child_id) {
            *had_error = true;
            symbol_redef_error(stores, child_name.location, prev_loc);
        }
    }

    fn new_header(
        &mut self,
        name: Spanned<Spur>,
        parent: Option<ItemId>,
        kind: ItemKind,
    ) -> ItemHeader {
        let new_id = self.item_headers.len();
        let new_id = ItemId(new_id.to_u16().unwrap());

        let item_header = ItemHeader {
            name,
            id: new_id,
            parent,
            kind,
        };
        self.item_headers.push(item_header);
        self.scopes.push(Scope {
            child_items: HashMap::new(),
            visible_symbols: HashMap::new(),
            unresolved_imports: Vec::new(),
        });
        item_header
    }

    fn new_module(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: Option<ItemId>,
    ) -> ItemId {
        let header = self.new_header(name, parent, ItemKind::Module);

        if let Some(parent_id) = parent {
            self.add_to_parent(stores, had_error, parent_id, name, header.id);
        }

        header.id
    }

    pub fn new_function(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
        entry_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Function);
        self.item_signatures_unresolved.insert(
            header.id,
            ItemSignatureUnresolved {
                exit_stack,
                entry_stack,
            },
        );

        self.add_to_parent(stores, had_error, parent, name, header.id);

        header.id
    }

    pub fn new_assert(
        &mut self,
        stores: &mut Stores,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Assert);
        // Such a hack.
        let bool_symbol = stores.strings.intern("bool");
        self.item_signatures_unresolved.insert(
            header.id,
            ItemSignatureUnresolved {
                exit_stack: vec![UnresolvedType::Tokens(UnresolvedTypeTokens::Simple(
                    UnresolvedIdent {
                        span: name.location,
                        is_from_root: false,
                        path: vec![bool_symbol.with_span(name.location)],
                        generic_params: None,
                    },
                ))
                .with_span(name.location)]
                .with_span(name.location),
                entry_stack: Vec::new().with_span(name.location),
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
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Const);
        self.item_signatures_unresolved.insert(
            header.id,
            ItemSignatureUnresolved {
                exit_stack,
                entry_stack: Vec::new().with_span(name.location),
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
        entry_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
        params: Vec<Spanned<Spur>>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::GenericFunction);
        self.item_signatures_unresolved.insert(
            header.id,
            ItemSignatureUnresolved {
                entry_stack,
                exit_stack,
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
    ) {
        let name = def.name;
        let header = self.new_header(name, Some(module), ItemKind::StructDef);
        self.structs_unresolved.insert(header.id, def);

        self.add_to_parent(stores, had_error, module, name, header.id);
    }

    pub fn new_memory(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        name: Spanned<Spur>,
        parent: ItemId,
        memory_type: Spanned<UnresolvedType>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Memory);
        self.memory_type_unresolved.insert(header.id, memory_type);

        self.add_to_parent(stores, had_error, parent, name, header.id);

        header.id
    }

    pub fn get_visible_symbol(&self, from: ItemHeader, symbol: Spur) -> Option<ItemId> {
        // 1. Check ourselves
        if from.name.inner == symbol {
            return Some(from.id);
        }

        // 2. Check our children
        let own_scope = self.get_scope(from.id);
        if let Some(child) = own_scope.get_symbol(symbol) {
            return Some(child);
        }

        // 3. If we're not a module traverse up the tree checking siblings until we hit a module.
        if from.kind != ItemKind::Module {
            let mut parent = from.parent;
            while let Some(parent_id) = parent {
                let parent_scope = self.get_scope(parent_id);
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

#[derive(Debug, Clone)]
pub struct Scope {
    child_items: HashMap<Spur, Spanned<ItemId>>,
    visible_symbols: HashMap<Spur, Spanned<ItemId>>,
    unresolved_imports: Vec<UnresolvedIdent>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ModuleQueueType {
    Root,
    Include(Spanned<Spur>),
}

impl Scope {
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

    fn add_visible_symbol(
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

    pub fn add_unresolved_import(&mut self, path: UnresolvedIdent) {
        self.unresolved_imports.push(path);
    }
}

fn symbol_redef_error(stores: &Stores, new_def: SourceLocation, prev_def: SourceLocation) {
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
