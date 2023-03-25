use std::{
    collections::BTreeMap,
    ffi::OsStr,
    ops::Not,
    path::{Path, PathBuf},
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
    lexer::{self, Token},
    opcode::{Op, OpCode, OpId},
    simulate::{simulate_execute_program, SimulationError, SimulatorValue},
    source_file::{SourceLocation, SourceStorage},
    type_store::{TypeId, TypeKind, TypeStore, UnresolvedStruct, UnresolvedType},
};

mod parser;
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
}

// TODO: Add compile-time asserts
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ItemKind {
    Assert,
    Const,
    Macro,
    Memory,
    Function,
    StructDef,
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

    item_headers: BTreeMap<ItemId, ItemHeader>,
    item_signatures_unresolved: HashMap<ItemId, ItemSignatureUnresolved>,
    item_signatures_resolved: HashMap<ItemId, ItemSignatureResolved>,
    item_bodies: HashMap<ItemId, Vec<Op>>,
    function_data: HashMap<ItemId, FunctionData>,
    const_vals: HashMap<ItemId, Vec<(TypeId, SimulatorValue)>>,
    analyzers: HashMap<ItemId, Analyzer>,

    structs_unresolved: HashMap<ItemId, UnresolvedStruct>,
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
            item_headers: BTreeMap::new(),
            item_signatures_unresolved: HashMap::new(),
            item_signatures_resolved: HashMap::new(),
            item_bodies: HashMap::new(),
            function_data: HashMap::new(),
            const_vals: HashMap::new(),
            analyzers: HashMap::new(),
            structs_unresolved: HashMap::new(),
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
        file: &Path,
        interner: &mut Interners,
        source_store: &mut SourceStorage,
        type_store: &mut TypeStore,
        library_paths: &[PathBuf],
    ) -> Result<ModuleId> {
        let _span = debug_span!(stringify!(Program::load_program)).entered();

        let mut loaded_modules = HashSet::new();
        let mut include_queue = Vec::new();

        let builtin_structs_module_name = interner.intern_lexeme("builtins");
        let builtin_module = self.new_module(builtin_structs_module_name);
        Module::load(
            self,
            builtin_module,
            source_store,
            interner,
            ModuleSource::Builtin(crate::type_store::STRING_DEF),
            &mut include_queue,
        )?;
        loaded_modules.insert(builtin_structs_module_name);

        type_store.update_builtins(&self.structs_unresolved);

        let module_name = Path::new(file).file_stem().and_then(OsStr::to_str).unwrap();
        let module_name = interner.intern_lexeme(module_name);
        let entry_module_id = self.new_module(module_name);

        Module::load(
            self,
            entry_module_id,
            source_store,
            interner,
            ModuleSource::File(file),
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
                ModuleSource::File(&full_path),
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
            .filter(|(_, i)| {
                i.kind() != ItemKind::Macro
                    && i.kind() != ItemKind::Memory
                    && i.kind() != ItemKind::StructDef
            })
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
            .filter(|(_, i)| {
                i.kind() != ItemKind::Macro
                    && i.kind() != ItemKind::Memory
                    && i.kind() != ItemKind::StructDef
            })
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
            .filter(|(_, i)| {
                i.kind() != ItemKind::Macro
                    && i.kind() != ItemKind::Memory
                    && i.kind() != ItemKind::StructDef
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
        self.resolve_struct_defs(interner, source_store, type_store)?;
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

    pub fn new_struct(&mut self, module: ModuleId, def: UnresolvedStruct) {
        let id = self.item_headers.len();
        let id = ItemId(id.to_u16().unwrap());
        let name = def.name;

        let item = ItemHeader {
            name,
            module,
            id,
            kind: ItemKind::StructDef,
            parent: None,
            new_op_id: 0,
        };

        self.item_headers.insert(id, item);
        self.structs_unresolved.insert(id, def);

        let module = self.modules.get_mut(&module).unwrap();
        module.top_level_symbols.insert(name.lexeme, id);
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

#[derive(Debug)]
pub enum ModuleSource<'a> {
    File(&'a Path),
    Builtin(&'static str),
}

impl Module {
    pub fn load(
        program: &mut Program,
        module_id: ModuleId,
        source_store: &mut SourceStorage,
        interner: &mut Interners,
        file: ModuleSource,
        include_queue: &mut Vec<Token>,
    ) -> Result<()> {
        let file_type = format!("{file:?}");
        let _span = debug_span!(stringify!(Module::load), file_type).entered();

        let (file, contents) = match file {
            ModuleSource::File(file) => (
                file,
                std::fs::read_to_string(file)
                    .with_context(|| eyre!("Failed to open file {}", file.display()))?,
            ),
            ModuleSource::Builtin(contents) => (Path::new("builtin"), contents.to_owned()),
        };

        let file_id = source_store.add(file, &contents);

        let tokens = lexer::lex_file(&contents, file_id, interner, source_store)
            .map_err(|_| eyre!("error lexing file: {}", file.display()))?;

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
        .map_err(|_| eyre!("error parsing file: {}", file.display()))?;

        Ok(())
    }

    pub fn get_item_id(&self, name: Spur) -> Option<ItemId> {
        self.top_level_symbols.get(&name).copied()
    }

    pub fn name(&self) -> Spur {
        self.name
    }
}

fn search_includes(paths: &[PathBuf], file_name: &Path) -> Option<PathBuf> {
    // Stupidly innefficient, but whatever...

    for path in paths {
        let path = Path::new(path).join(file_name);
        if path.exists() {
            return Some(path);
        }
    }

    None
}
