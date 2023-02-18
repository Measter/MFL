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
    simulate::{simulate_execute_program, SimulationError},
    source_file::{SourceLocation, SourceStorage},
};

mod parser;
pub mod static_analysis;
use static_analysis::Analyzer;

use self::type_store::{TypeId, TypeKind, TypeStore};
pub mod type_store;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProcedureId(u16);
impl ProcedureId {
    // This is only used during parse failure, so it shouldn't cause problems?
    pub fn dud() -> Self {
        Self(u16::MAX)
    }
}

#[derive(Debug, Default)]
pub struct FunctionData {
    pub allocs: HashMap<Spur, ProcedureId>,
    pub alloc_sizes: HashMap<ProcedureId, usize>,
    pub consts: HashMap<Spur, ProcedureId>,
}

// TODO: Add compile-time asserts
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ProcedureKind {
    Assert,
    Const,
    Macro,
    Memory,
    Function,
}

#[derive(Debug, Clone, Copy)]
pub struct ProcedureHeader {
    name: Token,
    module: ModuleId,
    id: ProcedureId,
    parent: Option<ProcedureId>,
    kind: ProcedureKind,
    new_op_id: u32,
}

impl ProcedureHeader {
    pub fn name(&self) -> Token {
        self.name
    }

    pub fn module(&self) -> ModuleId {
        self.module
    }

    pub fn id(&self) -> ProcedureId {
        self.id
    }

    pub fn parent(&self) -> Option<ProcedureId> {
        self.parent
    }

    pub fn kind(&self) -> ProcedureKind {
        self.kind
    }
}

#[derive(Debug)]
pub struct ProcedureSignatureUnresolved {
    exit_stack: Vec<Token>,
    exit_stack_location: SourceLocation,
    entry_stack: Vec<Token>,
    entry_stack_location: SourceLocation,
}

impl ProcedureSignatureUnresolved {
    pub fn exit_stack(&self) -> &[Token] {
        &self.exit_stack
    }

    pub fn exit_stack_location(&self) -> SourceLocation {
        self.exit_stack_location
    }

    pub fn entry_stack(&self) -> &[Token] {
        &self.entry_stack
    }

    pub fn entry_stack_location(&self) -> SourceLocation {
        self.entry_stack_location
    }
}
pub struct ProcedureSignatureResolved {
    exit_stack: SmallVec<[TypeId; 8]>,
    entry_stack: SmallVec<[TypeId; 8]>,
}

impl ProcedureSignatureResolved {
    pub fn exit_stack(&self) -> &[TypeId] {
        &self.exit_stack
    }

    pub fn entry_stack(&self) -> &[TypeId] {
        &self.entry_stack
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(u16);

pub struct Program {
    type_store: TypeStore,

    modules: HashMap<ModuleId, Module>,
    module_ident_map: HashMap<Spur, ModuleId>,

    procedure_headers: HashMap<ProcedureId, ProcedureHeader>,
    procedure_signatures_unresolved: HashMap<ProcedureId, ProcedureSignatureUnresolved>,
    procedure_signatures_resolved: HashMap<ProcedureId, ProcedureSignatureResolved>,
    procedure_bodies: HashMap<ProcedureId, Vec<Op>>,
    function_data: HashMap<ProcedureId, FunctionData>,
    const_vals: HashMap<ProcedureId, Vec<(TypeId, u64)>>,
    analyzers: HashMap<ProcedureId, Analyzer>,
    global_allocs: HashMap<ProcedureId, usize>,
}

impl Program {
    pub fn get_all_procedures(&self) -> impl Iterator<Item = (ProcedureId, ProcedureHeader)> + '_ {
        self.procedure_headers.iter().map(|(id, proc)| (*id, *proc))
    }

    pub fn get_module(&self, id: ModuleId) -> &Module {
        &self.modules[&id]
    }

    pub fn get_proc_header(&self, id: ProcedureId) -> ProcedureHeader {
        self.procedure_headers[&id]
    }

    pub fn get_proc_header_mut(&mut self, id: ProcedureId) -> &mut ProcedureHeader {
        self.procedure_headers.get_mut(&id).unwrap()
    }

    pub fn get_proc_signature_unresolved(&self, id: ProcedureId) -> &ProcedureSignatureUnresolved {
        &self.procedure_signatures_unresolved[&id]
    }

    #[track_caller]
    pub fn get_proc_signature_resolved(&self, id: ProcedureId) -> &ProcedureSignatureResolved {
        &self.procedure_signatures_resolved[&id]
    }

    pub fn get_proc_body(&self, id: ProcedureId) -> &[Op] {
        &self.procedure_bodies[&id]
    }

    pub fn set_proc_body(&mut self, id: ProcedureId, body: Vec<Op>) {
        self.procedure_bodies.insert(id, body);
    }

    pub fn get_analyzer(&self, id: ProcedureId) -> &Analyzer {
        &self.analyzers[&id]
    }

    pub fn get_type_store(&self) -> &TypeStore {
        &self.type_store
    }

    #[track_caller]
    pub fn get_function_data(&self, id: ProcedureId) -> &FunctionData {
        self.function_data
            .get(&id)
            .expect("ICE: tried to get function data for non-function proc")
    }

    #[track_caller]
    pub fn get_function_data_mut(&mut self, id: ProcedureId) -> &mut FunctionData {
        self.function_data
            .get_mut(&id)
            .expect("ICE: tried to get function data for non-function proc")
    }

    pub fn get_consts(&self, id: ProcedureId) -> Option<&[(TypeId, u64)]> {
        self.const_vals.get(&id).map(|v| &**v)
    }
}

impl Program {
    pub fn new() -> Self {
        Program {
            type_store: TypeStore::new(),
            modules: Default::default(),
            module_ident_map: Default::default(),
            procedure_headers: HashMap::new(),
            procedure_signatures_unresolved: HashMap::new(),
            procedure_signatures_resolved: HashMap::new(),
            procedure_bodies: HashMap::new(),
            function_data: HashMap::new(),
            const_vals: HashMap::new(),
            analyzers: HashMap::new(),
            global_allocs: HashMap::new(),
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
        library_paths: &[String],
    ) -> Result<ModuleId> {
        let _span = debug_span!(stringify!(Program::load_program)).entered();

        self.type_store.init_builtins(interner);

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
            filename.set_extension("porth");

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

        self.post_process_procs(interner, source_store)?;

        Ok(entry_module_id)
    }

    fn resolve_idents_in_block(
        &self,
        proc: ProcedureHeader,
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
                        proc,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut while_op.body_block);
                    while_op.body_block = self.resolve_idents_in_block(
                        proc,
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
                        proc,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut if_op.then_block);
                    if_op.then_block = self.resolve_idents_in_block(
                        proc,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut if_op.else_block);
                    if_op.else_block = self.resolve_idents_in_block(
                        proc,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                }
                // Symbol in own module.
                OpCode::UnresolvedIdent {
                    proc: proc_token,
                    module: None,
                } => {
                    // Obviously a symbol is visible to itself.
                    let visible_id = if proc_token.lexeme == proc.name.lexeme {
                        Some(proc.id())
                    } else {
                        self.get_visible_symbol(proc, proc_token.lexeme)
                    };
                    if let Some(id) = visible_id {
                        op.code = OpCode::ResolvedIdent {
                            module: proc.module,
                            proc_id: id,
                        };
                    } else {
                        let module = &self.modules[&proc.module];
                        let token_lexeme = interner.resolve_lexeme(proc_token.lexeme);
                        let module_lexeme = interner.resolve_lexeme(module.name);
                        *had_error = true;
                        diagnostics::emit_error(
                            proc_token.location,
                            format!(
                                "symbol `{token_lexeme}` not found in module `{module_lexeme}`"
                            ),
                            Some(
                                Label::new(proc_token.location)
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
                    proc: proc_token,
                    module: Some(module_token),
                } => {
                    let module_id = match self.module_ident_map.get(&module_token.lexeme) {
                        Some(id) => *id,
                        None => {
                            let module_name = interner.resolve_lexeme(module_token.lexeme);
                            diagnostics::emit_error(
                                proc_token.location,
                                format!("module `{module_name}` not found"),
                                Some(
                                    Label::new(proc_token.location)
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
                    match module.top_level_symbols.get(&proc_token.lexeme) {
                        Some(proc_id) => {
                            op.code = OpCode::ResolvedIdent {
                                module: module_id,
                                proc_id: *proc_id,
                            };
                        }
                        None => {
                            let proc_name = interner.resolve_lexeme(proc_token.lexeme);
                            let module_name = interner.resolve_lexeme(module_token.lexeme);
                            diagnostics::emit_error(
                                proc_token.location,
                                format!("symbol `{proc_name}` not found in module `{module_name}`"),
                                Some(
                                    Label::new(proc_token.location)
                                        .with_color(Color::Red)
                                        .with_message("not found"),
                                ),
                                None,
                                source_store,
                            );
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
        let procs: Vec<_> = self
            .procedure_headers
            .iter()
            .map(|(id, proc)| (*id, *proc))
            .collect();

        for (proc_id, proc) in procs {
            trace!(name = interner.get_symbol_name(self, proc_id));
            let body = self.procedure_bodies.remove(&proc_id).unwrap();

            self.procedure_bodies.insert(
                proc_id,
                self.resolve_idents_in_block(proc, body, &mut had_error, interner, source_store),
            );
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error during ident resolation"))
    }

    fn resolve_types_in_block(
        &self,
        mut body: Vec<Op>,
        had_error: &mut bool,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Vec<Op> {
        for op in &mut body {
            match &mut op.code {
                OpCode::While(while_op) => {
                    let temp_body = std::mem::take(&mut while_op.condition);
                    while_op.condition =
                        self.resolve_types_in_block(temp_body, had_error, interner, source_store);
                    let temp_body = std::mem::take(&mut while_op.body_block);
                    while_op.body_block =
                        self.resolve_types_in_block(temp_body, had_error, interner, source_store);
                }
                OpCode::If(if_op) => {
                    // Mmmm.. repetition...
                    let temp_body = std::mem::take(&mut if_op.condition);
                    if_op.condition =
                        self.resolve_types_in_block(temp_body, had_error, interner, source_store);
                    let temp_body = std::mem::take(&mut if_op.then_block);
                    if_op.then_block =
                        self.resolve_types_in_block(temp_body, had_error, interner, source_store);
                    let temp_body = std::mem::take(&mut if_op.else_block);
                    if_op.else_block =
                        self.resolve_types_in_block(temp_body, had_error, interner, source_store);
                }

                OpCode::UnresolvedCast { kind_token } => {
                    let Some(type_info) = self.type_store.resolve_type(kind_token.lexeme) else {
                        type_store::emit_type_error_diag(*kind_token, interner, source_store);
                        *had_error = true;
                        continue;
                    };

                    op.code = OpCode::ResolvedCast { id: type_info.id };
                }
                OpCode::UnresolvedLoad { kind_token } => {
                    let Some(type_info) = self.type_store.resolve_type(kind_token.lexeme) else {
                        type_store::emit_type_error_diag(*kind_token, interner, source_store);
                        *had_error = true;
                        continue;
                    };

                    op.code = OpCode::ResolvedLoad { id: type_info.id };
                }
                OpCode::UnresolvedStore { kind_token } => {
                    let Some(type_info) = self.type_store.resolve_type(kind_token.lexeme) else {
                        type_store::emit_type_error_diag(*kind_token, interner, source_store);
                        *had_error = true;
                        continue;
                    };

                    op.code = OpCode::ResolvedStore { id: type_info.id };
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
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::resolve_types)).entered();
        let mut had_error = false;

        for (proc_id, proc) in self.procedure_headers.iter().map(|(id, proc)| (*id, *proc)) {
            trace!(name = interner.get_symbol_name(self, proc_id));

            let unresolved_sig = &self.procedure_signatures_unresolved[&proc_id];

            let mut resolved_entry = SmallVec::with_capacity(unresolved_sig.entry_stack.len());
            let mut resolved_exit = SmallVec::with_capacity(unresolved_sig.exit_stack.len());

            if proc.kind == ProcedureKind::Memory {
                resolved_exit.push(
                    self.type_store
                        .get_builtin(type_store::BuiltinTypes::U64)
                        .id,
                );
            } else {
                for input_sig in unresolved_sig.entry_stack() {
                    let Some(info) = self.type_store.resolve_type(input_sig.lexeme) else {
                    type_store::emit_type_error_diag(*input_sig, interner, source_store);
                    had_error = true;
                    continue;
                };
                    resolved_entry.push(info.id);
                }

                for input_sig in unresolved_sig.exit_stack() {
                    let Some(info) = self.type_store.resolve_type(input_sig.lexeme) else {
                    type_store::emit_type_error_diag(*input_sig, interner, source_store);
                    had_error = true;
                    continue;
                };
                    resolved_exit.push(info.id);
                }
            }

            self.procedure_signatures_resolved.insert(
                proc_id,
                ProcedureSignatureResolved {
                    entry_stack: resolved_entry,
                    exit_stack: resolved_exit,
                },
            );

            let body = self.procedure_bodies.remove(&proc_id).unwrap();
            self.procedure_bodies.insert(
                proc_id,
                self.resolve_types_in_block(body, &mut had_error, interner, source_store),
            );
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error during type resolution"))
    }

    fn expand_macros_in_block(
        &self,
        block: &mut Vec<Op>,
        id: ProcedureId,
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
                OpCode::ResolvedIdent { proc_id, .. } if proc_id != id => {
                    let found_proc = self.procedure_headers[&proc_id];
                    if found_proc.kind() == ProcedureKind::Macro {
                        let token = block[i].token;
                        let expansions = block[i].expansions.clone();
                        let new_ops = self.get_proc_body(proc_id).iter().map(|new_op| {
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
        let non_macro_procs: Vec<_> = self
            .procedure_headers
            .iter()
            .filter(|(_, p)| p.kind() != ProcedureKind::Macro)
            .map(|(id, proc)| (*id, *proc))
            .collect();

        for (proc_id, proc) in non_macro_procs {
            trace!(name = interner.get_symbol_name(self, proc_id));
            let mut new_op_id = proc.new_op_id;

            let mut op_id_gen = || {
                let id = new_op_id;
                new_op_id += 1;
                OpId(id)
            };

            let mut body = self.procedure_bodies.remove(&proc_id).unwrap();
            self.expand_macros_in_block(&mut body, proc_id, &mut op_id_gen);
            self.procedure_bodies.insert(proc_id, body);
        }
    }

    fn check_invalid_cyclic_refs_in_block(
        &self,
        own_proc: ProcedureHeader,
        block: &[Op],
        cur_proc: ProcedureHeader,
        kind: &str,
        already_checked: &mut HashSet<ProcedureId>,
        check_queue: &mut Vec<ProcedureHeader>,
        had_error: &mut bool,
        source_store: &SourceStorage,
    ) {
        for op in block {
            match op.code {
                OpCode::While(ref while_op) => {
                    self.check_invalid_cyclic_refs_in_block(
                        own_proc,
                        &while_op.condition,
                        cur_proc,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        own_proc,
                        &while_op.body_block,
                        cur_proc,
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
                        own_proc,
                        &if_op.condition,
                        cur_proc,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        own_proc,
                        &if_op.then_block,
                        cur_proc,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        own_proc,
                        &if_op.else_block,
                        cur_proc,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                }
                OpCode::ResolvedIdent { proc_id, .. } => {
                    // False means that there was already a value in the set with this proc_id
                    #[allow(clippy::bool_comparison)]
                    if already_checked.insert(proc_id) == false {
                        continue;
                    }

                    if proc_id == own_proc.id() {
                        *had_error = true;
                        diagnostics::emit_error(
                            cur_proc.name.location,
                            format!("cyclic {kind} detected"),
                            [
                                Label::new(own_proc.name.location)
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
                        check_queue.push(self.get_proc_header(proc_id));
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
        for own_proc in self.procedure_headers.values().copied() {
            trace!(name = interner.get_symbol_name(self, own_proc.id()));

            let kind = match own_proc.kind() {
                ProcedureKind::Const => "const",
                ProcedureKind::Macro => "macro",
                ProcedureKind::Assert => "assert",
                ProcedureKind::Memory | ProcedureKind::Function => continue,
            };

            check_queue.clear();
            check_queue.push(own_proc);
            already_checked.clear();

            while let Some(proc) = check_queue.pop() {
                self.check_invalid_cyclic_refs_in_block(
                    own_proc,
                    &self.procedure_bodies[&proc.id],
                    proc,
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

    fn analyze_data_flow(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::analyze_data_flow)).entered();
        let mut had_error = false;
        let procs: Vec<_> = self
            .procedure_headers
            .iter()
            .filter(|(_, p)| p.kind() != ProcedureKind::Macro)
            .map(|(id, _)| *id)
            .collect();

        for id in procs {
            let _span = trace_span!(
                "Analyzing procedure",
                name = interner.get_symbol_name(self, id)
            )
            .entered();
            let mut analyzer = Analyzer::default();
            let mut local_error = false;
            local_error |= static_analysis::data_flow_analysis(
                self,
                id,
                &mut analyzer,
                interner,
                source_store,
            )
            .is_err();

            if !local_error {
                local_error |=
                    static_analysis::type_check(self, id, &mut analyzer, interner, source_store)
                        .is_err();
            }

            if !local_error {
                local_error |= static_analysis::const_propagation(
                    self,
                    id,
                    &mut analyzer,
                    interner,
                    source_store,
                )
                .is_err();
            }

            self.analyzers.insert(id, analyzer);
            had_error |= local_error;
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("data analysis error"))
    }

    fn evaluate_const_procs(
        &mut self,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::evaluate_const_procs)).entered();
        let mut had_error = false;

        let mut const_queue: Vec<_> = self
            .procedure_headers
            .iter()
            .filter(|(_, proc)| proc.kind() == ProcedureKind::Const)
            .map(|(id, _)| *id)
            .collect();
        let mut next_run_queue = Vec::with_capacity(const_queue.len());

        loop {
            for const_id in const_queue.drain(..) {
                let proc_sig = self.get_proc_signature_resolved(const_id);
                match simulate_execute_program(self, const_id, interner, source_store) {
                    Ok(stack) => {
                        let const_vals = stack
                            .into_iter()
                            .zip(&proc_sig.exit_stack)
                            .map(|(val, ty)| (*ty, val))
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
        own_proc_id: ProcedureId,
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
                                own_proc_id,
                                while_op.condition,
                                had_error,
                                interner,
                                source_store,
                            ),
                            body_block: self.process_idents_in_block(
                                own_proc_id,
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
                        own_proc_id,
                        if_op.condition,
                        had_error,
                        interner,
                        source_store,
                    );
                    let new_then_block = self.process_idents_in_block(
                        own_proc_id,
                        if_op.then_block,
                        had_error,
                        interner,
                        source_store,
                    );
                    let new_else_block = self.process_idents_in_block(
                        own_proc_id,
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

                OpCode::ResolvedIdent { module, proc_id } => {
                    let found_proc = self.procedure_headers[&proc_id];

                    match found_proc.kind() {
                        ProcedureKind::Const => {
                            let Some(vals) = self.const_vals.get( &found_proc.id ) else {
                                let own_proc = self.procedure_headers[&own_proc_id];
                                let name = interner.resolve_lexeme(own_proc.name.lexeme);
                                panic!("ICE: Encountered un-evaluated const during ident processing {name}");
                            };
                            for (kind, val) in vals {
                                let type_info = self.type_store.get_type_info(*kind);
                                let (code, const_val) = match type_info.kind {
                                    TypeKind::Integer(width) => (
                                        OpCode::PushInt { width, value: *val },
                                        ConstVal::Int(*val),
                                    ),
                                    TypeKind::Bool => {
                                        (OpCode::PushBool(*val != 0), ConstVal::Bool(*val != 0))
                                    }
                                    TypeKind::Pointer => {
                                        panic!("ICE: Const pointers not supported")
                                    }
                                };
                                new_ops.push(Op {
                                    code,
                                    id: op.id,
                                    token: op.token,
                                    expansions: op.expansions.clone(),
                                });

                                let analyzer = self.analyzers.get_mut(&own_proc_id).unwrap();
                                let op_io = analyzer.get_op_io(op.id);
                                let out_id = op_io.outputs()[0];
                                analyzer.set_value_const(out_id, const_val);
                            }
                        }
                        ProcedureKind::Memory => {
                            new_ops.push(Op {
                                code: OpCode::Memory {
                                    module_id: module,
                                    proc_id,
                                    offset: 0,
                                    global: found_proc.parent().is_none(),
                                },
                                id: op.id,
                                token: op.token,
                                expansions: op.expansions,
                            });
                        }
                        ProcedureKind::Function => {
                            new_ops.push(Op {
                                code: OpCode::CallProc { module, proc_id },
                                id: op.id,
                                token: op.token,
                                expansions: op.expansions,
                            });
                        }
                        ProcedureKind::Macro => {
                            let own_proc = self.procedure_headers[&own_proc_id];
                            let name = interner.resolve_lexeme(own_proc.name.lexeme);
                            panic!(
                                "ICE: Encountered assert, or macro during ident processing {name}"
                            );
                        }

                        ProcedureKind::Assert => {
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
        let all_proc_ids: Vec<_> = self
            .procedure_headers
            .iter()
            .filter(|(_, p)| p.kind() != ProcedureKind::Macro)
            .map(|(id, _)| *id)
            .collect();

        for own_proc_id in all_proc_ids {
            trace!("Processing {}", interner.get_symbol_name(self, own_proc_id));

            let old_body = self.procedure_bodies.remove(&own_proc_id).unwrap();
            let new_body = self.process_idents_in_block(
                own_proc_id,
                old_body,
                &mut had_error,
                interner,
                source_store,
            );
            self.procedure_bodies.insert(own_proc_id, new_body);
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error processing idents"))
    }

    fn evaluate_allocation_sizes(
        &mut self,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::evaluate_allocation_sizes)).entered();
        let mut had_error = false;

        let all_mem_procs: Vec<_> = self
            .procedure_headers
            .iter()
            .filter(|(_, p)| p.kind() == ProcedureKind::Memory)
            .map(|(id, proc)| (*id, *proc))
            .collect();

        for (proc_id, proc) in all_mem_procs {
            let mut stack = match simulate_execute_program(self, proc_id, interner, source_store) {
                Ok(stack) => stack,
                Err(_) => {
                    had_error = true;
                    continue;
                }
            };

            // The type checker ensures a single stack item.
            let alloc_size = stack.pop().unwrap().to_usize();

            match proc.parent {
                // If we have a parent, it means it's a local allocation.
                Some(parent_id) => {
                    let function_data = self.function_data.get_mut(&parent_id).unwrap();
                    function_data.alloc_sizes.insert(proc_id, alloc_size);
                }

                // If not, this is global, and needs to be placed in the program.
                // Less work needs doing here as global allocs are always referenced by name.
                None => {
                    self.global_allocs.insert(proc_id, alloc_size);
                }
            }
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("allocation size evaluation failed"))
    }

    fn check_asserts(&self, interner: &Interners, source_store: &SourceStorage) -> Result<()> {
        let _span = debug_span!(stringify!(Program::check_asserts)).entered();
        let mut had_error = false;

        for (&id, &proc) in self.procedure_headers.iter() {
            if proc.kind() != ProcedureKind::Memory {
                continue;
            }

            let assert_result = match simulate_execute_program(self, id, interner, source_store) {
                // Type check says we'll have a value at this point.
                Ok(mut stack) => stack.pop().unwrap() != 0,
                Err(_) => {
                    had_error = true;
                    continue;
                }
            };

            if !assert_result {
                diagnostics::emit_error(
                    proc.name.location,
                    "assert failure",
                    Some(
                        Label::new(proc.name.location)
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

    fn post_process_procs(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::post_process_procs)).entered();
        self.resolve_idents(interner, source_store)?;
        self.resolve_types(interner, source_store)?;

        self.check_invalid_cyclic_refs(interner, source_store)?;
        self.expand_macros(interner);

        self.analyze_data_flow(interner, source_store)?;
        self.evaluate_const_procs(interner, source_store)?;

        self.process_idents(interner, source_store)?;
        self.evaluate_allocation_sizes(interner, source_store)?;
        self.check_asserts(interner, source_store)?;

        Ok(())
    }

    pub fn new_procedure(
        &mut self,
        name: Token,
        module: ModuleId,
        kind: ProcedureKind,
        parent: Option<ProcedureId>,
        exit_stack: Vec<Token>,
        exit_stack_location: SourceLocation,
        entry_stack: Vec<Token>,
        entry_stack_location: SourceLocation,
    ) -> ProcedureId {
        let id = self.procedure_headers.len();
        let id = ProcedureId(id.to_u16().unwrap());

        let proc = ProcedureHeader {
            name,
            module,
            id,
            kind,
            parent,
            new_op_id: 0,
        };

        let sig = ProcedureSignatureUnresolved {
            exit_stack,
            exit_stack_location,
            entry_stack,
            entry_stack_location,
        };

        self.procedure_headers.insert(id, proc);
        self.procedure_signatures_unresolved.insert(id, sig);

        if kind == ProcedureKind::Function {
            self.function_data.insert(id, FunctionData::default());
        }

        if parent.is_none() {
            let module = self.modules.get_mut(&module).unwrap();
            module.top_level_symbols.insert(name.lexeme, id);
        }

        id
    }

    pub fn get_visible_symbol(&self, from: ProcedureHeader, symbol: Spur) -> Option<ProcedureId> {
        if from.name.lexeme == symbol {
            return Some(from.id);
        }

        // Check our own children.
        if from.kind == ProcedureKind::Function {
            let fd = self.get_function_data(from.id);
            if let Some(found_id) = fd.allocs.get(&symbol).or_else(|| fd.consts.get(&symbol)) {
                return Some(*found_id);
            }
        }

        // Check our parent's children.
        let mut cur_id = from.parent;
        while let Some(id) = cur_id {
            let proc = self.get_proc_header(id);

            if proc.name.lexeme == symbol {
                return Some(proc.id);
            }

            if proc.kind == ProcedureKind::Function {
                let fd = self.get_function_data(proc.id);
                if let Some(found_id) = fd.allocs.get(&symbol).or_else(|| fd.consts.get(&symbol)) {
                    return Some(*found_id);
                }
            }
            cur_id = proc.parent;
        }

        let module = &self.modules[&from.module];
        module.top_level_symbols.get(&symbol).copied()
    }
}

pub struct Module {
    name: Spur,
    top_level_symbols: HashMap<Spur, ProcedureId>,
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

    pub fn get_proc_id(&self, name: Spur) -> Option<ProcedureId> {
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
