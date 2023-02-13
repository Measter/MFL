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
use tracing::{debug, debug_span, trace, trace_span};
use variantly::Variantly;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{self, Token},
    opcode::{ConditionalBlock, Op, OpCode, OpId},
    program::static_analysis::ConstVal,
    simulate::{simulate_execute_program, SimulationError},
    source_file::{SourceLocation, SourceStorage},
};

mod parser;
pub mod static_analysis;
use static_analysis::{Analyzer, PorthType, PorthTypeKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProcedureId(u16);

#[derive(Debug, Default)]
pub struct FunctionData {
    pub allocs: HashMap<Spur, ProcedureId>,
    pub alloc_sizes: HashMap<ProcedureId, usize>,
    pub consts: HashMap<Spur, ProcedureId>,
}

// TODO: Add compile-time asserts
#[derive(Debug, Variantly)]
pub enum ProcedureKind {
    Assert,
    Const {
        const_val: Option<Vec<(PorthTypeKind, u64)>>,
    },
    Macro,
    Memory,
    Function(FunctionData),
}

impl ProcedureKind {
    pub fn get_proc_data(&self) -> &FunctionData {
        match self {
            ProcedureKind::Function(data) => data,
            _ => panic!("ICE: called get_proc_data on a non-proc"),
        }
    }

    pub fn get_proc_data_mut(&mut self) -> &mut FunctionData {
        match self {
            ProcedureKind::Function(data) => data,
            _ => panic!("ICE: called get_proc_data on a non-proc"),
        }
    }
}

#[derive(Debug)]
pub struct Procedure {
    name: Token,
    module: ModuleId,
    id: ProcedureId,
    parent: Option<ProcedureId>,
    kind: ProcedureKind,
    new_op_id: usize,

    body: Vec<Op>,
    exit_stack: Vec<PorthType>,
    exit_stack_location: SourceLocation,
    entry_stack: Vec<PorthType>,
    entry_stack_location: SourceLocation,
}

impl Procedure {
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

    pub fn body(&self) -> &[Op] {
        &self.body
    }

    pub fn body_mut(&mut self) -> &mut Vec<Op> {
        &mut self.body
    }

    pub fn kind(&self) -> &ProcedureKind {
        &self.kind
    }

    pub fn kind_mut(&mut self) -> &mut ProcedureKind {
        &mut self.kind
    }

    pub fn exit_stack(&self) -> &[PorthType] {
        &self.exit_stack
    }

    pub fn exit_stack_location(&self) -> SourceLocation {
        self.exit_stack_location
    }

    pub fn entry_stack(&self) -> &[PorthType] {
        &self.entry_stack
    }

    pub fn entry_stack_location(&self) -> SourceLocation {
        self.entry_stack_location
    }

    fn expand_macros_in_block(
        block: &mut Vec<Op>,
        id: ProcedureId,
        new_op_id: &mut impl FnMut() -> OpId,
        program: &Program,
    ) {
        let mut i = 0;
        while i < block.len() {
            match block[i].code {
                OpCode::While {
                    body: ref mut while_block,
                } => {
                    Self::expand_macros_in_block(
                        &mut while_block.condition,
                        id,
                        new_op_id,
                        program,
                    );
                    Self::expand_macros_in_block(&mut while_block.block, id, new_op_id, program);
                }
                OpCode::If {
                    ref mut condition,
                    ref mut else_block,
                    ..
                } => {
                    Self::expand_macros_in_block(&mut condition.condition, id, new_op_id, program);
                    Self::expand_macros_in_block(&mut condition.block, id, new_op_id, program);
                    Self::expand_macros_in_block(else_block, id, new_op_id, program);
                }
                OpCode::ResolvedIdent { proc_id, .. } if proc_id != id => {
                    let found_proc = program.get_proc(proc_id);
                    if found_proc.kind().is_macro() {
                        let token = block[i].token;
                        let expansions = block[i].expansions.clone();
                        let new_ops = found_proc.body().iter().map(|new_op| {
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

    fn expand_macros(&mut self, program: &Program) {
        let mut op_id_gen = || {
            let id = self.new_op_id;
            self.new_op_id += 1;
            OpId(id)
        };
        Self::expand_macros_in_block(&mut self.body, self.id, &mut op_id_gen, program);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(u16);

pub struct Program {
    modules: HashMap<ModuleId, Module>,
    module_ident_map: HashMap<Spur, ModuleId>,

    procedure_headers: HashMap<ProcedureId, Procedure>,
    analyzers: HashMap<ProcedureId, Analyzer>,
    global_allocs: HashMap<ProcedureId, usize>,
}

impl Program {
    pub fn get_all_procedures(&self) -> impl Iterator<Item = (ProcedureId, &Procedure)> {
        self.procedure_headers.iter().map(|(id, proc)| (*id, proc))
    }

    pub fn get_module(&self, id: ModuleId) -> &Module {
        &self.modules[&id]
    }

    pub fn get_proc(&self, id: ProcedureId) -> &Procedure {
        &self.procedure_headers[&id]
    }

    pub fn get_proc_mut(&mut self, id: ProcedureId) -> &mut Procedure {
        self.procedure_headers.get_mut(&id).unwrap()
    }

    pub fn get_analyzer(&self, id: ProcedureId) -> &Analyzer {
        &self.analyzers[&id]
    }
}

impl Program {
    pub fn new() -> Self {
        Program {
            modules: Default::default(),
            module_ident_map: Default::default(),
            procedure_headers: HashMap::new(),
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
        proc: &Procedure,
        mut body: Vec<Op>,
        had_error: &mut bool,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Vec<Op> {
        for op in &mut body {
            match &mut op.code {
                OpCode::While { body: while_body } => {
                    let temp_body = std::mem::take(&mut while_body.condition);
                    while_body.condition = self.resolve_idents_in_block(
                        proc,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut while_body.block);
                    while_body.block = self.resolve_idents_in_block(
                        proc,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                }
                OpCode::If {
                    condition,
                    else_block,
                    ..
                } => {
                    // Mmmm.. repetition...
                    let temp_body = std::mem::take(&mut condition.condition);
                    condition.condition = self.resolve_idents_in_block(
                        proc,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut condition.block);
                    condition.block = self.resolve_idents_in_block(
                        proc,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(else_block);
                    *else_block = self.resolve_idents_in_block(
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
        let proc_ids: Vec<_> = self.procedure_headers.keys().copied().collect();

        for proc_id in proc_ids {
            trace!(name = interner.get_symbol_name(self, proc_id));
            let mut proc = self.procedure_headers.remove(&proc_id).unwrap();
            let body = std::mem::take(&mut proc.body);

            proc.body =
                self.resolve_idents_in_block(&proc, body, &mut had_error, interner, source_store);
            self.procedure_headers.insert(proc_id, proc);
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error during ident resolation"))
    }

    fn expand_macros(&mut self, interner: &mut Interners) {
        let _span = debug_span!(stringify!(Program::expand_macros)).entered();
        debug!("");
        let non_macro_proc_ids: Vec<_> = self
            .procedure_headers
            .iter()
            .filter(|(_, p)| !p.kind().is_macro())
            .map(|(id, _)| *id)
            .collect();

        for proc_id in non_macro_proc_ids {
            trace!(name = interner.get_symbol_name(self, proc_id));
            let mut proc = self.procedure_headers.remove(&proc_id).unwrap();

            proc.expand_macros(self);

            self.procedure_headers.insert(proc_id, proc);
        }
    }

    fn check_invalid_cyclic_refs_in_block<'a>(
        &'a self,
        own_proc: &Procedure,
        block: &[Op],
        cur_proc: &Procedure,
        kind: &str,
        already_checked: &mut HashSet<ProcedureId>,
        check_queue: &mut Vec<&'a Procedure>,
        had_error: &mut bool,
        source_store: &SourceStorage,
    ) {
        for op in block {
            match op.code {
                OpCode::While {
                    body: ref while_body,
                    ..
                } => {
                    self.check_invalid_cyclic_refs_in_block(
                        own_proc,
                        &while_body.condition,
                        cur_proc,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        own_proc,
                        &while_body.block,
                        cur_proc,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    //
                }
                OpCode::If {
                    ref condition,
                    ref else_block,
                    ..
                } => {
                    self.check_invalid_cyclic_refs_in_block(
                        own_proc,
                        &condition.block,
                        cur_proc,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        own_proc,
                        else_block,
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
                        check_queue.push(self.get_proc(proc_id));
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
        for own_proc in self.procedure_headers.values() {
            trace!(name = interner.get_symbol_name(self, own_proc.id()));

            let kind = match own_proc.kind() {
                ProcedureKind::Const { .. } => "const",
                ProcedureKind::Macro => "macro",
                ProcedureKind::Assert => "assert",
                ProcedureKind::Memory | ProcedureKind::Function(_) => continue,
            };

            check_queue.clear();
            check_queue.push(own_proc);
            already_checked.clear();

            while let Some(proc) = check_queue.pop() {
                self.check_invalid_cyclic_refs_in_block(
                    own_proc,
                    proc.body(),
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
        let proc_ids: Vec<_> = self
            .procedure_headers
            .iter()
            .filter(|(_, p)| !p.kind().is_macro())
            .map(|(id, _)| *id)
            .collect();

        for id in proc_ids {
            let _span = trace_span!(
                "Analyzing procedure",
                name = interner.get_symbol_name(self, id)
            )
            .entered();
            let mut analyzer = Analyzer::default();
            let mut local_error = false;
            let proc = &self.procedure_headers[&id];
            local_error |= static_analysis::data_flow_analysis(
                self,
                proc,
                &mut analyzer,
                interner,
                source_store,
            )
            .is_err();

            if !local_error {
                local_error |=
                    static_analysis::type_check(self, proc, &mut analyzer, interner, source_store)
                        .is_err();
            }

            if !local_error {
                local_error |= static_analysis::const_propagation(
                    self,
                    proc,
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
            .filter(|(_, proc)| proc.kind().is_const())
            .map(|(id, _)| *id)
            .collect();
        let mut next_run_queue = Vec::with_capacity(const_queue.len());

        if had_error {
            return Err(eyre!("const jump label create failed"));
        }

        loop {
            for const_id in const_queue.drain(..) {
                let proc = self.get_proc(const_id);
                match simulate_execute_program(self, proc, interner, source_store) {
                    Ok(stack) => {
                        let const_vals = stack
                            .into_iter()
                            .zip(&proc.exit_stack)
                            .map(|(val, ty)| (ty.kind, val))
                            .collect();

                        match &mut self.get_proc_mut(const_id).kind {
                            ProcedureKind::Const { const_val } => {
                                *const_val = Some(const_vals);
                            }
                            _ => unreachable!(),
                        }
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
        own_proc: &Procedure,
        block: Vec<Op>,
        had_error: &mut bool,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Vec<Op> {
        let mut new_ops: Vec<Op> = Vec::with_capacity(block.len());
        for op in block {
            match op.code {
                OpCode::While { body: while_body } => {
                    new_ops.push(Op {
                        code: OpCode::While {
                            body: ConditionalBlock {
                                condition: self.process_idents_in_block(
                                    own_proc,
                                    while_body.condition,
                                    had_error,
                                    interner,
                                    source_store,
                                ),
                                block: self.process_idents_in_block(
                                    own_proc,
                                    while_body.block,
                                    had_error,
                                    interner,
                                    source_store,
                                ),
                                ..while_body
                            },
                        },
                        id: op.id,
                        token: op.token,
                        expansions: op.expansions,
                    });
                }
                OpCode::If {
                    open_token,
                    condition,
                    else_block,
                    end_token,
                } => {
                    let new_main = ConditionalBlock {
                        condition: self.process_idents_in_block(
                            own_proc,
                            condition.condition,
                            had_error,
                            interner,
                            source_store,
                        ),
                        block: self.process_idents_in_block(
                            own_proc,
                            condition.block,
                            had_error,
                            interner,
                            source_store,
                        ),
                        ..condition
                    };

                    let new_else = self.process_idents_in_block(
                        own_proc,
                        else_block,
                        had_error,
                        interner,
                        source_store,
                    );

                    new_ops.push(Op {
                        code: OpCode::If {
                            condition: new_main,
                            else_block: new_else,
                            open_token,
                            end_token,
                        },
                        id: op.id,
                        token: op.token,
                        expansions: op.expansions,
                    });
                }

                OpCode::ResolvedIdent { module, proc_id } => {
                    let found_proc = if proc_id == own_proc.id() {
                        own_proc
                    } else {
                        &self.procedure_headers[&proc_id]
                    };

                    match found_proc.kind() {
                        ProcedureKind::Const {
                            const_val: Some(vals),
                        } => {
                            for (kind, val) in vals {
                                let (code, const_val) = match kind {
                                    PorthTypeKind::Int(width) => (
                                        OpCode::PushInt {
                                            width: *width,
                                            value: *val,
                                        },
                                        ConstVal::Int(*val),
                                    ),
                                    PorthTypeKind::Bool => {
                                        (OpCode::PushBool(*val != 0), ConstVal::Bool(*val != 0))
                                    }
                                    PorthTypeKind::Ptr => {
                                        panic!("ICE: Const pointers not supported")
                                    }
                                };
                                new_ops.push(Op {
                                    code,
                                    id: op.id,
                                    token: op.token,
                                    expansions: op.expansions.clone(),
                                });

                                let analyzer = self.analyzers.get_mut(&own_proc.id).unwrap();
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
                        ProcedureKind::Function(_) => {
                            new_ops.push(Op {
                                code: OpCode::CallProc { module, proc_id },
                                id: op.id,
                                token: op.token,
                                expansions: op.expansions,
                            });
                        }
                        ProcedureKind::Const { const_val: None } | ProcedureKind::Macro => {
                            let name = interner.resolve_lexeme(own_proc.name.lexeme);
                            panic!("ICE: Encountered assert, macro or un-evaluated const during ident processing {name}");
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
            .filter(|(_, p)| !p.kind().is_macro())
            .map(|(id, _)| *id)
            .collect();

        for own_proc_id in all_proc_ids {
            trace!(
                "      Processing {}",
                interner.get_symbol_name(self, own_proc_id)
            );
            let mut proc = self.procedure_headers.remove(&own_proc_id).unwrap();

            let old_body = std::mem::take(&mut proc.body);
            proc.body = self.process_idents_in_block(
                &proc,
                old_body,
                &mut had_error,
                interner,
                source_store,
            );

            self.procedure_headers.insert(own_proc_id, proc);
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

        let all_mem_proc_ids: Vec<_> = self
            .procedure_headers
            .iter()
            .filter(|(_, p)| p.kind().is_memory())
            .map(|(id, _)| *id)
            .collect();

        for proc_id in all_mem_proc_ids {
            let proc = self.procedure_headers.remove(&proc_id).unwrap();

            let mut stack = match simulate_execute_program(self, &proc, interner, source_store) {
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
                    let parent_proc = self.get_proc_mut(parent_id);
                    let function_data = parent_proc.kind.get_proc_data_mut();

                    function_data.alloc_sizes.insert(proc_id, alloc_size);
                }

                // If not, this is global, and needs to be placed in the program.
                // Less work needs doing here as global allocs are always referenced by name.
                None => {
                    self.global_allocs.insert(proc_id, alloc_size);
                }
            }

            self.procedure_headers.insert(proc_id, proc);
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("allocation size evaluation failed"))
    }

    fn check_asserts(&self, interner: &Interners, source_store: &SourceStorage) -> Result<()> {
        let _span = debug_span!(stringify!(Program::check_asserts)).entered();
        let mut had_error = false;

        for proc in self.procedure_headers.values() {
            if !proc.kind().is_assert() {
                continue;
            }

            let assert_result = match simulate_execute_program(self, proc, interner, source_store) {
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
        debug!("");
        self.resolve_idents(interner, source_store)?;

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
        exit_stack: Vec<PorthType>,
        exit_stack_location: SourceLocation,
        entry_stack: Vec<PorthType>,
        entry_stack_location: SourceLocation,
    ) -> ProcedureId {
        let id = self.procedure_headers.len();
        let id = ProcedureId(id.to_u16().unwrap());

        let proc = Procedure {
            name,
            module,
            id,
            kind,
            body: Vec::new(),
            parent,
            new_op_id: 0,
            exit_stack,
            exit_stack_location,
            entry_stack,
            entry_stack_location,
        };

        self.procedure_headers.insert(id, proc);

        if parent.is_none() {
            let module = self.modules.get_mut(&module).unwrap();
            module.top_level_symbols.insert(name.lexeme, id);
        }

        id
    }

    pub fn get_visible_symbol(&self, from: &Procedure, symbol: Spur) -> Option<ProcedureId> {
        if from.name.lexeme == symbol {
            return Some(from.id);
        }

        // Check our own children.
        if let ProcedureKind::Function(FunctionData { allocs, consts, .. }) = &from.kind {
            if let Some(found_id) = allocs.get(&symbol).or_else(|| consts.get(&symbol)) {
                return Some(*found_id);
            }
        }

        // Check our parent's children.
        let mut cur_id = from.parent;
        while let Some(id) = cur_id {
            let proc = self.get_proc(id);

            if proc.name.lexeme == symbol {
                return Some(proc.id);
            }

            if let ProcedureKind::Function(FunctionData { allocs, consts, .. }) = &proc.kind {
                if let Some(found_id) = allocs.get(&symbol).or_else(|| consts.get(&symbol)) {
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
