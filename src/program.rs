use std::{
    collections::{HashMap, HashSet},
    ffi::OsStr,
    ops::Not,
    path::Path,
};

use ariadne::{Color, Label};
use color_eyre::eyre::{eyre, Context, Result};
use lasso::Spur;
use variantly::Variantly;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::{self, Token},
    opcode::{self, Op, OpCode},
    simulate::{simulate_execute_program, SimulationError},
    source_file::SourceStorage,
    type_check::{self, PorthType, PorthTypeKind},
    OPT_OPCODE,
};

mod parser;

#[derive(Debug, Clone, Copy)]
pub struct AllocData {
    pub size: usize,
    pub offset: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProcedureId(usize);

#[derive(Debug, Default)]
pub struct FunctionData {
    pub allocs: HashMap<Spur, ProcedureId>,
    pub alloc_size_and_offsets: HashMap<Spur, AllocData>,
    pub total_alloc_size: usize,
    pub consts: HashMap<Spur, ProcedureId>,
}

#[derive(Debug, Variantly)]
pub enum ProcedureKind {
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
}

#[derive(Debug)]
pub struct Procedure {
    name: Token,
    module: ModuleId,
    id: ProcedureId,
    parent: Option<ProcedureId>,
    kind: ProcedureKind,

    body: Vec<Op>,
    exit_stack: Vec<PorthType>,
    entry_stack: Vec<PorthType>,
    visible_symbols: HashMap<Spur, ProcedureId>,
}

impl Procedure {
    pub fn name(&self) -> Token {
        self.name
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

    pub fn entry_stack(&self) -> &[PorthType] {
        &self.entry_stack
    }

    pub fn get_visible_symbol(&self, symbol: Spur) -> Option<ProcedureId> {
        self.visible_symbols.get(&symbol).copied()
    }

    fn expand_macros(
        &mut self,
        program: &Program,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let mut src_ops = std::mem::take(&mut self.body);
        let mut dst_ops = Vec::with_capacity(self.body.len());
        let mut had_error = false;

        let mut num_expansions = 0;
        let mut last_changed_macros = Vec::new();

        loop {
            let mut expanded_macro = false;

            for op in src_ops.drain(..) {
                let (module, proc_id) = match op.code {
                    OpCode::ResolvedIdent {
                        module, proc_id, ..
                    } => (module, proc_id),
                    _ => {
                        dst_ops.push(op);
                        continue;
                    }
                };

                let found_proc = program.get_proc(proc_id);
                if !found_proc.kind().is_macro() {
                    dst_ops.push(op);
                    continue;
                }

                expanded_macro = true;
                last_changed_macros.push(found_proc.name());
                dst_ops.extend(found_proc.body().iter().map(|new_op| {
                    let mut new_op = new_op.clone();
                    new_op.expansions.push(op.token.location);
                    new_op.expansions.extend_from_slice(&op.expansions);
                    new_op
                }));
            }

            if !expanded_macro {
                break;
            }

            if num_expansions > 128 {
                let mut labels = Vec::new();

                let first_loc = last_changed_macros[0];
                for macro_token in last_changed_macros {
                    labels.push(
                        Label::new(macro_token.location)
                            .with_color(Color::Red)
                            .with_message("exceeded expansion limit"),
                    );
                }

                diagnostics::emit(
                    first_loc.location,
                    "depth of macro expansion exeeced 128",
                    labels,
                    None,
                    source_store,
                );

                had_error = true;
                break;
            }

            num_expansions += 1;
            std::mem::swap(&mut src_ops, &mut dst_ops);
        }

        self.body = src_ops;

        had_error
            .not()
            .then(|| ())
            .ok_or_else(|| eyre!("failed to expand macro"))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(usize);

pub struct Program {
    module_counter: usize,
    modules: HashMap<ModuleId, Module>,
    module_ident_map: HashMap<Spur, ModuleId>,

    proc_counter: usize,
    all_procedures: HashMap<ProcedureId, Procedure>,
}

impl Program {
    pub fn new() -> Self {
        Program {
            module_counter: 0,
            modules: Default::default(),
            module_ident_map: Default::default(),
            proc_counter: 0,
            all_procedures: HashMap::new(),
        }
    }

    fn new_module(&mut self, name: Spur) -> ModuleId {
        self.module_counter += 1;
        let new_id = ModuleId(self.module_counter);

        let module = Module {
            name,
            id: new_id,
            has_resolved_visible: false,
            top_level_symbols: HashMap::new(),
        };
        self.module_ident_map.insert(name, new_id);
        self.modules.insert(new_id, module);

        new_id
    }

    pub fn get_module(&self, id: ModuleId) -> &Module {
        &self.modules[&id]
    }

    pub fn modules(&self) -> &HashMap<ModuleId, Module> {
        &self.modules
    }

    pub fn load_program(
        &mut self,
        file: &str,
        interner: &mut Interners,
        source_store: &mut SourceStorage,
        opt_level: u8,
        library_paths: &[String],
    ) -> Result<ModuleId> {
        let module_name = Path::new(file).file_stem().and_then(OsStr::to_str).unwrap();
        let module_name = interner.intern_lexeme(module_name);

        let mut program = Program::new();

        let mut loaded_modules = HashSet::new();
        let mut include_queue = Vec::new();

        let entry_module_id = program.new_module(module_name);

        let entry_module = Module::load(
            &mut program,
            entry_module_id,
            source_store,
            interner,
            file,
            opt_level,
            library_paths,
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
                    diagnostics::emit(
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

            let new_module_id = program.new_module(token.lexeme);

            let new_module = match Module::load(
                &mut program,
                entry_module_id,
                source_store,
                interner,
                &full_path,
                opt_level,
                library_paths,
                &mut include_queue,
            ) {
                Ok(module) => module,
                Err(e) => {
                    diagnostics::emit(
                        token.location,
                        "error loading module",
                        Some(
                            Label::new(token.location)
                                .with_color(Color::Red)
                                .with_message("here"),
                        ),
                        format!("{}", e),
                        source_store,
                    );

                    had_error = true;
                    continue;
                }
            };

            loaded_modules.insert(token.lexeme);
        }

        had_error |= program.post_process_procs(interner, source_store).is_ok();

        had_error
            .not()
            .then(|| entry_module_id)
            .ok_or_else(|| eyre!("failed to load program"))
    }

    fn resolve_idents(&mut self, interner: &Interners, source_store: &SourceStorage) -> Result<()> {
        let mut had_error = false;
        for (proc_id, proc) in self.all_procedures.iter_mut() {
            for op in &mut proc.body {
                match op.code {
                    // Symbol in own module.
                    OpCode::UnresolvedIdent {
                        token,
                        sub_token: None,
                    } => {
                        if let Some(id) = self.get_visible_symbol(*proc_id, token.lexeme) {
                            op.code = OpCode::ResolvedIdent {
                                module: proc.module,
                                proc_id: id,
                            };
                        } else {
                            let module = &self.modules[&proc.module];
                            let token_lexeme = interner.resolve_lexeme(token.lexeme);
                            let module_lexeme = interner.resolve_lexeme(module.name);
                            diagnostics::emit(
                                token.location,
                                format!(
                                    "symbol `{}` not found in module `{}`",
                                    token_lexeme, module_lexeme
                                ),
                                Some(
                                    Label::new(token.location)
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
                        token,
                        sub_token: Some(proc),
                    } => {
                        let module_id = match self.module_ident_map.get(&token.lexeme) {
                            Some(id) => *id,
                            None => {
                                let module_name = interner.resolve_lexeme(token.lexeme);
                                diagnostics::emit(
                                    token.location,
                                    format!("module `{}` not found", module_name),
                                    Some(
                                        Label::new(token.location)
                                            .with_color(Color::Red)
                                            .with_message("not found"),
                                    ),
                                    None,
                                    source_store,
                                );
                                had_error = true;
                                continue;
                            }
                        };

                        let module = &self.modules[&module_id];
                        match module.top_level_symbols.get(&proc.lexeme) {
                            Some(proc_id) => {
                                op.code = OpCode::ResolvedIdent {
                                    module: module_id,
                                    proc_id: *proc_id,
                                };
                            }
                            None => {
                                let proc_name = interner.resolve_lexeme(proc.lexeme);
                                let module_name = interner.resolve_lexeme(token.lexeme);
                                diagnostics::emit(
                                    proc.location,
                                    format!(
                                        "symbol `{}` not found in module `{}`",
                                        proc_name, module_name
                                    ),
                                    Some(
                                        Label::new(proc.location)
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
        }

        had_error
            .not()
            .then(|| ())
            .ok_or_else(|| eyre!("error during ident resolation"))
    }

    fn expand_macros(&mut self, interner: &Interners, source_store: &SourceStorage) -> Result<()> {
        let mut had_error = false;
        let non_macro_proc_ids: Vec<_> = self
            .all_procedures
            .iter()
            .filter(|(_, p)| !p.kind().is_macro())
            .map(|(id, _)| *id)
            .collect();

        for proc_id in non_macro_proc_ids {
            let mut proc = self.all_procedures.remove(&proc_id).unwrap();

            if proc.expand_macros(self, interner, source_store).is_err() {
                had_error = true;
            }

            self.all_procedures.insert(proc_id, proc);
        }

        had_error
            .not()
            .then(|| ())
            .ok_or_else(|| eyre!("error during macro expansion"))
    }

    fn check_all_const_for_loops(
        &self,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let mut had_error = false;

        for (&own_proc_id, own_proc) in &self.all_procedures {
            if !own_proc.kind().is_const() {
                continue;
            }

            let mut seen_ids = HashSet::new();
            seen_ids.insert(own_proc_id);
            let mut check_queue = vec![own_proc];
            while let Some(proc) = check_queue.pop() {
                if !proc.kind().is_const() {
                    panic!("ICE: found non-const reference in const");
                }

                for op in &proc.body {
                    match op.code {
                        OpCode::ResolvedIdent { proc_id, .. } => {
                            if seen_ids.insert(proc_id) == false {
                                had_error = true;
                                diagnostics::emit(
                                    proc.name.location,
                                    "const reference cycle detected",
                                    [
                                        Label::new(own_proc.name.location)
                                            .with_color(Color::Red)
                                            .with_message("in this const"),
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
                        _ => {}
                    }
                }
            }
        }

        had_error
            .not()
            .then(|| ())
            .ok_or_else(|| eyre!("failed const self-check"))
    }

    fn type_check_procs(&self, interner: &Interners, source_store: &SourceStorage) -> Result<()> {
        let mut had_error = false;

        for (proc_id, proc) in &self.all_procedures {
            // Macros have already been expanded, so we don't need to check them.
            if proc.kind().is_macro() {
                continue;
            }

            had_error |= type_check::type_check(self, proc, interner, source_store).is_err();
        }

        had_error
            .not()
            .then(|| ())
            .ok_or_else(|| eyre!("failed type checking"))
    }

    fn evaluate_const_values(
        &mut self,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let mut had_error = false;

        let mut const_queue: Vec<_> = self
            .all_procedures
            .iter()
            .filter(|(_, proc)| proc.kind().is_const())
            .map(|(id, _)| *id)
            .collect();
        let mut next_run_queue = Vec::with_capacity(const_queue.len());

        // Generate the jump labels first so we can simulate them.
        for &const_id in &const_queue {
            let proc = self.get_proc_mut(const_id);
            had_error |= opcode::generate_jump_labels(&mut proc.body, source_store).is_err();
        }

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
                            .zip(proc.exit_stack)
                            .map(|(val, ty)| (ty.kind, val))
                            .collect();

                        match self.get_proc_mut(const_id).kind {
                            ProcedureKind::Const { const_val } => {
                                const_val = Some(const_vals);
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
            .then(|| ())
            .ok_or_else(|| eyre!("failed during const evaluation"))
    }

    fn post_process_procs(
        &mut self,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        self.resolve_idents(interner, source_store)?;
        self.expand_macros(interner, source_store)?;
        self.check_all_const_for_loops(interner, source_store)?;
        self.type_check_procs(interner, source_store)?;
        self.evaluate_const_values(interner, source_store);

        // Expand consts, calls, and memory references.
        // Evaluate memory.

        Ok(())
    }

    pub fn get_proc(&self, id: ProcedureId) -> &Procedure {
        &self.all_procedures[&id]
    }

    pub fn get_proc_mut(&mut self, id: ProcedureId) -> &mut Procedure {
        self.all_procedures.get_mut(&id).unwrap()
    }

    pub fn new_procedure(
        &mut self,
        name: Token,
        module: ModuleId,
        kind: ProcedureKind,
        parent: Option<ProcedureId>,
        exit_stack: Vec<PorthType>,
        entry_stack: Vec<PorthType>,
    ) -> ProcedureId {
        let id = ProcedureId(self.proc_counter);
        self.proc_counter += 1;

        let proc = Procedure {
            name,
            module,
            id,
            kind,
            body: Vec::new(),
            parent,
            exit_stack,
            entry_stack,
            visible_symbols: HashMap::new(),
        };

        self.all_procedures.insert(id, proc);

        if parent.is_none() {
            let module = &mut self.modules[&module];
            module.top_level_symbols.insert(name.lexeme, id);
        }

        id
    }

    pub fn get_visible_symbol(&self, from: ProcedureId, symbol: Spur) -> Option<ProcedureId> {
        let mut cur_id = Some(from);
        while let Some(id) = cur_id {
            let proc = self.get_proc(id);
            if let ProcedureKind::Function(FunctionData { allocs, consts, .. }) = &proc.kind {
                if let Some(found_id) = allocs.get(&symbol).or_else(|| consts.get(&symbol)) {
                    return Some(*found_id);
                }
            }
            cur_id = proc.parent;
        }

        let module_id = self.all_procedures[&from].module;
        let module = &self.modules[&module_id];
        module.top_level_symbols.get(&symbol).copied()
    }
}

pub struct Module {
    name: Spur,
    id: ModuleId,
    has_resolved_visible: bool,
    top_level_symbols: HashMap<Spur, ProcedureId>,
}

impl Module {
    fn post_process_procedure(
        &mut self,
        procedure: &mut Procedure,
        interner: &mut Interners,
        source_store: &SourceStorage,
        opt_level: u8,
    ) -> Result<bool, ()> {
        let (new_body, failed_const_eval) =
            opcode::expand_sub_blocks(self, interner, procedure, source_store)?;
        procedure.body = new_body;

        if !failed_const_eval {
            if opt_level >= OPT_OPCODE {
                procedure.body = opcode::optimize(&procedure.body, interner, source_store);
            }

            opcode::generate_jump_labels(&mut procedure.body, source_store)?;
        }

        Ok(failed_const_eval)
    }

    fn post_process(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
        opt_level: u8,
    ) -> Result<(), ()> {
        let mut had_error = false;

        // We're applying the same process to the global procedure, defined procedures, and memory defs,
        // so do them all in one loop instead of separately.
        let to_check: Vec<_> = self
            .all_procs
            .iter()
            .filter(|(_, p)| !p.kind.is_const() && !p.kind().is_macro())
            .map(|(id, _)| *id)
            .collect();

        for proc_id in to_check {
            let mut proc = self.all_procs.remove(&proc_id).unwrap();

            if self
                .post_process_procedure(&mut proc, interner, source_store, opt_level)
                .is_err()
            {
                had_error = true;
            }

            self.all_procs.insert(proc_id, proc);
        }

        had_error.not().then(|| ()).ok_or(())
    }

    fn post_process_consts(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
        opt_level: u8,
    ) -> Result<(), ()> {
        let mut had_error = false;

        let mut const_proc_ids: Vec<_> = self
            .all_procs
            .iter()
            .filter(|(_, p)| p.kind.is_const())
            .map(|(id, _)| *id)
            .collect();
        let mut next_run_names = Vec::new();

        let mut num_loops = 0;
        const MAX_EXPANSIONS: usize = 128;
        let mut last_changed_consts: Vec<Token> = Vec::new();

        loop {
            for const_id in const_proc_ids.drain(..) {
                let mut procedure = self.all_procs.remove(&const_id).unwrap();

                match self.post_process_procedure(&mut procedure, interner, source_store, opt_level)
                {
                    // We failed expansion. This would be because it needed the value of another,
                    // as yet un-evaluated constant.
                    Ok(true) => {
                        last_changed_consts.push(procedure.name);
                        self.all_procs.insert(const_id, procedure);
                        next_run_names.push(const_id);
                    }
                    // We succeeded in fully expanding the constant.
                    // Now we type check then evaluate it.
                    Ok(false) => {
                        if type_check::type_check(self, &procedure, interner, source_store).is_err()
                        {
                            had_error = true;
                            continue;
                        }

                        let stack =
                            match simulate_execute_program(&procedure, interner, source_store) {
                                Err(_) => {
                                    had_error = true;
                                    continue;
                                }
                                Ok(stack) => stack,
                            };

                        let const_vals = stack
                            .into_iter()
                            .zip(procedure.exit_stack())
                            .map(|(val, ty)| (ty.kind, val))
                            .collect();
                        match &mut procedure.kind {
                            ProcedureKind::Const { const_val } => *const_val = Some(const_vals),
                            _ => panic!("ICE: Tried setting const_val on non-const proc"),
                        }
                        self.all_procs.insert(const_id, procedure);
                    }
                    Err(_) => {
                        eprint!("test");
                        had_error = true;
                    }
                }
            }

            // No more constants left to evaluate.
            if next_run_names.is_empty() {
                break;
            }

            num_loops += 1;
            if num_loops > MAX_EXPANSIONS {
                let mut labels = Vec::new();

                let first_con = last_changed_consts[0];
                for con in last_changed_consts {
                    labels.push(Label::new(con.location).with_color(Color::Red));
                }
                diagnostics::emit(
                    first_con.location,
                    "depth of const expansion exceeded 128",
                    labels,
                    None,
                    source_store,
                );

                had_error = true;
                break;
            }

            std::mem::swap(&mut const_proc_ids, &mut next_run_names);
        }

        had_error.not().then(|| ()).ok_or(())
    }

    fn type_check(&self, interner: &Interners, source_store: &SourceStorage) -> Result<(), ()> {
        let mut had_error = false;

        for proc in self.all_procs.values() {
            if proc.kind.is_macro() {
                continue;
            }

            if type_check::type_check(self, proc, interner, source_store).is_err() {
                had_error = true;
            }
        }

        had_error.not().then(|| ()).ok_or(())
    }

    fn check_const_for_self(&self, source_store: &SourceStorage) -> Result<(), ()> {
        let mut had_error = false;
        // Consts cannot reference themselves, so we should check that here.
        for proc in self.all_procs.values() {
            if let ProcedureKind::Const { .. } = &proc.kind {
                for op in &proc.body {
                    if matches!(op.code, OpCode::UnresolvedIdent(ref_id) if ref_id == proc.name.lexeme)
                    {
                        diagnostics::emit(
                            op.token.location,
                            "self referencing const",
                            Some(Label::new(op.token.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        had_error = true;

                        break;
                    }
                }
            }
        }

        had_error.not().then(|| ()).ok_or(())
    }

    fn evaluate_allocation_sizes(
        &mut self,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Result<(), ()> {
        let mut had_error = false;

        let alloc_ids: Vec<_> = self
            .all_procs
            .iter()
            .filter(|(_, p)| p.kind.is_memory())
            .map(|(id, _)| *id)
            .collect();

        for alloc_id in alloc_ids {
            let mut stack =
                match simulate_execute_program(self.get_proc(alloc_id), interner, source_store) {
                    Err(()) => {
                        had_error = true;
                        continue;
                    }
                    Ok(stack) => stack,
                };

            // The type checker enforces a single stack item here.
            let alloc_size = stack.pop().unwrap() as usize;

            // All allocs have a parent.
            let alloc_proc = self.get_proc(alloc_id);
            let alloc_proc_parent = alloc_proc.parent.unwrap();
            let alloc_proc_name = alloc_proc.name();

            let parent_proc = self.get_proc_mut(alloc_proc_parent);
            let proc_data = match &mut parent_proc.kind {
                ProcedureKind::Function(data) => data,
                _ => panic!("ICE: Alloc parent wasn't a proc"),
            };

            let alloc_data = AllocData {
                size: alloc_size,
                offset: proc_data.total_alloc_size,
            };
            proc_data
                .alloc_size_and_offsets
                .insert(alloc_proc_name.lexeme, alloc_data);
            proc_data.total_alloc_size += alloc_size;
        }

        had_error.not().then(|| ()).ok_or(())
    }

    pub fn load(
        program: &mut Program,
        module_id: ModuleId,
        source_store: &mut SourceStorage,
        interner: &mut Interners,
        file: &str,
        opt_level: u8,
        library_paths: &[String],
        include_queue: &mut Vec<Token>,
    ) -> Result<()> {
        let contents =
            std::fs::read_to_string(file).with_context(|| eyre!("Failed to open file {}", file))?;

        let file_id = source_store.add(file, &contents);

        let tokens = lexer::lex_file(&contents, file_id, interner, source_store)
            .map_err(|_| eyre!("error lexing file: {}", file))?;

        let file_stem = Path::new(file).file_stem().and_then(OsStr::to_str).unwrap();
        let module_spur = interner.intern_lexeme(file_stem);

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

    fn post_process_module(
        &mut self,
        program: &Program,
        opt_level: u8,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let module_name = interner.resolve_lexeme(self.name);

        // Fix this crap

        self.post_process_consts(interner, source_store, opt_level)
            .map_err(|_| eyre!("error processing consts: {}", module_name))?;

        self.post_process(interner, source_store, opt_level)
            .map_err(|_| eyre!("error processing procedures: {}", module_name))?;

        self.type_check(interner, source_store)
            .map_err(|_| eyre!("error type checking: {}", module_name))?;

        self.evaluate_allocation_sizes(interner, source_store)
            .map_err(|_| eyre!("error evaluating allocation sizes: {}", module_name))?;

        Ok(())
    }

    pub fn get_proc_id(&self, name: Spur) -> Option<ProcedureId> {
        self.top_level_symbols.get(&name).copied()
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
