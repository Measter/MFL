use std::{collections::HashMap, path::Path};

use codespan_reporting::diagnostic::{Diagnostic, Label};
use color_eyre::eyre::{eyre, Context, Result};
use lasso::Spur;
use variantly::Variantly;

use crate::{
    interners::Interners,
    lexer::{self, Token},
    opcode::{self, Op, OpCode},
    simulate::simulate_execute_program,
    source_file::{FileId, SourceStorage},
    type_check::{self, PorthType, PorthTypeKind},
    OPT_OPCODE,
};

type LoadProgramResult = Result<Program, Vec<Diagnostic<FileId>>>;

#[derive(Debug, Clone, Copy)]
pub struct AllocData {
    pub size: usize,
    pub offset: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProcedureId(usize);

#[derive(Debug, Default)]
pub struct ProcData {
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
    Proc(ProcData),
}

impl ProcedureKind {
    pub fn get_proc_data(&self) -> &ProcData {
        match self {
            ProcedureKind::Proc(data) => data,
            _ => panic!("ICE: called get_proc_data on a non-proc"),
        }
    }
}

#[derive(Debug)]
pub struct Procedure {
    name: Token,
    id: ProcedureId,
    parent: Option<ProcedureId>,
    body: Vec<Op>,
    kind: ProcedureKind,
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
}

pub struct Program {
    top_level_proc_id: ProcedureId,
    included_files: HashMap<Spur, Vec<Op>>,
    include_queue: Vec<(Token, Spur)>,

    proc_counter: usize,
    all_procs: HashMap<ProcedureId, Procedure>,
    macros: HashMap<Spur, ProcedureId>,
    functions: HashMap<Spur, ProcedureId>,
    has_resolved_visible: bool,
}

impl Program {
    fn load_include(
        &mut self,
        source_store: &mut SourceStorage,
        interner: &mut Interners,
        library_paths: &[String],
        include_token: Token,
        file: Spur,
    ) -> Result<(), Vec<Diagnostic<FileId>>> {
        if self.included_files.contains_key(&file) {
            return Ok(());
        }

        let file_name = interner.resolve_literal(file);
        // String literals are always null-terminated, so we need to trim that off.
        let file_name = &file_name[..file_name.len() - 1];

        let include_path = match search_includes(library_paths, file_name) {
            Some(path) => path,
            None => {
                let diag = Diagnostic::error()
                    .with_message(format!("include not found: `{}`", file_name))
                    .with_labels(vec![Label::primary(
                        include_token.location.file_id,
                        include_token.location.range(),
                    )]);
                return Err(vec![diag]);
            }
        };

        let contents = match std::fs::read_to_string(&include_path) {
            Ok(contents) => contents,
            Err(e) => {
                let diag = Diagnostic::error()
                    .with_message(format!("error opening `{}`", include_path))
                    .with_labels(vec![Label::primary(
                        include_token.location.file_id,
                        include_token.location.range(),
                    )])
                    .with_notes(vec![format!("{}", e)]);
                return Err(vec![diag]);
            }
        };

        let file_id = source_store.add(&include_path, &contents);

        let tokens = match lexer::lex_file(&contents, file_id, interner, source_store) {
            Ok(program) => program,
            Err(diag) => return Err(vec![diag]),
        };

        let ops = match opcode::parse_token(self, &tokens, interner, self.top_level_proc_id) {
            Ok(ops) => ops,
            Err(diags) => return Err(diags),
        };

        self.included_files.insert(file, ops);

        Ok(())
    }

    fn process_include_queue(
        &mut self,
        source_store: &mut SourceStorage,
        interner: &mut Interners,
        library_paths: &[String],
    ) -> Result<(), Vec<Diagnostic<FileId>>> {
        let mut all_diags = Vec::new();

        while let Some((include_token, file)) = self.include_queue.pop() {
            if let Err(mut diags) =
                self.load_include(source_store, interner, library_paths, include_token, file)
            {
                all_diags.append(&mut diags);
            }
        }

        all_diags.is_empty().then(|| ()).ok_or(all_diags)
    }

    fn post_process_procedure(
        &mut self,
        procedure: &mut Procedure,
        interner: &mut Interners,
        source_store: &SourceStorage,
        opt_level: u8,
    ) -> Result<bool, Vec<Diagnostic<FileId>>> {
        procedure.body = opcode::expand_includes(&self.included_files, &procedure.body);
        let (new_body, failed_const_eval) = opcode::expand_sub_blocks(self, interner, procedure)?;
        procedure.body = new_body;

        if !failed_const_eval {
            if opt_level >= OPT_OPCODE {
                procedure.body = opcode::optimize(&procedure.body, interner, source_store);
            }

            opcode::generate_jump_labels(&mut procedure.body)?;
        }

        Ok(failed_const_eval)
    }

    fn post_process(
        &mut self,
        interner: &mut Interners,
        source_store: &mut SourceStorage,
        opt_level: u8,
    ) -> Result<(), Vec<Diagnostic<FileId>>> {
        let mut all_diags = Vec::new();

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

            if let Err(mut diags) =
                self.post_process_procedure(&mut proc, interner, source_store, opt_level)
            {
                all_diags.append(&mut diags);
            }

            self.all_procs.insert(proc_id, proc);
        }

        all_diags.is_empty().then(|| ()).ok_or(all_diags)
    }

    fn post_process_consts(
        &mut self,
        interner: &mut Interners,
        source_store: &mut SourceStorage,
        opt_level: u8,
    ) -> Result<(), Vec<Diagnostic<FileId>>> {
        let mut all_diags = Vec::new();

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
                        if let Err(mut diags) = type_check::type_check(self, &procedure, interner) {
                            all_diags.append(&mut diags);
                            continue;
                        }

                        let stack = match simulate_execute_program(self, &procedure, interner, &[])
                        {
                            Err(diag) => {
                                all_diags.push(diag);
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
                    Err(mut diags) => {
                        all_diags.append(&mut diags);
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

                for con in last_changed_consts {
                    labels.push(Label::primary(con.location.file_id, con.location.range()));
                }
                let diag = Diagnostic::error()
                    .with_message("depth of const expansion exceeded 128")
                    .with_labels(labels);

                all_diags.push(diag);
                break;
            }

            std::mem::swap(&mut const_proc_ids, &mut next_run_names);
        }

        all_diags.is_empty().then(|| ()).ok_or(all_diags)
    }

    fn type_check(&self, interner: &Interners) -> Result<(), Vec<Diagnostic<FileId>>> {
        let mut all_diags = Vec::new();

        for proc in self.all_procs.values() {
            if proc.kind.is_macro() {
                continue;
            }

            if let Err(mut diags) = type_check::type_check(self, proc, interner) {
                all_diags.append(&mut diags);
            }
        }

        all_diags.is_empty().then(|| ()).ok_or(all_diags)
    }

    fn check_const_for_self(&self) -> Result<(), Vec<Diagnostic<FileId>>> {
        let mut all_diags = Vec::new();
        // Consts cannot reference themselves, so we should check that here.
        for proc in self.all_procs.values() {
            if let ProcedureKind::Const { .. } = &proc.kind {
                for op in &proc.body {
                    if matches!(op.code, OpCode::Ident(ref_id) if ref_id == proc.name.lexeme) {
                        let diag = Diagnostic::error()
                            .with_message("self referencing const")
                            .with_labels(vec![Label::primary(
                                op.token.location.file_id,
                                op.token.location.range(),
                            )]);
                        all_diags.push(diag);
                        break;
                    }
                }
            }
        }

        all_diags.is_empty().then(|| ()).ok_or(all_diags)
    }

    fn evaluate_allocation_sizes(
        &mut self,
        interner: &Interners,
    ) -> Result<(), Vec<Diagnostic<FileId>>> {
        let mut diags = Vec::new();
        let alloc_ids: Vec<_> = self
            .all_procs
            .iter()
            .filter(|(_, p)| p.kind.is_memory())
            .map(|(id, _)| *id)
            .collect();

        for alloc_id in alloc_ids {
            let mut stack =
                match simulate_execute_program(self, self.get_proc(alloc_id), interner, &[]) {
                    Err(diag) => {
                        diags.push(diag);
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
                ProcedureKind::Proc(data) => data,
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

        diags.is_empty().then(|| ()).ok_or(diags)
    }

    pub fn load(
        source_store: &mut SourceStorage,
        interner: &mut Interners,
        file: &str,
        opt_level: u8,
        library_paths: &[String],
    ) -> Result<LoadProgramResult> {
        let contents =
            std::fs::read_to_string(file).with_context(|| eyre!("Failed to open file {}", file))?;

        let file_id = source_store.add(file, &contents);

        let tokens = match lexer::lex_file(&contents, file_id, interner, source_store) {
            Ok(program) => program,
            Err(diag) => return Ok(Err(vec![diag])),
        };

        let mut program = Program {
            top_level_proc_id: ProcedureId(usize::MAX),
            included_files: HashMap::new(),
            include_queue: Vec::new(),
            proc_counter: 0,
            all_procs: HashMap::new(),
            macros: HashMap::new(),
            functions: HashMap::new(),
            has_resolved_visible: false,
        };

        let top_level_proc_id = program.new_procedure(
            tokens[0],
            ProcedureKind::Proc(ProcData::default()),
            None,
            Vec::new(),
            Vec::new(),
        );

        program.top_level_proc_id = top_level_proc_id;

        let top_level_body =
            match opcode::parse_token(&mut program, &tokens, interner, top_level_proc_id) {
                Ok(ops) => ops,
                Err(diags) => return Ok(Err(diags)),
            };

        *program.get_proc_mut(top_level_proc_id).body_mut() = top_level_body;

        if let Err(diags) = program.process_include_queue(source_store, interner, library_paths) {
            return Ok(Err(diags));
        }

        program.resolve_visible_symbols();

        if let Err(diags) = program.check_const_for_self() {
            return Ok(Err(diags));
        }

        if let Err(diags) = program.post_process_consts(interner, source_store, opt_level) {
            return Ok(Err(diags));
        }

        if let Err(diags) = program.post_process(interner, source_store, opt_level) {
            return Ok(Err(diags));
        }

        if let Err(diags) = program.type_check(interner) {
            return Ok(Err(diags));
        }

        if let Err(diags) = program.evaluate_allocation_sizes(interner) {
            return Ok(Err(diags));
        }

        Ok(Ok(program))
    }

    pub fn new_procedure(
        &mut self,
        name: Token,
        kind: ProcedureKind,
        parent: Option<ProcedureId>,
        exit_stack: Vec<PorthType>,
        entry_stack: Vec<PorthType>,
    ) -> ProcedureId {
        let id = ProcedureId(self.proc_counter);
        self.proc_counter += 1;

        let is_macro = kind.is_macro();
        let is_function = kind.is_proc();

        let proc = Procedure {
            name,
            id,
            kind,
            body: Vec::new(),
            parent,
            exit_stack,
            entry_stack,
            visible_symbols: HashMap::new(),
        };

        self.all_procs.insert(id, proc);

        if is_macro {
            self.macros.insert(name.lexeme, id);
        } else if is_function {
            self.functions.insert(name.lexeme, id);
        }

        id
    }

    pub fn get_proc(&self, id: ProcedureId) -> &Procedure {
        &self.all_procs[&id]
    }

    pub fn get_proc_mut(&mut self, id: ProcedureId) -> &mut Procedure {
        self.all_procs.get_mut(&id).unwrap()
    }

    pub fn get_visible_symbol(&self, from: ProcedureId, symbol: Spur) -> Option<ProcedureId> {
        // We only fully resolve symbols after parsing the entire input.
        // If we haven't, we need to fully walk the parent tree.
        if self.has_resolved_visible {
            return self.get_proc(from).get_visible_symbol(symbol);
        }

        if let Some(&found_id) = self
            .macros
            .get(&symbol)
            .or_else(|| self.functions.get(&symbol))
        {
            return Some(found_id);
        }

        let mut cur_id = Some(from);
        while let Some(id) = cur_id {
            let proc = self.get_proc(id);
            if let ProcedureKind::Proc(ProcData { allocs, consts, .. }) = &proc.kind {
                if let Some(found_id) = allocs.get(&symbol).or_else(|| consts.get(&symbol)) {
                    return Some(*found_id);
                }
            }
            cur_id = proc.parent;
        }

        None
    }

    pub fn top_level_proc_id(&self) -> ProcedureId {
        self.top_level_proc_id
    }

    pub fn add_include(&mut self, path_literal: Token, literal: Spur) {
        self.include_queue.push((path_literal, literal));
    }

    fn resolve_visible_symbols(&mut self) {
        let proc_keys: Vec<_> = self
            .all_procs
            .iter()
            .filter(|(_, p)| !p.kind().is_macro())
            .map(|(id, _)| *id)
            .collect();

        for proc_id in proc_keys {
            let mut proc = self.all_procs.remove(&proc_id).unwrap();

            let mut parent = proc.parent;
            while let Some(parent_id) = parent {
                let parent_proc = self.get_proc(parent_id);
                if let ProcedureKind::Proc(ProcData { allocs, consts, .. }) = &parent_proc.kind {
                    for (&name, &id) in allocs.iter().chain(consts) {
                        proc.visible_symbols.insert(name, id);
                    }
                }
                parent = parent_proc.parent;
            }

            for (&name, &id) in self.macros.iter().chain(&self.functions) {
                proc.visible_symbols.insert(name, id);
            }

            if let ProcedureKind::Proc(ProcData { allocs, consts, .. }) = &proc.kind {
                for (&name, &id) in allocs.iter().chain(consts) {
                    proc.visible_symbols.insert(name, id);
                }
            }

            self.all_procs.insert(proc_id, proc);
        }

        self.has_resolved_visible = true;
    }
}

fn search_includes(paths: &[String], file_name: &str) -> Option<String> {
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
