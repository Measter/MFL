#![allow(clippy::too_many_arguments)]

use std::{
    collections::{HashMap, HashSet},
    path::Path,
    process::Command,
};

use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    term::termcolor::{ColorChoice, StandardStream},
};
use color_eyre::eyre::{eyre, Context, Result};
use interners::Interners;
use lasso::Spur;
use lexer::Token;
use source_file::{FileId, SourceStorage};
use structopt::StructOpt;

// mod compile;
mod compile;
mod interners;
mod lexer;
mod n_ops;
mod opcode;
mod simulate;
mod source_file;
mod type_check;

use opcode::{Op, OpCode, Procedure};
use simulate::simulate_execute_program;

const OPT_OPCODE: u8 = 1;
const OPT_INSTR: u8 = 2;
const OPT_STACK: u8 = 3;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Width {
    Byte,
    Word,
    Dword,
    Qword,
}

#[derive(Debug, StructOpt)]
enum Mode {
    /// Simulate the program
    #[structopt(name = "sim")]
    Simulate {
        file: String,

        /// Set optimization level
        #[structopt(short, parse(from_occurrences))]
        opt_level: u8,

        /// Arguments to pass to the executed Porth program
        args: Vec<String>,
    },

    /// Compile the program
    #[structopt(name = "com")]
    Compile {
        file: String,

        /// Set optimization level
        #[structopt(short, parse(from_occurrences))]
        opt_level: u8,
    },
}

#[derive(Debug, StructOpt)]
struct Args {
    /// Comma-separated list of paths to search includes.
    #[structopt(short = "I", require_delimiter = true)]
    library_paths: Vec<String>,

    #[structopt(subcommand)]
    mode: Mode,
}

type LoadProgramResult = Result<Program, Vec<Diagnostic<FileId>>>;

pub struct Program {
    global: Procedure,
    macros: HashMap<Spur, Procedure>,
    procedures: HashMap<Spur, Procedure>,
    const_values: HashMap<Spur, Procedure>,
    included_files: HashMap<Spur, Vec<Op>>,
    include_queue: Vec<(Token, Spur)>,
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

        let ops = match opcode::parse_token(self, &tokens, interner, None) {
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
        procedure: &mut Procedure,
        interner: &mut Interners,
        source_store: &SourceStorage,
        macros: &HashMap<Spur, Procedure>,
        const_values: &HashMap<Spur, Procedure>,
        included_files: &HashMap<Spur, Vec<Op>>,
        global_alloc_names: &HashSet<Spur>,
        procedure_names: &HashSet<Spur>,
        opt_level: u8,
    ) -> Result<bool, Vec<Diagnostic<FileId>>> {
        procedure.body = opcode::expand_includes(included_files, &procedure.body);
        let (new_body, failed_const_eval) = opcode::expand_sub_blocks(
            macros,
            const_values,
            global_alloc_names,
            procedure_names,
            &procedure.body,
            &procedure.allocs,
        )?;
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
        // We don't need the entire allocation or procedure data just for the expansion, so we'll just use
        // HashSets here.
        let global_alloc_names: HashSet<_> = self.global.allocs.keys().copied().collect();
        let procedure_names: HashSet<_> = self.procedures.keys().copied().collect();
        let mut all_diags = Vec::new();

        // We're applying the same process to the global procedure, defined procedures, and memory defs,
        // so do them all in one loop instead of separately.
        let to_check = std::iter::once(&mut self.global).chain(self.procedures.values_mut());

        for proc in to_check {
            if let Err(mut diags) = Program::post_process_procedure(
                proc,
                interner,
                source_store,
                &self.macros,
                &self.const_values,
                &self.included_files,
                &global_alloc_names,
                &procedure_names,
                opt_level,
            ) {
                all_diags.append(&mut diags);
            };

            // Now check the allocs
            for alloc in proc.allocs.values_mut() {
                if let Err(mut diags) = Program::post_process_procedure(
                    alloc,
                    interner,
                    source_store,
                    &self.macros,
                    &self.const_values,
                    &self.included_files,
                    &global_alloc_names,
                    &procedure_names,
                    opt_level,
                ) {
                    all_diags.append(&mut diags);
                };
            }
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

        let mut const_names: Vec<_> = self.const_values.keys().copied().collect();
        let mut next_run_names = Vec::new();
        let static_alloc_names: HashSet<_> = self.global.allocs.keys().copied().collect();
        let procedure_names: HashSet<_> = self.procedures.keys().copied().collect();

        let mut num_loops = 0;
        const MAX_EXPANSIONS: usize = 128;
        let mut last_changed_consts: Vec<Token> = Vec::new();

        loop {
            for const_id in const_names.drain(..) {
                let mut procedure = self.const_values.remove(&const_id).unwrap();

                match Program::post_process_procedure(
                    &mut procedure,
                    interner,
                    source_store,
                    &self.macros,
                    &self.const_values,
                    &self.included_files,
                    &static_alloc_names,
                    &procedure_names,
                    opt_level,
                ) {
                    // We failed expansion. This would be because it needed the value of another,
                    // as yet un-evaluated constant.
                    Ok(true) => {
                        last_changed_consts.push(procedure.name);
                        self.const_values.insert(const_id, procedure);
                        next_run_names.push(const_id);
                    }
                    // We succeeded in fully expanding the constant.
                    // Now we type check then evaluate it.
                    Ok(false) => {
                        if let Err(mut diags) =
                            type_check::type_check(&procedure, &self.procedures, interner)
                        {
                            all_diags.append(&mut diags);
                            continue;
                        }

                        let mut stack = match simulate_execute_program(
                            self,
                            &procedure,
                            &HashMap::new(),
                            interner,
                            &[],
                        ) {
                            Err(diag) => {
                                all_diags.push(diag);
                                continue;
                            }
                            Ok(stack) => stack,
                        };

                        // The type checker enforces a single stack item here.
                        procedure.const_val = stack.pop();
                        self.const_values.insert(const_id, procedure);
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

            std::mem::swap(&mut const_names, &mut next_run_names);
        }

        all_diags.is_empty().then(|| ()).ok_or(all_diags)
    }

    fn type_check(&self, interner: &Interners) -> Result<(), Vec<Diagnostic<FileId>>> {
        let mut all_diags = Vec::new();

        // Type checking requires seeing the entire program, so we have to iterate again
        // to avoid mutable aliasing.
        let to_check = std::iter::once(&self.global).chain(self.procedures.values());

        for proc in to_check {
            if let Err(mut diags) = type_check::type_check(proc, &self.procedures, interner) {
                all_diags.append(&mut diags);
            }

            for alloc in proc.allocs.values() {
                if let Err(mut diags) = type_check::type_check(alloc, &self.procedures, interner) {
                    all_diags.append(&mut diags);
                }
            }
        }

        all_diags.is_empty().then(|| ()).ok_or(all_diags)
    }

    fn check_const_for_self(&self) -> Result<(), Vec<Diagnostic<FileId>>> {
        let mut all_diags = Vec::new();
        // Consts cannot reference themselves, so we should check that here.
        for (id, proc) in &self.const_values {
            for op in &proc.body {
                if matches!(op.code, OpCode::Ident(ref_id) if ref_id == *id) {
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

        all_diags.is_empty().then(|| ()).ok_or(all_diags)
    }

    fn load(
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
            global: Procedure {
                name: tokens[0],
                body: Vec::new(),
                allocs: HashMap::new(),
                expected_entry_stack: Vec::new(),
                expected_exit_stack: Vec::new(),
                is_const: false,
                const_val: None,
            },
            macros: HashMap::new(),
            procedures: HashMap::new(),
            const_values: HashMap::new(),
            included_files: HashMap::new(),
            include_queue: Vec::new(),
        };

        program.global.body = match opcode::parse_token(&mut program, &tokens, interner, None) {
            Ok(ops) => ops,
            Err(diags) => return Ok(Err(diags)),
        };

        if let Err(diags) = program.process_include_queue(source_store, interner, library_paths) {
            return Ok(Err(diags));
        }

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

        Ok(Ok(program))
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

fn evaluate_allocation_sizes(
    program: &Program,
    interner: &Interners,
) -> Result<HashMap<Spur, usize>, Vec<Diagnostic<FileId>>> {
    let mut alloc_sizes = HashMap::new();
    let mut diags = Vec::new();

    for (&id, proc) in &program.global.allocs {
        let mut stack =
            match simulate_execute_program(program, proc, &HashMap::new(), interner, &[]) {
                Err(diag) => {
                    diags.push(diag);
                    continue;
                }
                Ok(stack) => stack,
            };

        // The type checker enforces a single stack item here.
        alloc_sizes.insert(id, stack.pop().unwrap() as usize);
    }

    diags.is_empty().then(|| alloc_sizes).ok_or(diags)
}

fn run_simulate(
    file: String,
    opt_level: u8,
    mut program_args: Vec<String>,
    include_paths: Vec<String>,
) -> Result<()> {
    let cfg = codespan_reporting::term::Config::default();
    let stderr = StandardStream::stderr(ColorChoice::Always);
    let mut stderr = stderr.lock();

    let mut source_storage = SourceStorage::new();
    let mut interner = Interners::new();

    program_args.insert(0, file.clone()); // We need the program name to be part of the args.

    let program = match Program::load(
        &mut source_storage,
        &mut interner,
        &file,
        opt_level,
        &include_paths,
    )? {
        Ok(program) => program,
        Err(diags) => {
            for diag in diags {
                codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
            }
            std::process::exit(-1);
        }
    };

    let alloc_sizes = match evaluate_allocation_sizes(&program, &interner) {
        Ok(sizes) => sizes,
        Err(diags) => {
            for diag in diags {
                codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
            }
            std::process::exit(-1);
        }
    };

    if let Err(diag) = simulate::simulate_execute_program(
        &program,
        &program.global,
        &alloc_sizes,
        &interner,
        &program_args,
    ) {
        codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
    }

    Ok(())
}

fn run_compile(file: String, opt_level: u8, include_paths: Vec<String>) -> Result<()> {
    let cfg = codespan_reporting::term::Config::default();
    let stderr = StandardStream::stderr(ColorChoice::Always);
    let mut stderr = stderr.lock();

    let mut source_storage = SourceStorage::new();
    let mut interner = Interners::new();

    let mut output_asm = Path::new(&file).to_path_buf();
    output_asm.set_extension("asm");
    let mut output_obj = output_asm.clone();
    output_obj.set_extension("o");
    let mut output_binary = output_obj.clone();
    output_binary.set_extension("");

    let program = match Program::load(
        &mut source_storage,
        &mut interner,
        &file,
        opt_level,
        &include_paths,
    )? {
        Ok(program) => program,
        Err(diags) => {
            for diag in diags {
                codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
            }
            std::process::exit(-1);
        }
    };

    println!("Evaluating static allocations...");

    let alloc_sizes = match evaluate_allocation_sizes(&program, &interner) {
        Ok(sizes) => sizes,
        Err(diags) => {
            for diag in diags {
                codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
            }
            std::process::exit(-1);
        }
    };

    println!("Compiling... to {}", output_asm.display());
    compile::compile_program(
        &program,
        &alloc_sizes,
        &source_storage,
        &interner,
        &output_asm,
        opt_level,
    )?;

    println!("Assembling... to {}", output_obj.display());
    let nasm = Command::new("nasm")
        .arg("-felf64")
        .arg(&output_asm)
        .status()
        .with_context(|| eyre!("Failed to execute nasm"))?;
    if !nasm.success() {
        std::process::exit(-2);
    }

    println!("Linking... into {}", output_binary.display());
    let ld = Command::new("ld")
        .arg("-o")
        .arg(&output_binary)
        .arg(&output_obj)
        .status()
        .with_context(|| eyre!("Failed to execude ld"))?;

    if !ld.success() {
        std::process::exit(-3);
    }

    Ok(())
}

fn main() -> Result<()> {
    color_eyre::install()?;
    let args = Args::from_args();

    match args.mode {
        Mode::Simulate {
            file,
            opt_level,
            args: program_args,
        } => run_simulate(file, opt_level, program_args, args.library_paths)?,
        Mode::Compile { file, opt_level } => run_compile(file, opt_level, args.library_paths)?,
    }

    Ok(())
}
