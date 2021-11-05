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

use opcode::Op;

use crate::simulate::simulate_execute_program;

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
    include_paths: Vec<String>,

    #[structopt(subcommand)]
    mode: Mode,
}

struct Program {
    ops: Vec<Op>,
    static_allocs: HashMap<Spur, (Token, Vec<Op>)>,
}

type LoadProgramResult = Result<Program, Vec<Diagnostic<FileId>>>;

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

fn load_include(
    source_store: &mut SourceStorage,
    macros: &mut HashMap<Spur, (Token, Vec<Op>)>,
    static_allocs: &mut HashMap<Spur, (Token, Vec<Op>)>,
    include_list: &mut Vec<(Token, Spur)>,
    included_files: &mut HashMap<Spur, Vec<Op>>,
    interner: &mut Interners,
    include_paths: &[String],
    include_token: Token,
    file: Spur,
) -> Result<(), Vec<Diagnostic<FileId>>> {
    if included_files.contains_key(&file) {
        return Ok(());
    }

    let file_name = interner.resolve_literal(file);
    // String literals are always null-terminated, so we need to trim that off.
    let file_name = &file_name[..file_name.len() - 1];

    let include_path = match search_includes(include_paths, file_name) {
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

    let ops = match opcode::parse_token(&tokens, interner, macros, static_allocs, include_list) {
        Ok(ops) => ops,
        Err(diags) => return Err(diags),
    };

    included_files.insert(file, ops);

    Ok(())
}

fn process_ops(
    mut program: Vec<Op>,
    interner: &mut Interners,
    included_files: &HashMap<Spur, Vec<Op>>,
    macros: &HashMap<Spur, (Token, Vec<Op>)>,
    static_alloc_names: &HashSet<Spur>,
    source_store: &SourceStorage,
    opt_level: u8,
    const_context: Option<Token>,
) -> Result<Vec<Op>, Vec<Diagnostic<FileId>>> {
    program = opcode::expand_includes(included_files, &program);
    program = opcode::expand_macros_and_allocs(macros, static_alloc_names, &program)?;

    if opt_level >= OPT_OPCODE {
        program = opcode::optimize(&program, interner, source_store);
    }

    opcode::generate_jump_labels(&mut program)?;
    type_check::type_check(&program, interner, const_context)?;

    Ok(program)
}

fn load_program(
    source_store: &mut SourceStorage,
    interner: &mut Interners,
    file: &str,
    opt_level: u8,
    include_paths: &[String],
) -> Result<LoadProgramResult> {
    let contents =
        std::fs::read_to_string(file).with_context(|| eyre!("Failed to open file {}", file))?;

    let file_id = source_store.add(file, &contents);

    let tokens = match lexer::lex_file(&contents, file_id, interner, source_store) {
        Ok(program) => program,
        Err(diag) => return Ok(Err(vec![diag])),
    };

    let mut macros = HashMap::new();
    let mut static_allocs = HashMap::new();
    let mut include_list = Vec::new();

    let mut program = match opcode::parse_token(
        &tokens,
        interner,
        &mut macros,
        &mut static_allocs,
        &mut include_list,
    ) {
        Ok(ops) => ops,
        Err(diags) => return Ok(Err(diags)),
    };

    let mut included_files = HashMap::new();

    while let Some((include_token, file)) = include_list.pop() {
        if let Err(diags) = load_include(
            source_store,
            &mut macros,
            &mut static_allocs,
            &mut include_list,
            &mut included_files,
            interner,
            include_paths,
            include_token,
            file,
        ) {
            return Ok(Err(diags));
        }
    }

    // We don't need the entry allocation data just for the expansion, so we'll just use a
    // HashSet here.
    let static_alloc_names: HashSet<_> = static_allocs.keys().copied().collect();

    program = match process_ops(
        program,
        interner,
        &included_files,
        &macros,
        &static_alloc_names,
        source_store,
        opt_level,
        None,
    ) {
        Ok(program) => program,
        Err(diags) => return Ok(Err(diags)),
    };

    // We also need to expand, generate labels and type check the memory allocation bodies.
    let mut all_alloc_diags = Vec::new();
    for (token, body) in static_allocs.values_mut() {
        match process_ops(
            std::mem::take(body),
            interner,
            &included_files,
            &macros,
            &static_alloc_names,
            source_store,
            0,
            Some(*token),
        ) {
            Ok(program) => *body = program,
            Err(mut diags) => {
                all_alloc_diags.append(&mut diags);
            }
        };
    }
    if !all_alloc_diags.is_empty() {
        return Ok(Err(all_alloc_diags));
    }

    let program = Program {
        ops: program,
        static_allocs,
    };

    Ok(Ok(program))
}

fn evaluate_allocation_sizes(
    static_allocs: &HashMap<Spur, (Token, Vec<Op>)>,
    interner: &Interners,
) -> Result<HashMap<Spur, usize>, Vec<Diagnostic<FileId>>> {
    let mut alloc_sizes = HashMap::new();
    let mut diags = Vec::new();

    for (&id, (_, body)) in static_allocs {
        let mut stack = match simulate_execute_program(body, &HashMap::new(), interner, &[], true) {
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

    let program = match load_program(
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

    let alloc_sizes = match evaluate_allocation_sizes(&program.static_allocs, &interner) {
        Ok(sizes) => sizes,
        Err(diags) => {
            for diag in diags {
                codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
            }
            std::process::exit(-1);
        }
    };

    if let Err(diag) = simulate::simulate_execute_program(
        &program.ops,
        &alloc_sizes,
        &interner,
        &program_args,
        false,
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

    let program = match load_program(
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

    let alloc_sizes = match evaluate_allocation_sizes(&program.static_allocs, &interner) {
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
        &program.ops,
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
        } => run_simulate(file, opt_level, program_args, args.include_paths)?,
        Mode::Compile { file, opt_level } => run_compile(file, opt_level, args.include_paths)?,
    }

    Ok(())
}
