use std::{collections::HashMap, path::Path, process::Command};

use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    term::termcolor::{ColorChoice, StandardStream},
};
use color_eyre::eyre::{eyre, Context, Result};
use interners::Interners;
use source_file::{FileId, SourceLocation, SourceStorage};
use structopt::StructOpt;

// mod compile;
mod compile_new;
mod interners;
mod lexer;
mod n_ops;
mod opcode;
mod simulate;
mod source_file;
mod type_check;

use opcode::Op;

const MEMORY_CAPACITY: usize = 2usize.pow(19);

#[derive(Debug, StructOpt)]
enum Mode {
    /// Simulate the program
    #[structopt(name = "sim")]
    Simulate {
        file: String,

        /// Enable optimizations
        #[structopt(short)]
        optimise: bool,

        /// Arguments to pass to the executed Porth program
        args: Vec<String>,
    },

    /// Compile the program
    #[structopt(name = "com")]
    Compile {
        file: String,

        /// Enable optimizations
        #[structopt(short)]
        optimise: bool,
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

fn generate_error(msg: impl Into<String>, location: SourceLocation) -> Diagnostic<FileId> {
    Diagnostic::error()
        .with_message(msg)
        .with_labels(vec![Label::primary(location.file_id, location.range())])
}

type LoadProgramResult = Result<Vec<Op>, Vec<Diagnostic<FileId>>>;

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

#[allow(clippy::too_many_arguments)]
fn load_program(
    source_store: &mut SourceStorage,
    interner: &mut Interners,
    file: &str,
    optimize: bool,
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
    let mut include_list = Vec::new();

    let mut ops = match opcode::parse_token(&mut macros, &tokens, interner, &mut include_list) {
        Ok(ops) => ops,
        Err(diags) => return Ok(Err(diags)),
    };

    let mut included_files = HashMap::new();

    while let Some((include_token, file)) = include_list.pop() {
        if included_files.contains_key(&file) {
            continue;
        }

        let file_name = interner.resolve_literal(file);

        let include_path = match search_includes(include_paths, file_name) {
            Some(path) => path,
            None => {
                let diag = Diagnostic::error()
                    .with_message(format!("include not found: `{}`", file_name))
                    .with_labels(vec![Label::primary(
                        include_token.location.file_id,
                        include_token.location.range(),
                    )]);
                return Ok(Err(vec![diag]));
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
                return Ok(Err(vec![diag]));
            }
        };

        let file_id = source_store.add(&include_path, &contents);

        let tokens = match lexer::lex_file(&contents, file_id, interner, source_store) {
            Ok(program) => program,
            Err(diag) => return Ok(Err(vec![diag])),
        };

        let ops = match opcode::parse_token(&mut macros, &tokens, interner, &mut include_list) {
            Ok(ops) => ops,
            Err(diags) => return Ok(Err(diags)),
        };

        included_files.insert(file, ops);
    }

    ops = opcode::expand_includes(&included_files, &ops);

    ops = match opcode::expand_macros(&macros, &ops) {
        Ok(ops) => ops,
        Err(diags) => return Ok(Err(diags)),
    };

    if optimize {
        ops = opcode::optimize(&ops, interner, source_store);
    }

    if let Err(diags) = opcode::generate_jump_labels(&mut ops) {
        return Ok(Err(diags));
    }

    if let Err(diags) = type_check::type_check(&ops, interner) {
        return Ok(Err(diags));
    }

    Ok(Ok(ops))
}

fn run_simulate(
    file: String,
    optimise: bool,
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
        optimise,
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

    if let Err(diag) = simulate::simulate_execute_program(&program, &interner, &program_args) {
        codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
    }

    Ok(())
}

fn run_compile(file: String, optimise: bool, include_paths: Vec<String>) -> Result<()> {
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
        optimise,
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

    println!("Compiling... to {}", output_asm.display());
    compile_new::compile_program(&program, &source_storage, &interner, &output_asm, optimise)?;

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
            optimise,
            args: program_args,
        } => run_simulate(file, optimise, program_args, args.include_paths)?,
        Mode::Compile { file, optimise } => run_compile(file, optimise, args.include_paths)?,
    }

    Ok(())
}
