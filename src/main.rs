use std::{collections::HashMap, path::Path, process::Command};

use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    term::{
        termcolor::{ColorChoice, StandardStream, StandardStreamLock},
        Config,
    },
};
use color_eyre::eyre::{eyre, Context, Result};
use interners::Interners;
use source_file::{FileId, SourceLocation, SourceStorage};
use structopt::StructOpt;

mod compile;
mod interners;
mod lexer;
mod opcode;
mod popn;
mod simulate;
mod source_file;

use opcode::Op;

const MEMORY_CAPACITY: usize = 2usize.pow(19);

#[derive(Debug, StructOpt)]
enum Args {
    /// Simulate the program
    #[structopt(name = "sim")]
    Simulate {
        file: String,

        /// Enable optimizations
        #[structopt(short)]
        optimise: bool,
    },

    /// Compile the program
    #[structopt(name = "com")]
    Compile {
        file: String,

        /// run the output immediately
        #[structopt(long, short)]
        run: bool,

        /// Enable optimizations
        #[structopt(short)]
        optimise: bool,
    },
}

fn generate_error(msg: impl Into<String>, location: SourceLocation) -> Diagnostic<FileId> {
    Diagnostic::error()
        .with_message(msg)
        .with_labels(vec![Label::primary(location.file_id, location.range())])
}

type LoadProgramResult = Result<Vec<Op>, Vec<Diagnostic<FileId>>>;

fn load_program(
    stderr: &mut StandardStreamLock,
    cfg: &Config,
    source_store: &mut SourceStorage,
    interner: &mut Interners,
    file: &str,
    optimize: bool,
) -> Result<LoadProgramResult> {
    let contents =
        std::fs::read_to_string(file).with_context(|| eyre!("Failed to open file {}", file))?;

    let file_id = source_store.add(file, &contents);

    let tokens = match lexer::lex_file(&contents, file_id, interner) {
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

        let file_path = interner.resolve_literal(file);
        let contents = match std::fs::read_to_string(file_path) {
            Ok(contents) => contents,
            Err(e) => {
                let diag = Diagnostic::error()
                    .with_message(format!("error opening `{}`", file_path))
                    .with_labels(vec![Label::primary(
                        include_token.location.file_id,
                        include_token.location.range(),
                    )])
                    .with_notes(vec![format!("{}", e)]);
                return Ok(Err(vec![diag]));
            }
        };

        let file_id = source_store.add(file_path, &contents);

        let tokens = match lexer::lex_file(&contents, file_id, interner) {
            Ok(program) => program,
            Err(diag) => return Ok(Err(vec![diag])),
        };

        let ops = match opcode::parse_token(&mut macros, &tokens, interner, &mut include_list) {
            Ok(ops) => ops,
            Err(diags) => return Ok(Err(diags)),
        };

        included_files.insert(file, ops);
    }

    ops = match opcode::expand_macros(&included_files, &macros, &ops) {
        Ok(ops) => ops,
        Err(diags) => return Ok(Err(diags)),
    };

    match opcode::check_stack(&ops) {
        Err(diags) => return Ok(Err(diags)),
        Ok(warnings) => {
            for warning in warnings {
                codespan_reporting::term::emit(stderr, cfg, source_store, &warning)?;
            }
        }
    }

    if optimize {
        ops = opcode::optimize(&ops);
    }

    if let Err(diags) = opcode::generate_jump_labels(&mut ops) {
        return Ok(Err(diags));
    }

    Ok(Ok(ops))
}

fn main() -> Result<()> {
    color_eyre::install()?;
    let args = Args::from_args();

    let cfg = codespan_reporting::term::Config::default();
    let stderr = StandardStream::stderr(ColorChoice::Always);
    let mut stderr = stderr.lock();

    let mut source_storage = SourceStorage::new();
    let mut interner = Interners::new();

    match args {
        Args::Simulate { file, optimise } => {
            let program = match load_program(
                &mut stderr,
                &cfg,
                &mut source_storage,
                &mut interner,
                &file,
                optimise,
            )? {
                Ok(program) => program,
                Err(diags) => {
                    for diag in diags {
                        codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
                    }
                    std::process::exit(-1);
                }
            };
            if let Err(diag) = simulate::simulate_program(&program, &interner) {
                codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
            }
        }
        Args::Compile {
            file,
            run,
            optimise,
        } => {
            let mut output_asm = Path::new(&file).to_path_buf();
            output_asm.set_extension("asm");
            let mut output_obj = output_asm.clone();
            output_obj.set_extension("o");
            let mut output_binary = output_obj.clone();
            output_binary.set_extension("");

            let program = match load_program(
                &mut stderr,
                &cfg,
                &mut source_storage,
                &mut interner,
                &file,
                optimise,
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
            compile::compile_program(&program, &source_storage, &interner, &output_asm, optimise)?;

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

            if run {
                println!("Running...");
                let bin = Command::new(&output_binary)
                    .status()
                    .with_context(|| eyre!("Failed to run {}", output_binary.display()))?;

                if !bin.success() {
                    std::process::exit(-4);
                }
            }
        }
    }

    Ok(())
}
