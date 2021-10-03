use std::{path::Path, process::Command};

use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    term::{
        termcolor::{ColorChoice, StandardStream, StandardStreamLock},
        Config,
    },
};
use color_eyre::eyre::{eyre, Context, Result};
use lasso::Rodeo;
use source_file::{FileId, SourceLocation, SourceStorage};
use structopt::StructOpt;

mod compile;
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
    Simulate { file: String },

    /// Compile the program
    #[structopt(name = "com")]
    Compile {
        file: String,

        /// run the output immediately
        #[structopt(long, short)]
        run: bool,
    },
}

fn generate_error(msg: impl Into<String>, location: SourceLocation) -> Diagnostic<FileId> {
    Diagnostic::error()
        .with_message(msg)
        .with_labels(vec![Label::primary(location.file_id, location.range())])
}

fn load_program(
    stderr: &mut StandardStreamLock,
    cfg: &Config,
    source_store: &mut SourceStorage,
    interner: &mut Rodeo,
    file: &str,
) -> Result<Result<Vec<Op>, Vec<Diagnostic<FileId>>>> {
    let contents =
        std::fs::read_to_string(file).with_context(|| eyre!("Failed to open file {}", file))?;

    let file_id = source_store.add(file, &contents);

    let tokens = match lexer::lex_file(&contents, file_id, interner) {
        Ok(program) => program,
        Err(diag) => return Ok(Err(vec![diag])),
    };

    let ops = match opcode::parse_token(&tokens) {
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

    let mut new_ops = opcode::optimize(&ops);

    if let Err(diags) = opcode::generate_jump_labels(&mut new_ops) {
        return Ok(Err(diags));
    }

    Ok(Ok(new_ops))
}

fn main() -> Result<()> {
    color_eyre::install()?;
    let args = Args::from_args();

    let cfg = codespan_reporting::term::Config::default();
    let stderr = StandardStream::stderr(ColorChoice::Always);
    let mut stderr = stderr.lock();

    let mut source_storage = SourceStorage::new();
    let mut interner = Rodeo::default();

    match args {
        Args::Simulate { file } => {
            let program =
                match load_program(&mut stderr, &cfg, &mut source_storage, &mut interner, &file)? {
                    Ok(program) => program,
                    Err(diags) => {
                        for diag in diags {
                            codespan_reporting::term::emit(
                                &mut stderr,
                                &cfg,
                                &source_storage,
                                &diag,
                            )?;
                        }
                        std::process::exit(-1);
                    }
                };
            if let Err(diag) = simulate::simulate_program(&program, &interner) {
                codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
            }
        }
        Args::Compile { file, run } => {
            let mut output_asm = Path::new(&file).to_path_buf();
            output_asm.set_extension("asm");
            let mut output_obj = output_asm.clone();
            output_obj.set_extension("o");
            let mut output_binary = output_obj.clone();
            output_binary.set_extension("");

            let program =
                match load_program(&mut stderr, &cfg, &mut source_storage, &mut interner, &file)? {
                    Ok(program) => program,
                    Err(diags) => {
                        for diag in diags {
                            codespan_reporting::term::emit(
                                &mut stderr,
                                &cfg,
                                &source_storage,
                                &diag,
                            )?;
                        }
                        std::process::exit(-1);
                    }
                };

            println!("Compiling... to {}", output_asm.display());
            compile::compile_program(&program, &source_storage, &interner, &output_asm)?;

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
