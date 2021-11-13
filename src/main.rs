#![allow(clippy::too_many_arguments)]

use std::{path::Path, process::Command};

use codespan_reporting::{
    diagnostic::Diagnostic,
    term::termcolor::{ColorChoice, StandardStream},
};
use color_eyre::eyre::{eyre, Context, Result};
use interners::Interners;
use program::Program;
use source_file::{FileId, SourceStorage};
use structopt::StructOpt;

// mod compile;
mod compile;
mod interners;
mod lexer;
mod n_ops;
mod opcode;
mod program;
mod simulate;
mod source_file;
mod type_check;

use opcode::AllocData;
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

fn evaluate_allocation_sizes(
    program: &mut Program,
    interner: &Interners,
) -> Result<(), Vec<Diagnostic<FileId>>> {
    let mut diags = Vec::new();

    for (&id, proc) in &program.global.allocs {
        let mut stack = match simulate_execute_program(program, proc, interner, &[]) {
            Err(diag) => {
                diags.push(diag);
                continue;
            }
            Ok(stack) => stack,
        };

        // The type checker enforces a single stack item here.
        let size = stack.pop().unwrap() as usize;
        let alloc_data = AllocData {
            size,
            offset: program.global.total_alloc_size,
        };
        program.global.alloc_size_and_offsets.insert(id, alloc_data);
        program.global.total_alloc_size += size;
    }

    let proc_ids: Vec<_> = program.procedures.keys().copied().collect();
    for proc_id in proc_ids {
        let mut proc = program.procedures.remove(&proc_id).unwrap();
        for (alloc_id, alloc) in &proc.allocs {
            let mut stack = match simulate_execute_program(program, alloc, interner, &[]) {
                Err(diag) => {
                    diags.push(diag);
                    continue;
                }
                Ok(stack) => stack,
            };

            // The type checker enforces a single stack item here.
            let size = stack.pop().unwrap() as usize;
            let alloc_data = AllocData {
                size,
                offset: proc.total_alloc_size,
            };
            proc.alloc_size_and_offsets.insert(*alloc_id, alloc_data);
            proc.total_alloc_size += size;
        }

        program.procedures.insert(proc_id, proc);
    }

    diags.is_empty().then(|| ()).ok_or(diags)
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

    let mut program = match Program::load(
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

    if let Err(diags) = evaluate_allocation_sizes(&mut program, &interner) {
        for diag in diags {
            codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
        }
        std::process::exit(-1);
    }

    if let Err(diag) =
        simulate::simulate_execute_program(&program, &program.global, &interner, &program_args)
    {
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

    let mut program = match Program::load(
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

    if let Err(diags) = evaluate_allocation_sizes(&mut program, &interner) {
        for diag in diags {
            codespan_reporting::term::emit(&mut stderr, &cfg, &source_storage, &diag)?;
        }
        std::process::exit(-1);
    }

    println!("Compiling... to {}", output_asm.display());
    compile::compile_program(&program, &source_storage, &interner, &output_asm, opt_level)?;

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
