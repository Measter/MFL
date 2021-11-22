#![allow(clippy::too_many_arguments)]

use std::{path::Path, process::Command};

use color_eyre::eyre::{eyre, Context, Result};
use interners::Interners;
use program::Program;
use source_file::SourceStorage;
use structopt::StructOpt;

mod compile;
mod diagnostics;
mod interners;
mod lexer;
mod n_ops;
mod opcode;
mod program;
mod simulate;
mod source_file;
mod type_check;

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

fn run_simulate(
    file: String,
    opt_level: u8,
    mut program_args: Vec<String>,
    include_paths: Vec<String>,
) -> Result<()> {
    let mut source_storage = SourceStorage::new();
    let mut interner = Interners::new();

    program_args.insert(0, file.clone()); // We need the program name to be part of the args.

    let program = Program::load(
        &mut source_storage,
        &mut interner,
        &file,
        opt_level,
        &include_paths,
    )
    .with_context(|| eyre!("failed to load program"))?;

    let top_level_proc = program.get_proc(program.top_level_proc_id());

    simulate::simulate_execute_program(
        &program,
        top_level_proc,
        &interner,
        &program_args,
        &source_storage,
    )
    .map_err(|_| eyre!("failed to simulate program"))?;

    Ok(())
}

fn run_compile(file: String, opt_level: u8, include_paths: Vec<String>) -> Result<()> {
    let mut source_storage = SourceStorage::new();
    let mut interner = Interners::new();

    let mut output_asm = Path::new(&file).to_path_buf();
    output_asm.set_extension("asm");
    let mut output_obj = output_asm.clone();
    output_obj.set_extension("o");
    let mut output_binary = output_obj.clone();
    output_binary.set_extension("");

    let program = Program::load(
        &mut source_storage,
        &mut interner,
        &file,
        opt_level,
        &include_paths,
    )
    .with_context(|| eyre!("failed to load program"))?;

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
