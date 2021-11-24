#![allow(clippy::too_many_arguments)]

use std::{path::Path, process::Command};

use ariadne::{Color, Label};
use color_eyre::eyre::{eyre, Context, Result};
use interners::Interners;
use lasso::Interner;
use program::{Module, ModuleId, ProcedureId};
use source_file::SourceStorage;
use structopt::StructOpt;

use crate::program::{ProcedureKind, Program};

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
    Compile {},
}

#[derive(Debug, StructOpt)]
struct Args {
    /// Comma-separated list of paths to search includes.
    #[structopt(short = "I", require_delimiter = true)]
    library_paths: Vec<String>,

    file: String,

    /// Set optimization level
    #[structopt(short, parse(from_occurrences))]
    opt_level: u8,
}

fn load_program(
    file: &str,
    opt_level: u8,
    include_paths: Vec<String>,
) -> Result<(Program, SourceStorage, Interners, ModuleId, ProcedureId)> {
    let mut source_storage = SourceStorage::new();
    let mut interner = Interners::new();

    let mut program = Program::new();
    let entry_module_id = program
        .load_program(
            &file,
            &mut interner,
            &mut source_storage,
            opt_level,
            &include_paths,
        )
        .with_context(|| eyre!("failude to load program"))?;

    // TODO: Get program entry function.
    let entry_symbol = interner.intern_lexeme("entry");
    let entry_module = program.get_module(entry_module_id);

    let entry_function_id = entry_module
        .get_proc_id(entry_symbol)
        .ok_or_else(|| eyre!("`entry` function not found"))?;

    let entry_proc = program.get_proc(entry_function_id);
    if !matches!(entry_proc.kind(), ProcedureKind::Function(_)) {
        let name = entry_proc.name();
        diagnostics::emit(
            name.location,
            "`entry` must be a function",
            Some(
                Label::new(name.location)
                    .with_color(Color::Red)
                    .with_message(format!("found `{:?}`", entry_proc.kind())),
            ),
            None,
            &source_storage,
        );
        return Err(eyre!("invalid `entry` procedure type"));
    }

    Ok((
        program,
        source_storage,
        interner,
        entry_module_id,
        entry_function_id,
    ))
}

fn run_compile(file: String, opt_level: u8, include_paths: Vec<String>) -> Result<()> {
    let mut output_asm = Path::new(&file).to_path_buf();
    output_asm.set_extension("asm");
    let mut output_obj = output_asm.clone();
    output_obj.set_extension("o");
    let mut output_binary = output_obj.clone();
    output_binary.set_extension("");

    let (program, source_storage, interner, entry_module, entry_function) =
        load_program(&file, opt_level, include_paths)?;

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

    run_compile(args.file, args.opt_level, args.library_paths)?;

    Ok(())
}
