#![allow(clippy::too_many_arguments)]

use std::{path::Path, process::Command};

use ariadne::{Color, Label};
use clap::Parser;
use color_eyre::eyre::{eyre, Context, Result};
use interners::Interners;
use log::{info, Level, LevelFilter};
use program::ProcedureId;
use simplelog::{ConfigBuilder, TermLogger};
use source_file::SourceStorage;

use crate::program::{ProcedureKind, Program};

mod compile;
mod diagnostics;
mod interners;
mod lexer;
mod n_ops;
mod opcode;
mod option;
mod program;
mod simulate;
mod source_file;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Width {
    Byte,
    Word,
    Dword,
    Qword,
}

impl Width {
    pub fn byte_size(self) -> u64 {
        match self {
            Width::Byte => 1,
            Width::Word => 2,
            Width::Dword => 4,
            Width::Qword => 8,
        }
    }
}

#[derive(Debug, Parser)]
struct Args {
    /// Print more to the console
    #[clap(short, parse(from_occurrences))]
    verbose: u8,

    /// Comma-separated list of paths to search includes.
    #[clap(short = 'I', require_value_delimiter = true)]
    library_paths: Vec<String>,

    file: String,

    /// Set optimization level
    #[clap(short, parse(from_occurrences))]
    opt_level: u8,
}

fn load_program(
    file: &str,
    include_paths: Vec<String>,
) -> Result<(Program, SourceStorage, Interners, ProcedureId)> {
    let mut source_storage = SourceStorage::new();
    let mut interner = Interners::new();

    let mut program = Program::new();
    let entry_module_id =
        program.load_program(file, &mut interner, &mut source_storage, &include_paths)?;

    let entry_symbol = interner.intern_lexeme("entry");
    let entry_module = program.get_module(entry_module_id);

    let entry_function_id = entry_module
        .get_proc_id(entry_symbol)
        .ok_or_else(|| eyre!("`entry` function not found"))?;

    let entry_proc = program.get_proc(entry_function_id);
    if !matches!(entry_proc.kind(), ProcedureKind::Function(_)) {
        let name = entry_proc.name();
        diagnostics::emit_error(
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

    if !entry_proc.entry_stack().is_empty() || !entry_proc.exit_stack().is_empty() {
        let name = entry_proc.name();
        diagnostics::emit_error(
            name.location,
            "`entry` must have the signature `[] to []`",
            Some(
                Label::new(name.location)
                    .with_color(Color::Red)
                    .with_message("defined Here"),
            ),
            None,
            &source_storage,
        );
        return Err(eyre!("invalid `entry` signature"));
    }

    Ok((program, source_storage, interner, entry_function_id))
}

fn run_compile(file: String, opt_level: u8, include_paths: Vec<String>) -> Result<()> {
    let mut output_asm = Path::new(&file).to_path_buf();
    output_asm.set_extension("asm");
    let mut output_obj = output_asm.clone();
    output_obj.set_extension("o");
    let mut output_binary = output_obj.clone();
    output_binary.set_extension("");

    let (program, source_storage, mut interner, entry_function) =
        load_program(&file, include_paths)?;

    info!("Compiling... to {}", output_asm.display());
    compile::compile_program(
        &program,
        entry_function,
        &source_storage,
        &mut interner,
        &output_asm,
        opt_level,
    )?;

    info!("Assembling... to {}", output_obj.display());
    let nasm = Command::new("nasm")
        .arg("-felf64")
        .arg(&output_asm)
        .status()
        .with_context(|| eyre!("Failed to execute nasm"))?;
    if !nasm.success() {
        std::process::exit(-2);
    }

    info!("Linking... into {}", output_binary.display());
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
    let args = Args::parse();
    let log_level = match args.verbose {
        0 => LevelFilter::Warn,
        1 => LevelFilter::Info,
        2 => LevelFilter::Debug,
        _ => LevelFilter::Trace,
    };

    let config = ConfigBuilder::new()
        .set_time_level(LevelFilter::Off)
        .set_level_padding(simplelog::LevelPadding::Right)
        .set_target_level(LevelFilter::Off)
        .set_thread_level(LevelFilter::Off)
        .set_location_level(LevelFilter::Error)
        .set_level_color(Level::Trace, Some(simplelog::Color::Green))
        .build();

    TermLogger::init(
        log_level,
        config,
        simplelog::TerminalMode::Stderr,
        simplelog::ColorChoice::Always,
    )?;

    run_compile(args.file, args.opt_level, args.library_paths)?;

    Ok(())
}
