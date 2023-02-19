#![allow(clippy::too_many_arguments)]

use std::{path::Path, process::Command};

use ariadne::{Color, Label};
use clap::Parser;
use color_eyre::eyre::{eyre, Context, Result};
use tracing::{debug, debug_span};
use tracing_subscriber::prelude::__tracing_subscriber_SubscriberExt;

use interners::Interners;
use program::{ItemId, ItemKind, Program};
use source_file::SourceStorage;

mod backend_llvm;
mod diagnostics;
mod interners;
mod lexer;
mod n_ops;
mod opcode;
mod option;
mod program;
mod simulate;
mod source_file;

#[derive(Debug, Parser)]
struct Args {
    /// Print more to the console
    #[arg(short, action = clap::ArgAction::Count)]
    verbose: u8,

    /// Comma-separated list of paths to search includes.
    #[arg(short = 'I', value_delimiter = ',')]
    library_paths: Vec<String>,

    file: String,

    /// Set optimization level
    #[arg(short, action = clap::ArgAction::Count)]
    opt_level: u8,
}

fn load_program(
    file: &str,
    include_paths: Vec<String>,
) -> Result<(Program, SourceStorage, Interners, ItemId)> {
    let _span = debug_span!(stringify!(load_program)).entered();
    let mut source_storage = SourceStorage::new();
    let mut interner = Interners::new();

    let mut program = Program::new();
    let entry_module_id =
        program.load_program(file, &mut interner, &mut source_storage, &include_paths)?;

    let entry_symbol = interner.intern_lexeme("entry");
    let entry_module = program.get_module(entry_module_id);

    let entry_function_id = entry_module
        .get_item_id(entry_symbol)
        .ok_or_else(|| eyre!("`entry` function not found"))?;

    debug!("checking entry signature");
    let entry_item = program.get_item_header(entry_function_id);
    if !matches!(entry_item.kind(), ItemKind::Function) {
        let name = entry_item.name();
        diagnostics::emit_error(
            name.location,
            "`entry` must be a function",
            Some(
                Label::new(name.location)
                    .with_color(Color::Red)
                    .with_message(format!("found `{:?}`", entry_item.kind())),
            ),
            None,
            &source_storage,
        );
        return Err(eyre!("invalid `entry` procedure type"));
    }

    let entry_sig = program.get_item_signature_resolved(entry_function_id);
    if !entry_sig.entry_stack().is_empty() || !entry_sig.exit_stack().is_empty() {
        let name = entry_item.name();
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
    let mut output_binary = Path::new(&file).to_path_buf();
    output_binary.set_extension("");

    let (program, _source_storage, mut interner, entry_function) =
        load_program(&file, include_paths)?;

    let objects = backend_llvm::compile(&program, entry_function, &mut interner, &file, opt_level)?;

    println!("Linking... into {}", output_binary.display());
    let ld = Command::new("ld")
        .arg("-o")
        .arg(&output_binary)
        .args(&objects)
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

    // let max_log_level = match args.verbose {
    //     0 => Level::WARN,
    //     1 => Level::INFO,
    //     2 => Level::DEBUG,
    //     _ => Level::TRACE,
    // };

    let tracer = opentelemetry_jaeger::new_agent_pipeline()
        .with_service_name("porth")
        .install_simple()?;
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    let subscriber = tracing_subscriber::Registry::default().with(telemetry);

    tracing::subscriber::set_global_default(subscriber)?;

    {
        let _span = debug_span!("porth main").entered();
        run_compile(args.file, args.opt_level, args.library_paths)?;
    }

    opentelemetry::global::shutdown_tracer_provider();

    Ok(())
}
