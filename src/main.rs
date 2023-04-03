#![allow(clippy::too_many_arguments)]

use std::{
    path::{Path, PathBuf},
    process::Command,
};

use ariadne::{Color, Label};
use clap::Parser;
use color_eyre::eyre::{eyre, Context, Result};
use tracing::{debug, debug_span};
use tracing_subscriber::prelude::__tracing_subscriber_SubscriberExt;

use interners::Interners;
use program::{ItemId, ItemKind, Program};
use source_file::SourceStorage;
use type_store::TypeStore;

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
mod type_store;

#[derive(Debug, Parser)]
pub struct Args {
    /// Print more to the console
    #[arg(short, action = clap::ArgAction::Count)]
    verbose: u8,

    /// Print the maximum depth of the stack in each procedure.
    #[arg(long = "stack-depth")]
    print_stack_depths: bool,

    /// Comma-separated list of library paths.
    #[arg(short = 'L', value_delimiter = ',')]
    library_paths: Vec<PathBuf>,

    /// The MFL file to compile
    file: PathBuf,

    #[arg(long = "lib")]
    is_library: bool,

    /// Directory storing the intermediate .o files.
    #[arg(long = "obj", default_value = "./obj")]
    obj_dir: PathBuf,

    /// Path to write the output binary.
    #[arg(short = 'o')]
    output: Option<PathBuf>,

    /// Enable optimizations.
    #[arg(short = 'O')]
    optimize: bool,

    /// Emit assembly
    #[arg(long = "emit-asm")]
    emit_asm: bool,
}

fn load_program(
    args: &Args,
) -> Result<(Program, SourceStorage, Interners, TypeStore, Vec<ItemId>)> {
    let _span = debug_span!(stringify!(load_program)).entered();
    let mut source_storage = SourceStorage::new();
    let mut interner = Interners::new();
    let mut type_store = TypeStore::new(&mut interner);

    let mut program = Program::new();
    let entry_module_id =
        program.load_program2(&mut interner, &mut source_storage, &mut type_store, args)?;

    let mut top_level_symbols = Vec::new();

    if args.is_library {
        let module_info = program.get_module(entry_module_id);
        for &item_id in module_info.top_level_symbols().values() {
            let item_header = program.get_item_header(item_id);
            if item_header.kind() == ItemKind::Function {
                top_level_symbols.push(item_id);
            }
        }
    } else {
        let entry_symbol = interner.intern_lexeme("entry");
        let entry_module = program.get_module(entry_module_id);

        let entry_function_id = entry_module
            .get_item_id(entry_symbol)
            .ok_or_else(|| eyre!("`entry` function not found"))?;

        top_level_symbols.push(entry_function_id);

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
    }

    Ok((
        program,
        source_storage,
        interner,
        type_store,
        top_level_symbols,
    ))
}

fn run_compile(args: Args) -> Result<()> {
    let (program, _source_storage, mut interner, mut type_store, entry_function) =
        load_program(&args)?;

    let objects = backend_llvm::compile(
        &program,
        entry_function,
        &mut interner,
        &mut type_store,
        &args,
    )?;

    if args.is_library {
        return Ok(());
    }

    let output_path = args.output.clone().unwrap();

    println!("Linking... into {}", output_path.display());
    let ld = Command::new("ld")
        .arg("-o")
        .arg(&output_path)
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
    let mut args = Args::parse();

    // let max_log_level = match args.verbose {
    //     0 => Level::WARN,
    //     1 => Level::INFO,
    //     2 => Level::DEBUG,
    //     _ => Level::TRACE,
    // };

    let tracer = opentelemetry_jaeger::new_agent_pipeline()
        .with_service_name("mfl")
        .install_simple()?;
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    let subscriber = tracing_subscriber::Registry::default().with(telemetry);

    tracing::subscriber::set_global_default(subscriber)?;

    {
        let _span = debug_span!("main").entered();

        args.output = args.output.or_else(|| {
            let mut output_binary = Path::new(&args.file).to_path_buf();
            output_binary.set_extension("");
            Some(output_binary)
        });
        run_compile(args)?;
    }

    opentelemetry::global::shutdown_tracer_provider();

    Ok(())
}
