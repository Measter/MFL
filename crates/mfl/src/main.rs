#![allow(clippy::too_many_arguments)]
#![warn(clippy::needless_pass_by_value, clippy::manual_let_else)]

use std::{
    path::{Path, PathBuf},
    process::Command,
};

use ariadne::{Color, Label};
use clap::Parser;
use color_eyre::{
    eyre::{eyre, Context, Result},
    owo_colors::OwoColorize,
};
use tracing::{debug, debug_span, Level};

use interners::Interner;
use program::{ItemId, ItemKind, ItemSignatureResolved, Program};
use source_file::SourceStorage;
use type_store::{BuiltinTypes, TypeStore};

mod backend_llvm;
mod diagnostics;
mod interners;
mod lexer;
mod n_ops;
mod opcode;
mod option;
mod parser;
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

    /// Emit LLIR
    #[arg(long = "emit-llir")]
    emit_llir: bool,
}

fn is_valid_entry_sig(
    interner: &mut Interner,
    type_store: &mut TypeStore,
    entry_sig: &ItemSignatureResolved,
) -> bool {
    if !entry_sig.exit_stack().is_empty() {
        return false;
    }

    if entry_sig.entry_stack().is_empty() {
        return true;
    }

    let [argc_id, argv_id] = entry_sig.entry_stack() else { return false };

    let expected_argc_id = type_store.get_builtin(BuiltinTypes::U64).id;
    let u8_ptr_type = type_store.get_builtin_ptr(BuiltinTypes::U8).id;
    let expected_argv_id = type_store.get_pointer(interner, u8_ptr_type).id;

    *argc_id == expected_argc_id && *argv_id == expected_argv_id
}

fn load_program(args: &Args) -> Result<(Program, SourceStorage, Interner, TypeStore, Vec<ItemId>)> {
    let _span = debug_span!(stringify!(load_program)).entered();
    let mut source_storage = SourceStorage::new();
    let mut interner = Interner::new();
    let mut type_store = TypeStore::new(&mut interner);

    let mut program = Program::new();
    let entry_module_id =
        program.load_program2(&mut interner, &mut source_storage, &mut type_store, args)?;

    let mut top_level_symbols = Vec::new();

    if args.is_library {
        let entry_scope = program.get_scope(entry_module_id);
        for &item_id in entry_scope.get_child_items().values() {
            let item_header = program.get_item_header(item_id.inner);
            if item_header.kind() == ItemKind::Function {
                top_level_symbols.push(item_id.inner);
            }
        }
    } else {
        let entry_symbol = interner.intern("entry");
        let entry_scope = program.get_scope(entry_module_id);

        let entry_function_id = entry_scope
            .get_symbol(entry_symbol)
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
        if !is_valid_entry_sig(&mut interner, &mut type_store, entry_sig) {
            let name = entry_item.name();
            diagnostics::emit_error(
                name.location,
                "`entry` must have the signature `[] to []` or `[u64 ptr(ptr(u8))] to []`",
                Some(Label::new(name.location).with_color(Color::Red)),
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

fn run_compile(args: &Args) -> Result<()> {
    print!("   Compiling...");
    let (program, source_storage, mut interner, mut type_store, top_level_items) =
        load_program(args)?;

    let objects = backend_llvm::compile(
        &program,
        &top_level_items,
        &source_storage,
        &mut interner,
        &mut type_store,
        args,
    )?;

    if args.is_library {
        println!(" {}", "Finished".green());
        return Ok(());
    }

    let output_path = args.output.clone().unwrap();

    let ld = Command::new("ld")
        .arg("-o")
        .arg(&output_path)
        .args(&objects)
        .status()
        .with_context(|| eyre!("Failed to execude ld"))?;

    if !ld.success() {
        std::process::exit(-3);
    }
    println!(" {}", "Finished".green());

    Ok(())
}

fn main() -> Result<()> {
    color_eyre::install()?;
    let mut args = Args::parse();

    let max_log_level = match args.verbose {
        0 => Level::WARN,
        1 => Level::INFO,
        2 => Level::DEBUG,
        _ => Level::TRACE,
    };

    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_max_level(max_log_level)
        .finish();

    tracing::subscriber::set_global_default(subscriber)?;

    {
        let _span = debug_span!("main").entered();

        args.output = args.output.or_else(|| {
            let mut output_binary = Path::new(&args.file).to_path_buf();
            output_binary.set_extension("");
            Some(output_binary)
        });
        run_compile(&args)?;
    }

    Ok(())
}
