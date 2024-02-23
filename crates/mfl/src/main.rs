#![allow(clippy::too_many_arguments)]
#![warn(clippy::needless_pass_by_value, clippy::manual_let_else)]

use std::{
    path::{Path, PathBuf},
    process::Command,
};

use ariadne::{Color, Label};
use clap::Parser;
use color_eyre::{
    eyre::{eyre, Context as _, Result},
    owo_colors::OwoColorize,
};
use context::{Context, ItemId, ItemKind, TypeResolvedItemSignature};
use tracing::{debug, debug_span, Level};

use interners::Interner;
use source_file::SourceStorage;
use type_store::{BuiltinTypes, TypeStore};

mod backend_llvm;
mod context;
mod diagnostics;
mod interners;
mod ir;
mod lexer;
mod n_ops;
mod option;
mod parser;
mod pass_manager;
mod program;
mod simulate;
mod source_file;
mod type_store;

#[derive(Debug, Parser)]
pub struct Args {
    /// Print more to the console
    #[arg(short, action = clap::ArgAction::Count)]
    verbose: u8,

    /// Print the number of unique values, and the stack depth of procedures.
    #[arg(long = "value-stats")]
    print_analyzer_stats: bool,

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

pub struct Stores {
    source: SourceStorage,
    strings: Interner,
    types: TypeStore,
}

fn is_valid_entry_sig(stores: &mut Stores, entry_sig: &TypeResolvedItemSignature) -> bool {
    if !entry_sig.exit.is_empty() {
        return false;
    }

    if entry_sig.entry.is_empty() {
        return true;
    }

    let [argc_id, argv_id] = entry_sig.entry.as_slice() else {
        return false;
    };

    let expected_argc_id = stores.types.get_builtin(BuiltinTypes::U64).id;
    let u8_ptr_type = stores.types.get_builtin_ptr(BuiltinTypes::U8).id;
    let expected_argv_id = stores
        .types
        .get_pointer(&mut stores.strings, u8_ptr_type)
        .id;

    *argc_id == expected_argc_id && *argv_id == expected_argv_id
}

fn load_program(args: &Args) -> Result<(Context, Stores, Vec<ItemId>)> {
    let _span = debug_span!(stringify!(load_program)).entered();
    let source_storage = SourceStorage::new();
    let mut interner = Interner::new();
    let type_store = TypeStore::new(&mut interner);

    let mut stores = Stores {
        source: source_storage,
        strings: interner,
        types: type_store,
    };

    let mut context = Context::new();
    let entry_module_id = program::load_program(&mut context, &mut stores, args)?;

    let mut top_level_symbols = Vec::new();

    if args.is_library {
        let entry_scope = context.nrir().get_scope(entry_module_id);
        for &item_id in entry_scope.get_child_items().values() {
            let item_header = context.get_item_header(item_id.inner);
            if item_header.kind == ItemKind::Function {
                top_level_symbols.push(item_id.inner);
            }
        }
    } else {
        let entry_symbol = stores.strings.intern("entry");
        let entry_scope = context.nrir().get_scope(entry_module_id);

        let entry_function_id = entry_scope
            .get_symbol(entry_symbol)
            .ok_or_else(|| eyre!("`entry` function not found"))?;

        top_level_symbols.push(entry_function_id);

        debug!("checking entry signature");
        let entry_item = context.get_item_header(entry_function_id);
        if !matches!(entry_item.kind, ItemKind::Function) {
            let name = entry_item.name;
            diagnostics::emit_error(
                &stores,
                name.location,
                "`entry` must be a function",
                Some(
                    Label::new(name.location)
                        .with_color(Color::Red)
                        .with_message(format!("found `{:?}`", entry_item.kind)),
                ),
                None,
            );
            return Err(eyre!("invalid `entry` procedure type"));
        }

        let entry_sig = context.trir().get_item_signature(entry_function_id);
        if !is_valid_entry_sig(&mut stores, entry_sig) {
            let name = entry_item.name;
            diagnostics::emit_error(
                &stores,
                name.location,
                "`entry` must have the signature `[] to []` or `[u64 u8&&] to []`",
                Some(Label::new(name.location).with_color(Color::Red)),
                None,
            );
            return Err(eyre!("invalid `entry` signature"));
        }
    }

    Ok((context, stores, top_level_symbols))
}

fn run_compile(args: &Args) -> Result<()> {
    print!("   Compiling...");
    let (mut program, mut stores, top_level_items) = match load_program(args) {
        Ok(o) => o,
        Err(e) => {
            eprintln!();
            eprintln!("{}: unable to compile program", "Error".red());
            eprintln!("  Failed at stage: {e}");
            std::process::exit(-3);
        }
    };

    pass_manager::run(&mut program, &mut stores)?;

    let objects = backend_llvm::compile(&program, &mut stores, &top_level_items, args)?;

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
