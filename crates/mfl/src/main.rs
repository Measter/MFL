#![allow(clippy::too_many_arguments)]
#![warn(
    clippy::manual_let_else,
    clippy::redundant_else,
    clippy::unnested_or_patterns,
    clippy::uninlined_format_args,
    clippy::match_same_arms
)]

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
use item_store::{ItemStore, ItemAttribute, ItemId, ItemKind, TypeResolvedItemSignature};
use tracing::{debug, debug_span, Level};

use stores::{types::BuiltinTypes, Stores};

mod backend_llvm;
mod diagnostics;
mod error_signal;
mod ir;
mod item_store;
mod lexer;
mod n_ops;
mod option;
mod parser;
mod pass_manager;
mod program;
mod simulate;
mod stores;

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

    /// Comma-separated list of library paths.
    #[arg(short = 'l', value_delimiter = ',')]
    addition_obj_paths: Vec<PathBuf>,

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
    let u8_type = stores.types.get_builtin(BuiltinTypes::U8);
    let u8_ptr_type = stores
        .types
        .get_multi_pointer(&mut stores.strings, u8_type.id);
    let u8_ptr_ptr_type = stores
        .types
        .get_multi_pointer(&mut stores.strings, u8_ptr_type.id);

    *argc_id == expected_argc_id && *argv_id == u8_ptr_ptr_type.id
}

fn load_program(args: &Args) -> Result<(ItemStore, Stores, Vec<ItemId>)> {
    let _span = debug_span!(stringify!(load_program)).entered();
    let mut stores = Stores::new();

    let mut item_store = ItemStore::new();
    let entry_module_id = program::load_program(&mut item_store, &mut stores, args)?;

    pass_manager::run(&mut item_store, &mut stores, args.print_analyzer_stats)?;

    let mut top_level_symbols = Vec::new();

    if args.is_library {
        let entry_scope = item_store.nrir().get_scope(entry_module_id);
        for &item_id in entry_scope.get_child_items().values() {
            let item_header = item_store.get_item_header(item_id.inner);
            if item_header.kind == ItemKind::Function
                && item_header.attributes.contains(ItemAttribute::Extern)
            {
                top_level_symbols.push(item_id.inner);
            }
        }
    } else {
        let entry_symbol = stores.strings.intern("entry");
        let entry_scope = item_store.nrir().get_scope(entry_module_id);

        let entry_function_id = entry_scope
            .get_symbol(entry_symbol)
            .ok_or_else(|| eyre!("`entry` function not found"))?;

        top_level_symbols.push(entry_function_id);

        debug!("checking entry signature");
        let entry_item = item_store.get_item_header(entry_function_id);
        if !matches!(entry_item.kind, ItemKind::Function { .. }) {
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

        let entry_sig = item_store.trir().get_item_signature(entry_function_id);
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

    Ok((item_store, stores, top_level_symbols))
}

fn run_compile(args: &Args) -> Result<()> {
    print!("   Compiling...");
    let (ctx, mut stores, top_level_items) = match load_program(args) {
        Ok(o) => o,
        Err(e) => {
            eprintln!();
            eprintln!("{}: unable to compile program", "Error".red());
            eprintln!("  Failed at stage: {e}");
            std::process::exit(-3);
        }
    };

    let mut objects = backend_llvm::compile(&ctx, &mut stores, &top_level_items, args)?;
    objects.extend(args.addition_obj_paths.iter().cloned());

    if args.is_library {
        println!(" {}", "Finished".green());
        return Ok(());
    }

    let output_path = args.output.clone().unwrap();

    let ld = Command::new("gcc")
        .arg("-o")
        .arg(&output_path)
        .args(&objects)
        .status()
        .with_context(|| eyre!("Failed to link"))?;

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
