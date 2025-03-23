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

use ::stores::{items::ItemId, source::SourceStore, strings::StringStore};
use clap::Parser;
use color_eyre::{
    eyre::{eyre, Context as _, Result},
    owo_colors::OwoColorize,
};
use tracing::{debug, debug_span, Level};

use stores::{
    block::BlockStore,
    diagnostics::{Diagnostic, DiagnosticStore},
    item::{ItemAttribute, ItemKind, ItemStore},
    ops::OpStore,
    signatures::SigStore,
    types::{BuiltinTypes, TypeStore},
    values::ValueStore,
    Stores,
};

mod backend_llvm;
mod error_signal;
mod ir;
mod lexer;
mod n_ops;
mod option;
mod parser;
mod pass_manager;
mod program;
mod simulate;
mod stores;
mod timer;

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

    #[arg(long = "time-passes")]
    time_passes: bool,
}

fn is_valid_entry_sig(stores: &mut Stores, item_id: ItemId) -> bool {
    let header = stores.items.get_item_header(item_id);
    if header.attributes.contains(ItemAttribute::TrackCaller) {
        return false;
    }

    let entry_sig = stores.sigs.trir.get_item_signature(item_id);
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
    let u8_ptr_type = stores.types.get_multi_pointer(stores.strings, u8_type.id);
    let u8_ptr_ptr_type = stores
        .types
        .get_multi_pointer(stores.strings, u8_ptr_type.id);

    *argc_id == expected_argc_id && *argv_id == u8_ptr_ptr_type.id
}

fn load_program(stores: &mut Stores, args: &Args) -> Result<Vec<ItemId>> {
    let _span = debug_span!(stringify!(load_program)).entered();

    let entry_module_id = program::load_program(stores, args)?;

    pass_manager::run(stores, args.print_analyzer_stats)?;

    let mut top_level_symbols = Vec::new();

    if args.is_library {
        let entry_scope = stores.sigs.nrir.get_scope(entry_module_id);
        for &item_id in entry_scope.get_child_items() {
            let item_header = stores.items.get_item_header(item_id);
            if item_header.kind == ItemKind::Function
                && item_header.attributes.contains(ItemAttribute::Extern)
            {
                top_level_symbols.push(item_id);
            }
        }
    } else {
        let entry_symbol = stores.strings.intern("entry");
        let entry_scope = stores.sigs.nrir.get_scope(entry_module_id);

        let entry_function_id = entry_scope
            .get_symbol(entry_symbol)
            .ok_or_else(|| eyre!("`entry` function not found"))?;

        top_level_symbols.push(entry_function_id);

        debug!("checking entry signature");
        let entry_item = stores.items.get_item_header(entry_function_id);
        if !matches!(entry_item.kind, ItemKind::Function) {
            let name = entry_item.name;

            Diagnostic::error(name.location, "`entry` must be a function")
                .primary_label_message(format!("found `{:?}", entry_item.kind))
                .attached(stores.diags, entry_item.id);

            return Err(eyre!("invalid `entry` procedure type"));
        }

        if !is_valid_entry_sig(stores, entry_function_id) {
            let name = entry_item.name;
            Diagnostic::error(
                name.location,
                "`entry` must have the signature `[] to []` or `[u64 u8&&] to []`, and cannot track_caller",
            )
            .attached(stores.diags, entry_item.id);

            return Err(eyre!("invalid `entry` signature"));
        }
    }

    Ok(top_level_symbols)
}

fn run_compile(args: &Args) -> Result<()> {
    let mut source_storage = SourceStore::new();
    let mut string_store = StringStore::new();
    let mut type_store = TypeStore::new(&mut string_store);
    let mut op_store = OpStore::new();
    let mut block_store = BlockStore::new();
    let mut value_store = ValueStore::new();
    let mut sig_store = SigStore::new();
    let mut item_store = ItemStore::new(&mut string_store, &mut sig_store, &mut type_store);
    let mut diag_store = DiagnosticStore::new();
    let timer = timer::Timer::new(args.time_passes);

    let mut stores = Stores {
        source: &mut source_storage,
        strings: &mut string_store,
        types: &mut type_store,
        ops: &mut op_store,
        blocks: &mut block_store,
        values: &mut value_store,
        items: &mut item_store,
        sigs: &mut sig_store,
        diags: &mut diag_store,
        timer: &timer,
    };

    print!("   Compiling...");

    let loaded_program = load_program(&mut stores, args);
    stores.display_diags();
    let top_level_items = match loaded_program {
        Ok(o) => o,
        Err(e) => {
            eprintln!();
            eprintln!("{}: unable to compile program", "Error".red());
            eprintln!("  Failed at stage: {e}");
            std::process::exit(-3);
        }
    };

    let mut objects = {
        let _start = stores.timer.start_compile();
        backend_llvm::compile(&mut stores, &top_level_items, args)?
    };
    objects.extend(args.addition_obj_paths.iter().cloned());

    if args.is_library {
        println!(" {}", "Finished".green());
        return Ok(());
    }

    let output_path = args.output.clone().unwrap();

    let ld = {
        let _start = stores.timer.start_link();
        Command::new("gcc")
            .arg("-o")
            .arg(&output_path)
            .args(&objects)
            .status()
            .with_context(|| eyre!("Failed to link"))?
    };

    if args.time_passes {
        stores.timer.print();
    }

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
