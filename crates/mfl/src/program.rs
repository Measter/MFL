use std::{collections::VecDeque, ffi::OsStr, path::Path};

use color_eyre::eyre::{eyre, Report, Result};
use hashbrown::HashSet;
use lasso::Spur;
use stores::{
    items::ItemId,
    source::{FileId, SourceLocation, Spanned, WithSpan},
};
use tracing::debug_span;

use crate::{error_signal::ErrorSignal, lexer, stores::diagnostics::Diagnostic, Args, Stores};

// mod passes;

const BUILTINS: &str = include_str!("builtins/builtins.mfl");

#[derive(Debug, PartialEq, Eq)]
pub enum ModuleQueueType {
    Root,
    Include(Spanned<Spur>),
}

pub fn load_program(stores: &mut Stores, args: &Args) -> Result<ItemId> {
    let _span = debug_span!(stringify!(Program::load_program)).entered();
    let mut had_error = ErrorSignal::new();

    let core_module_name = stores.strings.intern("core");
    let core_module = stores.items.new_module(
        stores.sigs,
        core_module_name.with_span(SourceLocation::new(FileId::dud(), 0..0)),
        None,
        true,
    );
    stores.items.set_core_module(core_module);

    let builtin_structs_module_name = stores.strings.intern("builtins");
    let builtin_module = stores.items.new_module(
        stores.sigs,
        builtin_structs_module_name.with_span(SourceLocation::new(FileId::dud(), 0..0)),
        None,
        true,
    );

    if let Err(e) = load_module(
        stores,
        builtin_module,
        Path::new("builtins"),
        BUILTINS,
        &mut VecDeque::new(),
    ) {
        had_error.forget();
        return Err(e);
    }

    let module_name = args.file.file_stem().and_then(OsStr::to_str).unwrap();
    let main_lib_root = args.file.parent().unwrap();
    let root_file_name = args.file.file_name().unwrap();
    let entry_module = load_library(
        stores,
        &mut had_error,
        module_name,
        root_file_name,
        main_lib_root,
    );

    for lib in &args.library_paths {
        let module_name = lib.file_stem().and_then(OsStr::to_str).unwrap();
        let res = load_library(
            stores,
            &mut had_error,
            module_name,
            OsStr::new("lib.mfl"),
            lib,
        )
        .is_err();

        if res {
            had_error.set();
        }
    }

    if had_error.into_err() {
        return Err(eyre!("Error loading program"));
    }

    stores.items.update_core_symbols(stores.sigs);
    stores.types.update_builtins(stores.items.get_lang_items());

    entry_module
}

fn load_library(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    lib_name: &str,
    lib_filename: &OsStr,
    lib_path: &Path,
) -> Result<ItemId> {
    let mut loaded_modules = HashSet::new();
    let mut module_queue = VecDeque::new();

    let mut root = lib_path.to_owned();

    module_queue.push_back((ModuleQueueType::Root, None));

    let mut first_module = None;
    while let Some((module, parent)) = module_queue.pop_front() {
        let (contents, module_name) = match module {
            ModuleQueueType::Root => {
                root.push(lib_filename);

                let contents = match std::fs::read_to_string(&root) {
                    Ok(c) => c,
                    Err(e) => {
                        let err =
                            Report::new(e).wrap_err(eyre!("failed to read `{}`", root.display()));
                        eprintln!("{err:?}");
                        return Err(err);
                    }
                };
                (
                    contents,
                    stores
                        .strings
                        .intern(lib_name)
                        .with_span(SourceLocation::new(FileId::dud(), 0..0)),
                )
            }
            ModuleQueueType::Include(token) => {
                if loaded_modules.contains(&token.inner) {
                    continue;
                }
                loaded_modules.insert(token.inner);

                let name = stores.strings.resolve(token.inner);
                root.push(name);
                root.set_extension("mfl");

                let contents = match std::fs::read_to_string(&root) {
                    Ok(c) => c,
                    Err(e) => {
                        let diag =
                            Diagnostic::error(token.location, format!("error loading module: {e}"));
                        if let Some(parent) = parent {
                            diag.attached(stores.diags, parent);
                        } else {
                            diag.detached(stores.diags);
                        }

                        had_error.set();
                        root.pop();
                        continue;
                    }
                };

                (contents, token)
            }
        };

        let module_id = stores.items.new_module(
            stores.sigs,
            module_name,
            parent,
            module == ModuleQueueType::Root,
        );

        first_module = first_module.or(Some(module_id));
        let res = load_module(stores, module_id, &root, &contents, &mut module_queue);

        if res.is_err() {
            had_error.set();
        }

        root.pop();
    }

    Ok(first_module.unwrap())
}

fn load_module(
    stores: &mut Stores,
    module_id: ItemId,
    file: &Path,
    file_contents: &str,
    include_queue: &mut VecDeque<(ModuleQueueType, Option<ItemId>)>,
) -> Result<()> {
    let file_type = format!("{file:?}");
    let _span = debug_span!(stringify!(Module::load), file_type).entered();

    let file_id = stores.source.add(file, file_contents);

    let tokens = {
        let _start = stores.timer.start_lex();
        lexer::lex_file(stores, file_contents, file_id)
            .map_err(|_| eyre!("error lexing file: {}", file.display()))?
    };

    let file_stem = Path::new(file).file_stem().and_then(OsStr::to_str).unwrap();
    stores.strings.intern(file_stem);

    let _start = stores.timer.start_parse();
    crate::parser::parse_module(stores, module_id, &tokens, include_queue)
        .map_err(|_| eyre!("error parsing file: {}", file.display()))?;

    Ok(())
}
