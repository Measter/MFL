use std::{collections::VecDeque, ffi::OsStr, path::Path};

use ariadne::{Color, Label};
use color_eyre::eyre::{eyre, Context as _, Result};
use hashbrown::HashSet;
use lasso::Spur;
use tracing::debug_span;

use crate::{
    context::{Context, ItemId},
    diagnostics, lexer,
    source_file::{FileId, SourceLocation, Spanned, WithSpan},
    Args, Stores,
};

// mod passes;

const BUILTINS: &str = include_str!("builtins/builtins.mfl");

#[derive(Debug, PartialEq, Eq)]
pub enum ModuleQueueType {
    Root,
    Include(Spanned<Spur>),
}

pub fn load_program(ctx: &mut Context, stores: &mut Stores, args: &Args) -> Result<ItemId> {
    let _span = debug_span!(stringify!(Program::load_program)).entered();
    let mut had_error = false;

    let builtin_structs_module_name = stores.strings.intern("builtins");
    let builtin_module = ctx.new_module(
        stores,
        &mut had_error,
        builtin_structs_module_name.with_span(SourceLocation::new(FileId::dud(), 0..0)),
        None,
        true,
    );
    load_module(
        ctx,
        stores,
        builtin_module,
        Path::new("builtins"),
        BUILTINS,
        &mut VecDeque::new(),
    )?;

    let module_name = args.file.file_stem().and_then(OsStr::to_str).unwrap();
    let main_lib_root = args.file.parent().unwrap();
    let root_file_name = args.file.file_name().unwrap();
    let entry_module = load_library(
        ctx,
        stores,
        &mut had_error,
        module_name,
        root_file_name,
        main_lib_root,
    );

    for lib in &args.library_paths {
        let module_name = lib.file_stem().and_then(OsStr::to_str).unwrap();
        had_error |= load_library(
            ctx,
            stores,
            &mut had_error,
            module_name,
            OsStr::new("lib.mfl"),
            lib,
        )
        .is_err();
    }

    if had_error {
        return Err(eyre!("Error loading program"));
    }

    stores.types.update_builtins(ctx.get_lang_items());

    // self.post_process_items(stores, args.print_analyzer_stats)?;

    entry_module
}

fn load_library(
    ctx: &mut Context,
    stores: &mut Stores,
    had_error: &mut bool,
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
                        return Err(e)
                            .with_context(|| eyre!("failed to load `{}`", root.display()));
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
                        diagnostics::emit_error(
                            stores,
                            token.location,
                            format!("error loading module: {e}"),
                            [Label::new(token.location).with_color(Color::Red)],
                            None,
                        );
                        *had_error = true;
                        root.pop();
                        continue;
                    }
                };

                (contents, token)
            }
        };

        let module_id = ctx.new_module(
            stores,
            had_error,
            module_name,
            parent,
            module == ModuleQueueType::Root,
        );

        first_module = first_module.or(Some(module_id));
        let res = load_module(ctx, stores, module_id, &root, &contents, &mut module_queue);

        *had_error |= res.is_err();

        root.pop();
    }

    Ok(first_module.unwrap())
}

fn load_module(
    ctx: &mut Context,
    stores: &mut Stores,
    module_id: ItemId,
    file: &Path,
    file_contents: &str,
    include_queue: &mut VecDeque<(ModuleQueueType, Option<ItemId>)>,
) -> Result<()> {
    let file_type = format!("{file:?}");
    let _span = debug_span!(stringify!(Module::load), file_type).entered();

    let file_id = stores.source.add(file, file_contents);

    let tokens = lexer::lex_file(stores, file_contents, file_id)
        .map_err(|_| eyre!("error lexing file: {}", file.display()))?;

    let file_stem = Path::new(file).file_stem().and_then(OsStr::to_str).unwrap();
    stores.strings.intern(file_stem);

    crate::parser::parse_file(ctx, stores, module_id, &tokens, include_queue)
        .map_err(|_| eyre!("error parsing file: {}", file.display()))?;

    Ok(())
}

// // The self parameter is the source of this, but it makes more sense for it to be a method.
// #[allow(clippy::only_used_in_recursion)]
// fn determine_terminal_blocks_in_block(&self, block: &mut [Op]) -> bool {
//     for op in block {
//         match &mut op.code {
//             OpCode::If(if_block) => {
//                 if_block.is_condition_terminal =
//                     self.determine_terminal_blocks_in_block(&mut if_block.condition);
//                 if_block.is_then_terminal =
//                     self.determine_terminal_blocks_in_block(&mut if_block.then_block);
//                 if_block.is_else_terminal =
//                     self.determine_terminal_blocks_in_block(&mut if_block.else_block);
//             }
//             OpCode::While(while_block) => {
//                 self.determine_terminal_blocks_in_block(&mut while_block.condition);
//                 self.determine_terminal_blocks_in_block(&mut while_block.body_block);
//             }
//             OpCode::Return | OpCode::Exit => return true,
//             _ => {}
//         }
//     }

//     false
// }

// fn determine_terminal_blocks(&mut self, stores: &mut Stores) {
//     let _span = debug_span!(stringify!(Program::determine_terminal_blocks)).entered();
//     let items: Vec<_> = self
//         .item_headers
//         .iter()
//         .filter(|i| {
//             i.kind() != ItemKind::Memory
//                 && i.kind() != ItemKind::StructDef
//                 && i.kind() != ItemKind::Module
//         })
//         .map(|i| i.id)
//         .collect();

//     for item_id in items {
//         trace!(name = stores.strings.get_symbol_name(self, item_id));

//         let mut body = self.item_bodies.remove(&item_id).unwrap();
//         self.determine_terminal_blocks_in_block(&mut body);
//         self.item_bodies.insert(item_id, body);
//     }
// }

// fn analyze_data_flow(&mut self, stores: &mut Stores, print_analyzer_stats: bool) -> Result<()> {
//     let _span = debug_span!(stringify!(Program::analyze_data_flow)).entered();
//     let mut had_error = false;
//     let items: Vec<_> = self
//         .item_headers
//         .iter()
//         .filter(|i| {
//             i.kind() != ItemKind::Memory
//                 && i.kind() != ItemKind::StructDef
//                 && i.kind() != ItemKind::Module
//                 && i.kind() != ItemKind::GenericFunction
//         })
//         .map(|i| i.id)
//         .collect();

//     let mut stats_table = Table::new();
//     stats_table.set_format(*TABLE_FORMAT);
//     stats_table.set_titles(row!("Proc Name", "Stack Depth", "Value Count"));

//     for id in items {
//         let _span = trace_span!(
//             "Analyzing item",
//             name = stores.strings.get_symbol_name(self, id)
//         )
//         .entered();
//         let mut analyzer = Analyzer::default();

//         let res = static_analysis::analyze_item(self, stores, &mut analyzer, id);

//         let stats = match res {
//             Ok(s) => s,
//             Err(s) => {
//                 had_error = true;
//                 s
//             }
//         };

//         stats_table.add_row(row![
//             stores.strings.get_symbol_name(self, id),
//             stats.max_stack_depth,
//             stats.unique_item_count
//         ]);

//         self.analyzers.insert(id, analyzer);
//     }

//     if print_analyzer_stats {
//         println!("\n{stats_table}");
//     }

//     had_error
//         .not()
//         .then_some(())
//         .ok_or_else(|| eyre!("data analysis error"))
// }

// fn evaluate_const_items(&mut self, stores: &mut Stores) -> Result<()> {
//     let _span = debug_span!(stringify!(Program::evaluate_const_items)).entered();
//     let mut had_error = false;

//     let mut const_queue: Vec<_> = self
//         .item_headers
//         .iter()
//         .filter(|item| item.kind() == ItemKind::Const)
//         .map(|i| i.id)
//         .collect();
//     let mut next_run_queue = Vec::with_capacity(const_queue.len());

//     loop {
//         for const_id in const_queue.drain(..) {
//             let item_sig = self.get_item_signature_resolved(const_id);
//             match simulate_execute_program(self, stores, const_id) {
//                 Ok(stack) => {
//                     let const_vals = stack
//                         .into_iter()
//                         .zip(&item_sig.exit_stack)
//                         .map(|(val, ty)| {
//                             let expected_type = stores.types.get_type_info(*ty);
//                             let val = match val {
//                                 SimulatorValue::Int { kind, .. } => {
//                                     let TypeKind::Integer(int) = expected_type.kind else {
//                                         unreachable!()
//                                     };

//                                     SimulatorValue::Int {
//                                         width: int.width,
//                                         kind: kind.cast(int),
//                                     }
//                                 }
//                                 SimulatorValue::Bool(_) => val,
//                             };

//                             (*ty, val)
//                         })
//                         .collect();

//                     self.const_vals.insert(const_id, const_vals);
//                 }
//                 Err(SimulationError::UnsupportedOp) => {
//                     had_error = true;
//                 }
//                 Err(SimulationError::UnreadyConst) => {
//                     next_run_queue.push(const_id);
//                 }
//             }
//         }

//         if next_run_queue.is_empty() {
//             break;
//         }

//         std::mem::swap(&mut const_queue, &mut next_run_queue);
//     }

//     had_error
//         .not()
//         .then_some(())
//         .ok_or_else(|| eyre!("failed during const evaluation"))
// }

// fn check_asserts(&self, stores: &mut Stores) -> Result<()> {
//     let _span = debug_span!(stringify!(Program::check_asserts)).entered();
//     let mut had_error = false;

//     for &item in &self.item_headers {
//         if item.kind() != ItemKind::Assert {
//             continue;
//         }

//         let assert_result = match simulate_execute_program(self, stores, item.id) {
//             // Type check says we'll have a value at this point.
//             Ok(mut stack) => {
//                 let Some(SimulatorValue::Bool(val)) = stack.pop() else {
//                     panic!("ICE: Simulated assert returned non-bool");
//                 };
//                 val
//             }
//             Err(_) => {
//                 had_error = true;
//                 continue;
//             }
//         };

//         if !assert_result {
//             diagnostics::emit_error(
//                 stores,
//                 item.name.location,
//                 "assert failure",
//                 Some(
//                     Label::new(item.name.location)
//                         .with_color(Color::Red)
//                         .with_message("evaluated to false"),
//                 ),
//                 None,
//             );
//             had_error = true;
//         }
//     }

//     had_error
//         .not()
//         .then_some(())
//         .ok_or_else(|| eyre!("failed assert check"))
// }

// fn post_process_items(&mut self, stores: &mut Stores, print_analyzer_stats: bool) -> Result<()> {
//     let _span = debug_span!(stringify!(Program::post_process_items)).entered();
//     self.resolve_idents(stores)?;
//     self.instantiate_generic_functions(stores)?;
//     self.resolve_struct_defs(stores)?;
//     self.resolve_types(stores)?;

//     self.check_invalid_cyclic_refs(stores)?;

//     self.determine_terminal_blocks(stores);

//     self.analyze_data_flow(stores, print_analyzer_stats)?;
//     self.evaluate_const_items(stores)?;

//     self.process_idents(stores)?;
//     self.check_asserts(stores)?;

//     Ok(())
// }
