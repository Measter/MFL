use std::ops::Not;

use ariadne::{Color, Label};
use color_eyre::{eyre::eyre, Result};
use smallvec::SmallVec;
use tracing::{debug_span, trace};

use crate::{
    diagnostics,
    interners::Interners,
    opcode::{Op, OpCode},
    program::{ItemKind, ItemSignatureResolved, Program},
    source_file::SourceStorage,
    type_store::{emit_type_error_diag, BuiltinTypes, TypeKind, TypeStore, UnresolvedType},
};

impl Program {
    pub fn resolve_struct_defs(
        &self,
        interner: &mut Interners,
        source_store: &SourceStorage,
        type_store: &mut TypeStore,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::check_self_referring_structs)).entered();
        let mut had_error = false;

        let struct_item_ids: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, hdr)| hdr.kind() == ItemKind::StructDef)
            .map(|(id, _)| *id)
            .collect();

        // First pass, we just declare the existance of all the structs.
        for &id in &struct_item_ids {
            let def = self.structs_unresolved.get(&id).unwrap();
            // We check if the name already exists by trying to resolve it.
            if let Ok(existing_info) = type_store.resolve_type(
                interner,
                &UnresolvedType::SimpleCustom {
                    id,
                    token: def.name,
                },
            ) {
                if let Some(loc) = existing_info.location {
                    // The user defined the type.
                    diagnostics::emit_error(
                        def.name.location,
                        "type with this name already exists",
                        [
                            Label::new(def.name.location).with_color(Color::Red),
                            Label::new(loc)
                                .with_color(Color::Cyan)
                                .with_message("already defined here"),
                        ],
                        None,
                        source_store,
                    );
                } else {
                    // It's a built-in type.
                    diagnostics::emit_error(
                        def.name.location,
                        "cannot define struct with the name of a primative",
                        [Label::new(def.name.location).with_color(Color::Red)],
                        None,
                        source_store,
                    );
                }

                had_error = true;
            };

            type_store.add_type(def.name.lexeme, def.name.location, TypeKind::Struct(id));
        }

        if had_error {
            return Err(eyre!("error defining structs"));
        }

        // Now we try to resolve the struct definition.
        for id in struct_item_ids {
            let def = self.structs_unresolved.get(&id).unwrap();
            if let Err(missing_token) = type_store.define_struct(interner, id, def) {
                // The type that failed to resolve is us.
                diagnostics::emit_error(
                    missing_token.location,
                    "undefined field type",
                    [
                        Label::new(missing_token.location).with_color(Color::Red),
                        Label::new(def.name.location)
                            .with_color(Color::Cyan)
                            .with_message("In this struct"),
                    ],
                    None,
                    source_store,
                );
                had_error = true;
                continue;
            }
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("self-referential struct check failed"))
    }

    // The self parameter is the source of this, but it makes more sense for it to be a method.
    #[allow(clippy::only_used_in_recursion)]
    pub fn resolve_types_in_block(
        &self,
        mut body: Vec<Op>,
        had_error: &mut bool,
        interner: &mut Interners,
        source_store: &SourceStorage,
        type_store: &mut TypeStore,
    ) -> Vec<Op> {
        for op in &mut body {
            match &mut op.code {
                OpCode::While(while_op) => {
                    let temp_body = std::mem::take(&mut while_op.condition);
                    while_op.condition = self.resolve_types_in_block(
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        type_store,
                    );
                    let temp_body = std::mem::take(&mut while_op.body_block);
                    while_op.body_block = self.resolve_types_in_block(
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        type_store,
                    );
                }
                OpCode::If(if_op) => {
                    // Mmmm.. repetition...
                    let temp_body = std::mem::take(&mut if_op.condition);
                    if_op.condition = self.resolve_types_in_block(
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        type_store,
                    );
                    let temp_body = std::mem::take(&mut if_op.then_block);
                    if_op.then_block = self.resolve_types_in_block(
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        type_store,
                    );
                    let temp_body = std::mem::take(&mut if_op.else_block);
                    if_op.else_block = self.resolve_types_in_block(
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        type_store,
                    );
                }

                OpCode::UnresolvedCast { unresolved_type } => {
                    let type_info = match type_store.resolve_type(interner, unresolved_type) {
                        Ok(info) => info,
                        Err(err_token) => {
                            emit_type_error_diag(err_token, interner, source_store);

                            *had_error = true;
                            continue;
                        }
                    };

                    op.code = OpCode::ResolvedCast { id: type_info.id };
                }
                OpCode::UnresolvedPackStruct { unresolved_type } => {
                    let type_info = match type_store.resolve_type(interner, unresolved_type) {
                        Ok(info) => info,
                        Err(err_token) => {
                            emit_type_error_diag(err_token, interner, source_store);

                            *had_error = true;
                            continue;
                        }
                    };

                    op.code = OpCode::PackStruct { id: type_info.id };
                }
                OpCode::UnresolvedSizeOf { unresolved_type } => {
                    let type_info = match type_store.resolve_type(interner, unresolved_type) {
                        Ok(info) => info,
                        Err(err_token) => {
                            emit_type_error_diag(err_token, interner, source_store);

                            *had_error = true;
                            continue;
                        }
                    };

                    op.code = OpCode::SizeOf(type_info.id);
                }

                _ => {}
            }
        }

        body
    }

    pub fn resolve_types(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
        type_store: &mut TypeStore,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::resolve_types)).entered();
        let mut had_error = false;

        let items = self
            .item_headers
            .iter()
            .filter(|(_, item)| item.kind != ItemKind::StructDef && item.kind != ItemKind::Module)
            .map(|(id, item)| (*id, *item));

        for (item_id, item) in items {
            trace!(name = interner.get_symbol_name(self, item_id));

            let unresolved_sig = &self.item_signatures_unresolved[&item_id];

            let mut resolved_entry = SmallVec::with_capacity(unresolved_sig.entry_stack.len());
            let mut resolved_exit = SmallVec::with_capacity(unresolved_sig.exit_stack.len());
            let mut resolved_memory_type = None;

            if item.kind == ItemKind::Memory {
                resolved_exit.push(type_store.get_builtin(BuiltinTypes::U64).id);
                let info = match type_store.resolve_type(interner, unresolved_sig.memory_type()) {
                    Ok(info) => info,
                    Err(tk) => {
                        had_error = true;
                        emit_type_error_diag(tk, interner, source_store);
                        continue;
                    }
                };
                resolved_memory_type = Some(info.id);
            } else {
                for (input_sig, _) in unresolved_sig.entry_stack() {
                    let info = match type_store.resolve_type(interner, input_sig) {
                        Ok(info) => info,
                        Err(tk) => {
                            had_error = true;
                            emit_type_error_diag(tk, interner, source_store);
                            continue;
                        }
                    };
                    resolved_entry.push(info.id);
                }

                for (input_sig, _) in unresolved_sig.exit_stack() {
                    let info = match type_store.resolve_type(interner, input_sig) {
                        Ok(info) => info,
                        Err(tk) => {
                            had_error = true;
                            emit_type_error_diag(tk, interner, source_store);
                            continue;
                        }
                    };
                    resolved_exit.push(info.id);
                }
            }

            self.item_signatures_resolved.insert(
                item_id,
                ItemSignatureResolved {
                    entry_stack: resolved_entry,
                    exit_stack: resolved_exit,
                    memory_type: resolved_memory_type,
                },
            );

            if item.kind != ItemKind::Memory {
                let body = self.item_bodies.remove(&item_id).unwrap();
                self.item_bodies.insert(
                    item_id,
                    self.resolve_types_in_block(
                        body,
                        &mut had_error,
                        interner,
                        source_store,
                        type_store,
                    ),
                );
            }
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error during type resolution"))
    }
}
