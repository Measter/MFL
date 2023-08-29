use std::ops::Not;

use ariadne::{Color, Label};
use color_eyre::{eyre::eyre, Result};
use smallvec::SmallVec;
use tracing::{debug_span, trace};

use crate::{
    diagnostics,
    opcode::{Op, OpCode},
    program::{ItemKind, ItemSignatureResolved, Program},
    type_store::{emit_type_error_diag, TypeKind, UnresolvedTypeIds},
    Stores,
};

impl Program {
    pub fn resolve_struct_defs(&self, stores: &mut Stores) -> Result<()> {
        let _span = debug_span!(stringify!(Program::check_self_referring_structs)).entered();
        let mut had_error = false;

        let struct_item_ids: Vec<_> = self
            .item_headers
            .iter()
            .filter(|i| i.kind() == ItemKind::StructDef)
            .map(|i| i.id)
            .collect();

        let mut generic_structs = Vec::new();

        // First pass, we just declare the existance of all the structs.
        for &id in &struct_item_ids {
            let def = self.structs_unresolved.get(&id).unwrap();
            // We check if the name already exists by trying to resolve it.
            if let Ok(existing_info) = stores.types.resolve_type(
                &mut stores.strings,
                &UnresolvedTypeIds::SimpleCustom {
                    id,
                    token: def.name,
                },
            ) {
                if let Some(loc) = existing_info.location {
                    // The user defined the type.
                    diagnostics::emit_error(
                        stores,
                        def.name.location,
                        "type with this name already exists",
                        [
                            Label::new(def.name.location).with_color(Color::Red),
                            Label::new(loc)
                                .with_color(Color::Cyan)
                                .with_message("already defined here"),
                        ],
                        None,
                    );
                } else {
                    // It's a built-in type.
                    diagnostics::emit_error(
                        stores,
                        def.name.location,
                        "cannot define struct with the name of a primative",
                        [Label::new(def.name.location).with_color(Color::Red)],
                        None,
                    );
                }

                had_error = true;
            };

            if def.generic_params.is_some() {
                generic_structs.push(id);
                stores.types.add_type(
                    def.name.inner,
                    def.name.location,
                    TypeKind::GenericStructBase(id),
                );
            } else {
                stores
                    .types
                    .add_type(def.name.inner, def.name.location, TypeKind::Struct(id));
            }
        }

        if had_error {
            return Err(eyre!("error defining structs"));
        }

        for id in generic_structs {
            let def = self.structs_unresolved.get(&id).unwrap();
            stores
                .types
                .partially_resolve_generic_struct(&mut stores.strings, id, def);
        }

        // Now we try to resolve the struct definition.
        for id in struct_item_ids {
            let def = self.structs_unresolved.get(&id).unwrap();
            if def.generic_params.is_some() {
                continue;
            }

            if let Err(missing_token) =
                stores
                    .types
                    .define_fixed_struct(&mut stores.strings, id, def)
            {
                // The type that failed to resolve is us.
                diagnostics::emit_error(
                    stores,
                    missing_token.location,
                    "undefined field type",
                    [
                        Label::new(missing_token.location).with_color(Color::Red),
                        Label::new(def.name.location)
                            .with_color(Color::Cyan)
                            .with_message("In this struct"),
                    ],
                    None,
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
        stores: &mut Stores,
        had_error: &mut bool,
        mut body: Vec<Op>,
    ) -> Vec<Op> {
        for op in &mut body {
            match &mut op.code {
                OpCode::While(while_op) => {
                    let temp_body = std::mem::take(&mut while_op.condition);
                    while_op.condition = self.resolve_types_in_block(stores, had_error, temp_body);
                    let temp_body = std::mem::take(&mut while_op.body_block);
                    while_op.body_block = self.resolve_types_in_block(stores, had_error, temp_body);
                }
                OpCode::If(if_op) => {
                    // Mmmm.. repetition...
                    let temp_body = std::mem::take(&mut if_op.condition);
                    if_op.condition = self.resolve_types_in_block(stores, had_error, temp_body);
                    let temp_body = std::mem::take(&mut if_op.then_block);
                    if_op.then_block = self.resolve_types_in_block(stores, had_error, temp_body);
                    let temp_body = std::mem::take(&mut if_op.else_block);
                    if_op.else_block = self.resolve_types_in_block(stores, had_error, temp_body);
                }

                OpCode::UnresolvedCast { unresolved_type } => {
                    let type_info = match stores
                        .types
                        .resolve_type(&mut stores.strings, unresolved_type.as_id())
                    {
                        Ok(info) => info,
                        Err(err_token) => {
                            emit_type_error_diag(stores, err_token);

                            *had_error = true;
                            continue;
                        }
                    };

                    op.code = OpCode::ResolvedCast { id: type_info.id };
                }
                OpCode::UnresolvedPackStruct { unresolved_type } => {
                    let type_info = match stores
                        .types
                        .resolve_type(&mut stores.strings, unresolved_type.as_id())
                    {
                        Ok(info) => info,
                        Err(err_token) => {
                            emit_type_error_diag(stores, err_token);

                            *had_error = true;
                            continue;
                        }
                    };

                    op.code = OpCode::PackStruct { id: type_info.id };
                }
                OpCode::UnresolvedSizeOf { unresolved_type } => {
                    let type_info = match stores
                        .types
                        .resolve_type(&mut stores.strings, unresolved_type.as_id())
                    {
                        Ok(info) => info,
                        Err(err_token) => {
                            emit_type_error_diag(stores, err_token);

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

    pub fn resolve_types(&mut self, stores: &mut Stores) -> Result<()> {
        let _span = debug_span!(stringify!(Program::resolve_types)).entered();
        let mut had_error = false;

        let items = self.item_headers.iter().filter(|item| {
            item.kind != ItemKind::StructDef
                && item.kind != ItemKind::Module
                && item.kind != ItemKind::GenericFunction
        });

        for item in items {
            trace!(name = stores.strings.get_symbol_name(self, item.id));

            if item.kind == ItemKind::Memory {
                let parent_kind = self.get_item_header(item.parent.unwrap()).kind;
                if parent_kind == ItemKind::GenericFunction {
                    // We don't process these.
                    continue;
                }

                let unresolved_memory_type = &self.memory_type_unresolved[&item.id];

                let info = match stores
                    .types
                    .resolve_type(&mut stores.strings, unresolved_memory_type.inner.as_id())
                {
                    Ok(info) => info,
                    Err(tk) => {
                        had_error = true;
                        emit_type_error_diag(stores, tk);
                        continue;
                    }
                };

                self.memory_type_resolved.insert(item.id, info.id);
            } else {
                let unresolved_sig = &self.item_signatures_unresolved[&item.id];
                let mut resolved_entry =
                    SmallVec::with_capacity(unresolved_sig.entry_stack.inner.len());
                let mut resolved_exit =
                    SmallVec::with_capacity(unresolved_sig.exit_stack.inner.len());

                for input_sig in unresolved_sig.entry_stack() {
                    let info = match stores
                        .types
                        .resolve_type(&mut stores.strings, input_sig.inner.as_id())
                    {
                        Ok(info) => info,
                        Err(tk) => {
                            had_error = true;
                            emit_type_error_diag(stores, tk);
                            continue;
                        }
                    };
                    resolved_entry.push(info.id);
                }

                for output_sig in unresolved_sig.exit_stack() {
                    let info = match stores
                        .types
                        .resolve_type(&mut stores.strings, output_sig.inner.as_id())
                    {
                        Ok(info) => info,
                        Err(tk) => {
                            had_error = true;
                            emit_type_error_diag(stores, tk);
                            continue;
                        }
                    };
                    resolved_exit.push(info.id);
                }

                self.item_signatures_resolved.insert(
                    item.id,
                    ItemSignatureResolved {
                        entry_stack: resolved_entry,
                        exit_stack: resolved_exit,
                    },
                );

                let body = self.item_bodies.remove(&item.id).unwrap();
                self.item_bodies.insert(
                    item.id,
                    self.resolve_types_in_block(stores, &mut had_error, body),
                );
            }
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error during type resolution"))
    }
}
