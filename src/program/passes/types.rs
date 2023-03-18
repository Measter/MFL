use std::ops::Not;

use color_eyre::{eyre::eyre, Result};
use smallvec::SmallVec;
use tracing::{debug_span, trace};

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{ItemKind, ItemSignatureResolved, Program},
    source_file::SourceStorage,
    type_store::{BuiltinTypes, TypeStore},
};

impl Program {
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
                    let Some(type_info) = type_store.resolve_type(interner, source_store, unresolved_type) else {
                        *had_error = true;
                        continue;
                    };

                    op.code = OpCode::ResolvedCast { id: type_info.id };
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
            .filter(|(_, item)| item.kind != ItemKind::StructDef)
            .map(|(id, item)| (*id, *item));

        for (item_id, item) in items {
            trace!(name = interner.get_symbol_name(self, item_id));

            let unresolved_sig = &self.item_signatures_unresolved[&item_id];

            let mut resolved_entry = SmallVec::with_capacity(unresolved_sig.entry_stack.len());
            let mut resolved_exit = SmallVec::with_capacity(unresolved_sig.exit_stack.len());
            let mut resolved_memory_type = None;

            if item.kind == ItemKind::Memory {
                resolved_exit.push(type_store.get_builtin(BuiltinTypes::U64).id);
                let Some(info) = type_store.resolve_type(interner, source_store, unresolved_sig.memory_type()) else {
                    had_error = true;
                    continue;
                };
                resolved_memory_type = Some(info.id);
            } else {
                for input_sig in unresolved_sig.entry_stack() {
                    let Some(info) = type_store.resolve_type(interner, source_store, input_sig) else {
                        had_error = true;
                        continue;
                    };
                    resolved_entry.push(info.id);
                }

                for input_sig in unresolved_sig.exit_stack() {
                    let Some(info) = type_store.resolve_type(interner, source_store, input_sig) else {
                        had_error = true;
                        continue;
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
