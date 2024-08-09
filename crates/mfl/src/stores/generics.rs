use hashbrown::HashMap;
use lasso::Spur;
use stores::{items::ItemId, source::WithSpan};
use tracing::{debug_span, trace};

use crate::{
    error_signal::ErrorSignal,
    ir::{Basic, Control, If, OpCode, PartiallyResolvedOp, TypeResolvedOp, While},
    pass_manager::{PassManager, PassState},
    stores::signatures::{
        NameResolvedItemSignature, StackDefItemNameResolved, TypeResolvedItemSignature,
    },
};

use super::{block::BlockId, item::ItemKind, types::TypeId, Stores};

impl Stores<'_, '_, '_, '_, '_, '_, '_, '_> {
    fn expand_generic_params_in_block(
        &mut self,
        pass_manager: &mut PassManager,
        had_error: &mut ErrorSignal,
        block_id: BlockId,
        param_map: &HashMap<Spur, TypeId>,
        old_alloc_map: &HashMap<ItemId, ItemId>,
    ) -> BlockId {
        let mut new_body = Vec::new();

        let old_block = self.blocks.get_block(block_id).clone();
        for op_id in old_block.ops {
            let op_code = self.ops.get_partially_type_resolved(op_id).clone();
            let new_code = match op_code {
                OpCode::Basic(bo) => match bo {
                    Basic::Control(Control::If(if_op)) => {
                        let resolved_condition = self.expand_generic_params_in_block(
                            pass_manager,
                            had_error,
                            if_op.condition,
                            param_map,
                            old_alloc_map,
                        );
                        let resolved_then = self.expand_generic_params_in_block(
                            pass_manager,
                            had_error,
                            if_op.then_block,
                            param_map,
                            old_alloc_map,
                        );
                        let resolved_else = self.expand_generic_params_in_block(
                            pass_manager,
                            had_error,
                            if_op.else_block,
                            param_map,
                            old_alloc_map,
                        );
                        OpCode::Basic(Basic::Control(Control::If(If {
                            tokens: if_op.tokens,
                            condition: resolved_condition,
                            then_block: resolved_then,
                            else_block: resolved_else,
                        })))
                    }
                    Basic::Control(Control::While(while_op)) => {
                        let resolved_condition = self.expand_generic_params_in_block(
                            pass_manager,
                            had_error,
                            while_op.condition,
                            param_map,
                            old_alloc_map,
                        );
                        let resolved_body = self.expand_generic_params_in_block(
                            pass_manager,
                            had_error,
                            while_op.body_block,
                            param_map,
                            old_alloc_map,
                        );

                        OpCode::Basic(Basic::Control(Control::While(While {
                            tokens: while_op.tokens,
                            condition: resolved_condition,
                            body_block: resolved_body,
                        })))
                    }
                    _ => OpCode::Basic(bo),
                },
                OpCode::Complex(co) => match co {
                    ref op_code @ (PartiallyResolvedOp::Cast { ref id }
                    | PartiallyResolvedOp::PackStruct { ref id }
                    | PartiallyResolvedOp::SizeOf { ref id }) => {
                        let new_id = self.types.resolve_generic_type(self.strings, id, param_map);
                        match op_code {
                            PartiallyResolvedOp::Cast { .. } => {
                                OpCode::Complex(TypeResolvedOp::Cast { id: new_id })
                            }
                            PartiallyResolvedOp::PackStruct { .. } => {
                                OpCode::Complex(TypeResolvedOp::PackStruct { id: new_id })
                            }
                            PartiallyResolvedOp::SizeOf { .. } => {
                                OpCode::Complex(TypeResolvedOp::SizeOf { id: new_id })
                            }
                            _ => unreachable!(),
                        }
                    }

                    PartiallyResolvedOp::Const { id } => {
                        OpCode::Complex(TypeResolvedOp::Const { id })
                    }
                    PartiallyResolvedOp::Variable { id, is_global } => {
                        let id = if let Some(new_id) = old_alloc_map.get(&id) {
                            *new_id
                        } else {
                            id
                        };
                        OpCode::Complex(TypeResolvedOp::Variable { id, is_global })
                    }

                    PartiallyResolvedOp::CallFunction { id, generic_params } => {
                        let new_params: Vec<_> = generic_params
                            .iter()
                            .map(|gp| self.types.resolve_generic_type(self.strings, gp, param_map))
                            .collect();

                        let header = self.items.get_item_header(id);
                        let callee_id = if header.kind != ItemKind::GenericFunction {
                            id
                        } else if !new_params.is_empty() {
                            self.get_generic_function_instance(
                                pass_manager,
                                had_error,
                                id,
                                &new_params,
                            )
                            .unwrap()
                            //
                        } else {
                            // No parameters were provided, figure it out in type check.
                            id
                        };

                        OpCode::Complex(TypeResolvedOp::CallFunction {
                            id: callee_id,
                            generic_params: new_params,
                        })
                    }

                    PartiallyResolvedOp::AssumeInit { id } => {
                        let id = if let Some(new_id) = old_alloc_map.get(&id) {
                            *new_id
                        } else {
                            id
                        };
                        OpCode::Complex(TypeResolvedOp::AssumeInit { id })
                    }
                },
            };

            let old_token = self.ops.get_token(op_id);
            let mut old_unresolved = self.ops.get_unresolved(op_id).clone();
            // Need to patch up the old unresolved opcode so that the If and While codes point to the new blocks.
            match (&mut old_unresolved, &new_code) {
                (
                    OpCode::Basic(Basic::Control(Control::If(old_if))),
                    OpCode::Basic(Basic::Control(Control::If(new_if))),
                ) => {
                    old_if.condition = new_if.condition;
                    old_if.then_block = new_if.then_block;
                    old_if.else_block = new_if.else_block;
                }
                (
                    OpCode::Basic(Basic::Control(Control::While(old_while))),
                    OpCode::Basic(Basic::Control(Control::While(new_while))),
                ) => {
                    old_while.condition = new_while.condition;
                    old_while.body_block = new_while.body_block
                }
                _ => {}
            }

            let new_op_id = self.ops.new_op(old_unresolved, old_token);
            self.ops.set_type_resolved(new_op_id, new_code);

            new_body.push(new_op_id);
        }

        self.blocks.new_block(new_body)
    }

    fn instantiate_variables(
        &mut self,
        base_fn_id: ItemId,
        new_proc_id: ItemId,
        pass_manager: &mut PassManager,
        had_error: &mut ErrorSignal,
        param_map: &HashMap<Spur, TypeId>,
    ) -> HashMap<ItemId, ItemId> {
        let base_scope = self.sigs.nrir.get_scope(base_fn_id).clone();
        let mut old_alloc_map = HashMap::new();
        for (&child_name, &child_item) in base_scope.get_child_items() {
            let child_item_header = self.items.get_item_header(child_item.inner);
            if child_item_header.kind != ItemKind::Variable {
                // We just reuse the existing item, so we need to add it manually.
                let new_scope = self.sigs.nrir.get_scope_mut(new_proc_id);
                new_scope
                    .add_child(child_name.with_span(child_item.location), child_item.inner)
                    .unwrap();
                continue;
            }

            if pass_manager
                .ensure_type_resolved_signature(self, child_item_header.id)
                .is_err()
            {
                had_error.set();
                continue;
            }

            let alloc_type_unresolved = self.sigs.urir.get_variable_type(child_item_header.id);
            let (new_alloc_id, redef_err_loc) = self.items.new_variable(
                self.sigs,
                had_error,
                child_item_header.name,
                new_proc_id,
                child_item_header.attributes,
                alloc_type_unresolved.map(|i| i.clone()),
            );
            // This should be been picked up by the base def.
            assert!(redef_err_loc.is_none());

            let alloc_type = self
                .sigs
                .trir
                .get_partial_variable_type(child_item_header.id);
            let new_variable_sig =
                self.types
                    .resolve_generic_type(self.strings, alloc_type, param_map);
            self.sigs
                .trir
                .set_variable_type(new_alloc_id, new_variable_sig);
            pass_manager.add_new_item(
                new_alloc_id,
                child_item_header.id,
                PassState::IdentResolvedSignature | PassState::TypeResolvedSignature,
            );

            old_alloc_map.insert(child_item_header.id, new_alloc_id);
        }
        old_alloc_map
    }

    fn type_resolve_generic_signature(
        &mut self,
        base_fn_id: ItemId,
        resolved_generic_params: &[TypeId],
        param_map: &HashMap<Spur, TypeId>,
    ) -> TypeResolvedItemSignature {
        let partial_type_resolved_sig = self.sigs.trir.get_partial_item_signature(base_fn_id);
        let mut instantiated_sig = TypeResolvedItemSignature {
            exit: Vec::new(),
            entry: Vec::new(),
            generic_params: resolved_generic_params.to_owned(),
        };

        for stack_item in &partial_type_resolved_sig.exit {
            // let new_id = self.expand_generic_params_in_type(stack_item, &param_map);
            let new_id = self
                .types
                .resolve_generic_type(self.strings, stack_item, param_map);
            instantiated_sig.exit.push(new_id);
        }

        for stack_item in &partial_type_resolved_sig.entry {
            let new_id = self
                .types
                .resolve_generic_type(self.strings, stack_item, param_map);
            instantiated_sig.entry.push(new_id);
        }
        instantiated_sig
    }

    fn create_name_resolved_signature(
        &mut self,
        base_fn_id: ItemId,
        old_alloc_map: &HashMap<ItemId, ItemId>,
    ) -> NameResolvedItemSignature {
        let orig_name_resolved_sig = self.sigs.nrir.get_item_signature(base_fn_id).clone();
        let mut new_name_resolved_sig = NameResolvedItemSignature {
            exit: orig_name_resolved_sig.exit.clone(),
            entry: Vec::new(),
            generic_params: orig_name_resolved_sig.generic_params.clone(),
        };

        for entry in orig_name_resolved_sig.entry {
            let new_entry = match entry {
                StackDefItemNameResolved::Var { name, kind } => StackDefItemNameResolved::Var {
                    name: old_alloc_map[&name],
                    kind,
                },
                StackDefItemNameResolved::Stack(kind) => StackDefItemNameResolved::Stack(kind),
            };

            new_name_resolved_sig.entry.push(new_entry);
        }
        new_name_resolved_sig
    }

    pub fn get_generic_function_instance(
        &mut self,
        pass_manager: &mut PassManager,
        had_error: &mut ErrorSignal,
        base_fn_id: ItemId,
        resolved_generic_params: &[TypeId],
    ) -> Result<ItemId, ()> {
        if let Some(id) = self
            .items
            .get_cached_generic_function(base_fn_id, resolved_generic_params)
        {
            return Ok(id);
        }

        let _span = debug_span!(stringify!(get_generic_function_instance)).entered();
        trace!(?base_fn_id, ?resolved_generic_params,);

        // We need to make sure the generic function has been partially type-resolved before this step.
        let resolve_res = pass_manager.ensure_partially_resolve_types(self, base_fn_id);
        if resolve_res.is_err() {
            had_error.set();
            return Err(());
        }

        let base_fd_params = self.items.get_function_template_paramaters(base_fn_id);
        let base_header = self.items.get_item_header(base_fn_id);
        assert_eq!(resolved_generic_params.len(), base_fd_params.len());

        let param_map: HashMap<_, _> = base_fd_params
            .iter()
            .zip(resolved_generic_params)
            .map(|(name, ty)| (name.inner, *ty))
            .collect();

        // Essentially we need to do what the parser does what in encounters a non-generic function.
        let orig_unresolved_sig = self.sigs.urir.get_item_signature(base_fn_id).clone();
        let instantiated_sig =
            self.type_resolve_generic_signature(base_fn_id, resolved_generic_params, &param_map);

        let new_proc_id = self.items.new_function_generic_instance(
            self.sigs,
            base_header.name.inner.with_span(base_header.name.location),
            base_header.parent.unwrap(),
            base_header.attributes,
            orig_unresolved_sig.entry,
            orig_unresolved_sig.exit,
        );
        trace!(?new_proc_id);
        self.sigs
            .trir
            .set_item_signature(new_proc_id, instantiated_sig);

        let old_alloc_map = self.instantiate_variables(
            base_fn_id,
            new_proc_id,
            pass_manager,
            had_error,
            &param_map,
        );

        // Need to update the named parameters so codegen knows where to put the params.
        let new_name_resolved_sig = self.create_name_resolved_signature(base_fn_id, &old_alloc_map);
        self.sigs
            .nrir
            .set_item_signature(new_proc_id, new_name_resolved_sig);

        let body = self.items.get_item_body(base_fn_id);
        let new_body = self.expand_generic_params_in_block(
            pass_manager,
            had_error,
            body,
            &param_map,
            &old_alloc_map,
        );
        self.items.set_item_body(new_proc_id, new_body);
        self.items.set_cached_generic_function(
            base_fn_id,
            resolved_generic_params.into(),
            new_proc_id,
        );
        pass_manager.add_new_item(
            new_proc_id,
            base_fn_id,
            PassState::IdentResolvedBody
                | PassState::IdentResolvedSignature
                | PassState::TypeResolvedBody
                | PassState::TypeResolvedSignature,
        );

        Ok(new_proc_id)
    }
}
