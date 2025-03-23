use inkwell::values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue};
use intcast::IntCast;
use stores::{items::ItemId, source::Spanned};
use tracing::trace;

use crate::{
    ir::{Cond, While},
    n_ops::SliceNOps,
    stores::{
        item::{ItemAttribute, ItemKind},
        ops::OpId,
        signatures::StackDefItemNameResolved,
        types::TypeKind,
        Stores,
    },
};

use super::{CodeGen, InkwellResult, SsaMap};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_function_pointer(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        callee_id: ItemId,
    ) -> InkwellResult {
        self.enqueue_function(callee_id);

        let output_value_id = ds.ops.get_op_io(op_id).outputs[0];
        let function_value = self.item_function_map[&callee_id];
        let function_pointer = function_value.as_global_value().as_pointer_value();

        value_store.store_value(self, output_value_id, function_pointer.into())?;

        Ok(())
    }

    pub(super) fn build_function_call(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        item_id: ItemId,
        function: FunctionValue<'ctx>,
        callee_id: ItemId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let mut args: Vec<BasicMetadataValueEnum> = op_io
            .inputs()
            .iter()
            .zip(&ds.sigs.trir.get_item_signature(callee_id).entry)
            .map(|(&value_id, &expected_type)| -> InkwellResult<_> {
                let value = value_store.load_value(self, value_id, ds.values, ds.types)?;
                let [input_type_id] = ds.values.value_types([value_id]).unwrap();

                let v = match (
                    ds.types.get_type_info(expected_type).kind,
                    ds.types.get_type_info(input_type_id).kind,
                ) {
                    (TypeKind::Integer(expected_int), TypeKind::Integer(input_int)) => self
                        .cast_int(
                            value.into_int_value(),
                            expected_int.width.get_int_type(self.ctx),
                            input_int.signed,
                        )?
                        .as_basic_value_enum(),
                    (TypeKind::Float(expected_float), TypeKind::Float(_)) => self
                        .builder
                        .build_float_cast(
                            value.into_float_value(),
                            expected_float.get_float_type(self.ctx),
                            "",
                        )?
                        .as_basic_value_enum(),
                    _ => value,
                };
                Ok(v)
            })
            .map(|p| p.map(Into::into))
            .collect::<InkwellResult<_>>()?;

        let callee_header = ds.items.get_item_header(callee_id);
        if callee_header
            .attributes
            .contains(ItemAttribute::TrackCaller)
        {
            let this_header = ds.items.get_item_header(item_id);
            let here_string = if this_header.attributes.contains(ItemAttribute::TrackCaller) {
                function.get_last_param().unwrap()
            } else {
                let op_loc = ds.ops.get_token(op_id).location;
                self.get_here_string(ds, value_store, op_loc)?
            };

            args.push(here_string.into());
        }

        let callee_name = ds.strings.get_mangled_name(callee_id);
        let callee_value = self.item_function_map[&callee_id];

        let result =
            self.builder
                .build_call(callee_value, &args, &format!("call_{callee_name}"))?;

        let callee_header = ds.items.get_item_header(callee_id);
        if matches!(callee_header.kind, ItemKind::Function) {
            self.enqueue_function(callee_id);
        }

        let Some(BasicValueEnum::StructValue(result)) = result.try_as_basic_value().left() else {
            // It was a void-type, so nothing to do.
            return Ok(());
        };

        let op_io = ds.ops.get_op_io(op_id);
        for (&id, idx) in op_io.outputs().iter().zip(0..) {
            let output_name = format!("{id}");

            let value = self
                .builder
                .build_extract_value(result, idx, &output_name)?;

            value_store.store_value(self, id, value)?;
        }

        Ok(())
    }

    pub(super) fn build_method_call(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        item_id: ItemId,
        function: FunctionValue<'ctx>,
    ) -> InkwellResult {
        let callee_id = ds.ops.get_method_callee(op_id).unwrap();
        self.build_function_call(ds, value_store, op_id, item_id, function, callee_id)
    }

    pub(super) fn build_epilogue_return(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        self_id: ItemId,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        if op_io.inputs().is_empty() {
            self.builder.build_return(None)?;
            return Ok(());
        }

        let sig = ds.sigs.trir.get_item_signature(self_id);

        let return_values: Vec<BasicValueEnum> = op_io
            .inputs()
            .iter()
            .zip(&sig.exit)
            .map(|(value_id, expected_type_id)| -> InkwellResult<_> {
                let value = value_store.load_value(self, *value_id, ds.values, ds.types)?;
                let [value_type_id] = ds.values.value_types([*value_id]).unwrap();

                let value_type_info = ds.types.get_type_info(value_type_id);
                let expected_type_info = ds.types.get_type_info(*expected_type_id);

                let value = match (value_type_info.kind, expected_type_info.kind) {
                    (TypeKind::Integer(value_int), TypeKind::Integer(expected_int)) => self
                        .cast_int(
                            value.into_int_value(),
                            expected_int.width.get_int_type(self.ctx),
                            value_int.signed,
                        )?
                        .as_basic_value_enum(),
                    _ => value,
                };

                Ok(value)
            })
            .collect::<InkwellResult<_>>()?;

        self.builder.build_aggregate_return(&return_values)?;

        Ok(())
    }

    pub(super) fn build_exit(&mut self, code: u8) -> InkwellResult {
        let args = vec![
            self.ctx.i64_type().const_int(60, false).into(),
            self.ctx.i64_type().const_int(code.to_u64(), false).into(),
        ];

        let callee = self.syscall_wrappers[1];
        self.builder.build_call(callee, &args, "exit")?;
        self.builder.build_unreachable()?;

        Ok(())
    }

    pub(super) fn build_prologue(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        item_id: ItemId,
        op_id: OpId,
        function: FunctionValue<'ctx>,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let sig = ds.sigs.nrir.get_item_signature(item_id);

        let params = function.get_param_iter();
        for ((id, entry_def), param) in op_io.outputs().iter().zip(&sig.entry).zip(params) {
            match entry_def {
                StackDefItemNameResolved::Var { name, .. } => {
                    let var_ptr = value_store.variable_map[name];
                    self.builder.build_store(var_ptr, param)?;
                }
                StackDefItemNameResolved::Stack(_) => {
                    value_store.store_value(self, *id, param)?;
                }
            }
        }

        Ok(())
    }

    pub(super) fn build_syscall(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        arg_count: Spanned<u8>,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let callee_value = self.syscall_wrappers[arg_count.inner.to_usize() - 1];

        let args: Vec<BasicMetadataValueEnum> = op_io
            .inputs()
            .iter()
            .map(|id| -> InkwellResult<_> {
                match value_store.load_value(self, *id, ds.values, ds.types)? {
                    BasicValueEnum::PointerValue(v) => {
                        Ok(self
                            .builder
                            .build_ptr_to_int(v, self.ctx.i64_type(), "ptr_cast")?)
                    }
                    BasicValueEnum::IntValue(int_val) => {
                        let [type_id] = ds.values.value_types([*id]).unwrap();
                        let TypeKind::Integer(int_type) = ds.types.get_type_info(type_id).kind
                        else {
                            unreachable!()
                        };
                        Ok(self.cast_int(int_val, self.ctx.i64_type(), int_type.signed)?)
                    }
                    t => panic!("ICE: Unexected type: {t:?}"),
                }
            })
            .map(|p| p.map(Into::into))
            .collect::<InkwellResult<_>>()?;

        let result = self.builder.build_call(
            callee_value,
            &args,
            &format!("calling syscall{}", arg_count.inner),
        )?;

        let Some(BasicValueEnum::IntValue(ret_val)) = result.try_as_basic_value().left() else {
            panic!("ICE: All syscalls return a value");
        };

        value_store.store_value(self, op_io.outputs()[0], ret_val.into())?;

        Ok(())
    }

    pub(super) fn build_cond(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        function: FunctionValue<'ctx>,
        id: ItemId,
        op_id: OpId,
        cond_op: &Cond,
    ) -> InkwellResult {
        let current_block = self.builder.get_insert_block().unwrap();

        // Generate new blocks for Then, Else, and Post.
        let else_basic_block = self
            .ctx
            .append_basic_block(function, &format!("cond_{op_id}_else"));

        let post_basic_block = if cond_op.is_all_terminal(ds) {
            None
        } else {
            Some(
                self.ctx
                    .append_basic_block(function, &format!("cond_{op_id}_post")),
            )
        };

        // At least one conditional arm.
        let mut arm_condition_blocks = Vec::new();
        for arm in &cond_op.arms {
            arm_condition_blocks.push(self.ctx.append_basic_block(
                function,
                &format!("cond_{op_id}_arm_condition_{}", arm.condition),
            ));
        }
        // Considering it a condition block simplifies things.
        arm_condition_blocks.push(else_basic_block);
        self.builder.position_at_end(current_block);
        self.builder
            .build_unconditional_branch(arm_condition_blocks[0])?;

        let op_io = ds.ops.get_op_io(op_id).clone();

        for ((pair, arm), &cond_value_id) in arm_condition_blocks
            .windows(2)
            .zip(&cond_op.arms)
            .zip(&op_io.inputs)
        {
            let [this_condition, next_condition] = *pair.as_arr();

            let then_block = self
                .ctx
                .append_basic_block(function, &format!("cond_{op_id}_arm_block_{}", arm.block));

            trace!(
                "Compiling arm condition for {:?} {:?}",
                op_id,
                arm.condition
            );
            self.builder.position_at_end(this_condition);
            self.compile_block(ds, value_store, id, arm.condition, function)?;

            trace!("Compiling jump for arm {:?} {:?}", op_id, arm.condition);
            // Make conditional jump.
            let bool_value = value_store
                .load_value(self, cond_value_id, ds.values, ds.types)?
                .into_int_value();
            self.builder
                .build_conditional_branch(bool_value, then_block, next_condition)?;

            trace!("Compiling then_block for arm {:?} {:?}", op_id, arm.block);
            self.builder.position_at_end(then_block);
            self.compile_block(ds, value_store, id, arm.block, function)?;

            trace!("Transfering to merge vars for {:?} {:?}", op_id, arm.block);
            if !ds.blocks.is_terminal(arm.block) && !ds.blocks.is_terminal(arm.condition) {
                let Some(merges) = ds.values.get_merge_values(op_id).cloned() else {
                    panic!("ICE: Cond block doesn't have merges");
                };
                for merge in merges {
                    let Some(block_merge_value_id) = merge.block_input(arm.block) else {
                        continue;
                    };

                    let type_ids = ds
                        .values
                        .value_types([block_merge_value_id, merge.output])
                        .unwrap();
                    let type_info_kinds = type_ids.map(|tid| ds.types.get_type_info(tid).kind);

                    let data =
                        value_store.load_value(self, block_merge_value_id, ds.values, ds.types)?;

                    let data = match type_info_kinds {
                        [TypeKind::Integer(b_int), TypeKind::Integer(out_int)] => {
                            let int = data.into_int_value();
                            let target_type = out_int.width.get_int_type(self.ctx);
                            self.cast_int(int, target_type, b_int.signed)?
                                .as_basic_value_enum()
                        }
                        [TypeKind::Float(_), TypeKind::Float(out_float)] => {
                            let flt = data.into_float_value();
                            let target_type = out_float.get_float_type(self.ctx);
                            self.builder
                                .build_float_cast(flt, target_type, "")?
                                .as_basic_value_enum()
                        }

                        _ => data,
                    };

                    value_store.store_value(self, merge.output, data)?;
                }

                if let Some(post_block) = post_basic_block {
                    self.builder.build_unconditional_branch(post_block)?;
                }
            }
        }

        // Compile Else
        self.builder.position_at_end(else_basic_block);
        trace!("Compiling else-block for {:?}", op_id);
        self.compile_block(ds, value_store, id, cond_op.else_block, function)?;

        trace!("Transfering to merge vars for {:?}", op_id);
        if !ds.blocks.is_terminal(cond_op.else_block) {
            let Some(merges) = ds.values.get_merge_values(op_id).cloned() else {
                panic!("ICE: Cond block doesn't have merges");
            };
            for merge in merges {
                let Some(else_merge_value_id) = merge.block_input(cond_op.else_block) else {
                    continue;
                };

                let type_ids = ds
                    .values
                    .value_types([else_merge_value_id, merge.output])
                    .unwrap();
                let type_info_kinds = type_ids.map(|tid| ds.types.get_type_info(tid).kind);

                let data =
                    value_store.load_value(self, else_merge_value_id, ds.values, ds.types)?;

                let data = match type_info_kinds {
                    [TypeKind::Integer(b_int), TypeKind::Integer(out_int)] => {
                        let int = data.into_int_value();
                        let target_type = out_int.width.get_int_type(self.ctx);
                        self.cast_int(int, target_type, b_int.signed)?
                            .as_basic_value_enum()
                    }
                    [TypeKind::Float(_), TypeKind::Float(out_float)] => {
                        let flt = data.into_float_value();
                        let target_type = out_float.get_float_type(self.ctx);
                        self.builder
                            .build_float_cast(flt, target_type, "")?
                            .as_basic_value_enum()
                    }

                    _ => data,
                };

                value_store.store_value(self, merge.output, data)?;
            }

            if let Some(post_block) = post_basic_block {
                self.builder.build_unconditional_branch(post_block)?;
            }
        }

        // Build our jumps
        if let Some(post_block) = post_basic_block {
            self.builder.position_at_end(post_block);
        }
        Ok(())
    }

    pub(super) fn build_while(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        function: FunctionValue<'ctx>,
        id: ItemId,
        op_id: OpId,
        while_op: &While,
    ) -> InkwellResult {
        let current_block = self.builder.get_insert_block().unwrap();

        let condition_block = self
            .ctx
            .append_basic_block(function, &format!("while_{op_id}_condition"));
        let body_block = self
            .ctx
            .append_basic_block(function, &format!("while_{op_id}_body"));
        let post_block = self
            .ctx
            .append_basic_block(function, &format!("while_{op_id}_post"));

        self.builder.position_at_end(current_block);

        trace!("Transfering to merge vars for {:?}", op_id);
        {
            let Some(merges) = ds.values.get_merge_values(op_id).cloned() else {
                panic!("ICE: While block doesn't have merges");
            };
            for merge in &merges {
                // While loops only have two inputs, so we can just make the assumption.
                let type_ids = ds
                    .values
                    .value_types([merge.inputs[0].1, merge.output])
                    .unwrap();
                let type_info_kinds = type_ids.map(|id| ds.types.get_type_info(id).kind);

                let data = value_store.load_value(self, merge.inputs[0].1, ds.values, ds.types)?;

                let data = match type_info_kinds {
                    [TypeKind::Integer(a_int), TypeKind::Integer(out_int)] => {
                        let int = data.into_int_value();
                        let target_type = out_int.width.get_int_type(self.ctx);
                        self.cast_int(int, target_type, a_int.signed)?
                            .as_basic_value_enum()
                    }
                    [TypeKind::Float(_), TypeKind::Float(out_float)] => {
                        let flt = data.into_float_value();
                        let target_type = out_float.get_float_type(self.ctx);
                        self.builder
                            .build_float_cast(flt, target_type, "")?
                            .as_basic_value_enum()
                    }

                    _ => data,
                };

                value_store.store_value(self, merge.output, data)?;
            }
        }

        self.builder.build_unconditional_branch(condition_block)?;

        trace!("Compiling condition for {:?}", op_id);
        self.builder.position_at_end(condition_block);
        self.compile_block(ds, value_store, id, while_op.condition, function)?;

        trace!("Compiling jump for {:?}", op_id);
        // Make conditional jump.
        let op_io = ds.ops.get_op_io(op_id);

        let bool_value = value_store
            .load_value(self, op_io.inputs()[0], ds.values, ds.types)?
            .into_int_value();
        self.builder
            .build_conditional_branch(bool_value, body_block, post_block)?;

        // Compile body
        self.builder.position_at_end(body_block);
        trace!("Compiling body-block for {:?}", op_id);
        self.compile_block(ds, value_store, id, while_op.body_block, function)?;

        trace!("Transfering to merge vars for {:?}", op_id);
        {
            let Some(merge_values) = ds.values.get_merge_values(op_id).cloned() else {
                panic!("ICE: While block doesn't have merges");
            };
            for merge in &merge_values {
                let type_ids = ds
                    .values
                    .value_types([merge.inputs[1].1, merge.output])
                    .unwrap();
                let type_info_kinds = type_ids.map(|id| ds.types.get_type_info(id).kind);

                let data = value_store.load_value(self, merge.inputs[1].1, ds.values, ds.types)?;

                let data = match type_info_kinds {
                    [TypeKind::Integer(b_int), TypeKind::Integer(out_int)] => {
                        let int = data.into_int_value();
                        let target_type = out_int.width.get_int_type(self.ctx);
                        self.cast_int(int, target_type, b_int.signed)?
                            .as_basic_value_enum()
                    }
                    [TypeKind::Float(_), TypeKind::Float(out_float)] => {
                        let flt = data.into_float_value();
                        let target_type = out_float.get_float_type(self.ctx);
                        self.builder
                            .build_float_cast(flt, target_type, "")?
                            .as_basic_value_enum()
                    }

                    _ => data,
                };

                value_store.store_value(self, merge.output, data)?;
            }
        }

        self.builder.build_unconditional_branch(condition_block)?;

        self.builder.position_at_end(post_block);

        Ok(())
    }
}
