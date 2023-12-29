use inkwell::values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue};
use intcast::IntCast;
use tracing::trace;

use crate::{
    opcode::{If, Op, While},
    program::ItemId,
    source_file::Spanned,
    type_store::TypeKind,
};

use super::{CodeGen, DataStore, InkwellResult, ValueStore};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_function_call(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut ValueStore<'ctx>,
        op: &Op,
        callee_id: ItemId,
    ) -> InkwellResult {
        let op_io = ds.analyzer.get_op_io(op.id);

        let args: Vec<BasicMetadataValueEnum> = op_io
            .inputs()
            .iter()
            .zip(
                ds.program
                    .get_item_signature_resolved(callee_id)
                    .entry_stack(),
            )
            .map(|(&value_id, &expected_type)| -> InkwellResult<_> {
                let value = value_store.load_value(self, value_id, ds)?;
                let [input_type_id] = ds.analyzer.value_types([value_id]).unwrap();

                let v = match (
                    ds.type_store.get_type_info(expected_type).kind,
                    ds.type_store.get_type_info(input_type_id).kind,
                ) {
                    (TypeKind::Integer(expected_int), TypeKind::Integer(input_int)) => self
                        .cast_int(
                            value.into_int_value(),
                            expected_int.width.get_int_type(self.ctx),
                            input_int.signed,
                        )?
                        .as_basic_value_enum(),
                    _ => value,
                };
                Ok(v)
            })
            .map(|p| p.map(Into::into))
            .collect::<InkwellResult<_>>()?;

        let callee_name = ds.interner.get_symbol_name(ds.program, callee_id);
        let callee_value = self.item_function_map[&callee_id];

        let result =
            self.builder
                .build_call(callee_value, &args, &format!("call_{callee_name}"))?;

        self.enqueue_function(callee_id);

        let Some(BasicValueEnum::StructValue(result)) = result.try_as_basic_value().left() else {
            // It was a void-type, so nothing to do.
            return Ok(());
        };

        for (&id, idx) in op_io.outputs().iter().zip(0..) {
            let output_name = format!("{id}");

            let value = self
                .builder
                .build_extract_value(result, idx, &output_name)?;

            value_store.store_value(self, id, value)?;
        }

        Ok(())
    }

    pub(super) fn build_epilogue_return(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut ValueStore<'ctx>,
        self_id: ItemId,
        op: &Op,
    ) -> InkwellResult {
        let op_io = ds.analyzer.get_op_io(op.id);

        if op_io.inputs().is_empty() {
            self.builder.build_return(None)?;
            return Ok(());
        }

        let sig = ds.program.get_item_signature_resolved(self_id);

        let return_values: Vec<BasicValueEnum> = op_io
            .inputs()
            .iter()
            .zip(sig.exit_stack())
            .map(|(value_id, expected_type_id)| -> InkwellResult<_> {
                let value = value_store.load_value(self, *value_id, ds)?;
                let [value_type_id] = ds.analyzer.value_types([*value_id]).unwrap();

                let value_type_info = ds.type_store.get_type_info(value_type_id);
                let expected_type_info = ds.type_store.get_type_info(*expected_type_id);

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

    pub(super) fn build_exit(&mut self) -> InkwellResult {
        let args = vec![
            self.ctx.i64_type().const_int(60, false).into(),
            self.ctx.i64_type().const_int(1, false).into(),
        ];

        let callee = self.syscall_wrappers[1];
        self.builder.build_call(callee, &args, "exit")?;
        self.builder.build_unreachable()?;

        Ok(())
    }

    pub(super) fn build_prologue(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut ValueStore<'ctx>,
        op: &Op,
        function: FunctionValue<'ctx>,
    ) -> InkwellResult {
        let op_io = ds.analyzer.get_op_io(op.id);

        let params = function.get_param_iter();
        for (id, param) in op_io.outputs().iter().zip(params) {
            value_store.store_value(self, *id, param)?;
        }

        Ok(())
    }

    pub(super) fn build_syscall(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut ValueStore<'ctx>,
        op: &Op,
        arg_count: Spanned<u8>,
    ) -> InkwellResult {
        let op_io = ds.analyzer.get_op_io(op.id);
        let callee_value = self.syscall_wrappers[arg_count.inner.to_usize() - 1];

        let args: Vec<BasicMetadataValueEnum> = op_io
            .inputs()
            .iter()
            .map(|id| -> InkwellResult<_> {
                match value_store.load_value(self, *id, ds)? {
                    BasicValueEnum::PointerValue(v) => {
                        Ok(self
                            .builder
                            .build_ptr_to_int(v, self.ctx.i64_type(), "ptr_cast")?)
                    }
                    BasicValueEnum::IntValue(int_val) => {
                        let [type_id] = ds.analyzer.value_types([*id]).unwrap();
                        let TypeKind::Integer(int_type) = ds.type_store.get_type_info(type_id).kind
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

    pub(super) fn build_if(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut ValueStore<'ctx>,
        function: FunctionValue<'ctx>,
        id: ItemId,
        op: &Op,
        if_op: &If,
    ) -> InkwellResult {
        let current_block = self.builder.get_insert_block().unwrap();

        // Generate new blocks for Then, Else, and Post.
        let then_basic_block = self
            .ctx
            .append_basic_block(function, &format!("if_{}_then", op.id));
        let else_basic_block = self
            .ctx
            .append_basic_block(function, &format!("if_{}_else", op.id));

        let post_basic_block = if if_op.is_then_terminal && if_op.is_else_terminal {
            None
        } else {
            Some(
                self.ctx
                    .append_basic_block(function, &format!("if_{}_post", op.id)),
            )
        };

        self.builder.position_at_end(current_block);
        // Compile condition
        trace!("Compiling condition for {:?}", op.id);
        self.compile_block(ds, value_store, id, &if_op.condition, function)?;

        if if_op.is_condition_terminal {
            return Ok(());
        }

        trace!("Compiling jump for {:?}", op.id);
        // Make conditional jump.
        let op_io = ds.analyzer.get_op_io(op.id);
        let bool_value = value_store
            .load_value(self, op_io.inputs()[0], ds)?
            .into_int_value();
        self.builder
            .build_conditional_branch(bool_value, then_basic_block, else_basic_block)?;

        // Compile Then
        self.builder.position_at_end(then_basic_block);
        trace!("Compiling then-block for {:?}", op.id);
        self.compile_block(ds, value_store, id, &if_op.then_block, function)?;

        trace!("Transfering to merge vars for {:?}", op.id);
        if !if_op.is_then_terminal {
            let Some(merges) = ds.analyzer.get_if_merges(op.id) else {
                panic!("ICE: If block doesn't have merges");
            };
            for merge in merges {
                let type_ids = ds
                    .analyzer
                    .value_types([merge.then_value, merge.output_value])
                    .unwrap();
                let type_info_kinds = type_ids.map(|id| ds.type_store.get_type_info(id).kind);

                let data = value_store.load_value(self, merge.then_value, ds)?;

                let data = if let [TypeKind::Integer(then_int), TypeKind::Integer(output_int)] =
                    type_info_kinds
                {
                    let int = data.into_int_value();
                    let target_type = output_int.width.get_int_type(self.ctx);
                    self.cast_int(int, target_type, then_int.signed)?
                        .as_basic_value_enum()
                } else {
                    data
                };

                value_store.store_value(self, merge.output_value, data)?;
            }

            if let Some(post_block) = post_basic_block {
                self.builder.build_unconditional_branch(post_block)?;
            }
        }

        // Compile Else
        self.builder.position_at_end(else_basic_block);
        trace!("Compiling else-block for {:?}", op.id);
        self.compile_block(ds, value_store, id, &if_op.else_block, function)?;

        trace!("Transfering to merge vars for {:?}", op.id);
        if !if_op.is_else_terminal {
            let Some(merges) = ds.analyzer.get_if_merges(op.id) else {
                panic!("ICE: If block doesn't have merges");
            };
            for merge in merges {
                let type_ids = ds
                    .analyzer
                    .value_types([merge.else_value, merge.output_value])
                    .unwrap();
                let type_info_kinds = type_ids.map(|id| ds.type_store.get_type_info(id).kind);

                let data = value_store.load_value(self, merge.else_value, ds)?;

                let data = if let [TypeKind::Integer(else_int), TypeKind::Integer(output_int)] =
                    type_info_kinds
                {
                    let int = data.into_int_value();
                    let target_type = output_int.width.get_int_type(self.ctx);
                    self.cast_int(int, target_type, else_int.signed)?
                        .as_basic_value_enum()
                } else {
                    data
                };

                value_store.store_value(self, merge.output_value, data)?;
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
        ds: &mut DataStore,
        value_store: &mut ValueStore<'ctx>,
        function: FunctionValue<'ctx>,
        id: ItemId,
        op: &Op,
        while_op: &While,
    ) -> InkwellResult {
        let current_block = self.builder.get_insert_block().unwrap();
        let condition_block = self
            .ctx
            .append_basic_block(function, &format!("while_{}_condition", op.id));
        let body_block = self
            .ctx
            .append_basic_block(function, &format!("while_{}_body", op.id));
        let post_block = self
            .ctx
            .append_basic_block(function, &format!("while_{}_post", op.id));

        self.builder.position_at_end(current_block);
        self.builder.build_unconditional_branch(condition_block)?;

        trace!("Compiling condition for {:?}", op.id);
        self.builder.position_at_end(condition_block);
        self.compile_block(ds, value_store, id, &while_op.condition, function)?;

        trace!("Transfering to merge vars for {:?}", op.id);
        {
            let Some(merges) = ds.analyzer.get_while_merges(op.id) else {
                panic!("ICE: While block doesn't have merges");
            };
            for merge in &merges.condition {
                let type_ids = ds
                    .analyzer
                    .value_types([merge.condition_value, merge.pre_value])
                    .unwrap();
                let type_info_kinds = type_ids.map(|id| ds.type_store.get_type_info(id).kind);

                let data = value_store.load_value(self, merge.condition_value, ds)?;

                let data = if let [TypeKind::Integer(condition_int), TypeKind::Integer(pre_int)] =
                    type_info_kinds
                {
                    let int = data.into_int_value();
                    let target_type = pre_int.width.get_int_type(self.ctx);
                    self.cast_int(int, target_type, condition_int.signed)?
                        .as_basic_value_enum()
                } else {
                    data
                };

                value_store.store_value(self, merge.pre_value, data)?;
            }
        }

        trace!("Compiling jump for {:?}", op.id);
        // Make conditional jump.
        let op_io = ds.analyzer.get_op_io(op.id);

        let bool_value = value_store
            .load_value(self, op_io.inputs()[0], ds)?
            .into_int_value();
        self.builder
            .build_conditional_branch(bool_value, body_block, post_block)?;

        // Compile body
        self.builder.position_at_end(body_block);
        trace!("Compiling body-block for {:?}", op.id);
        self.compile_block(ds, value_store, id, &while_op.body_block, function)?;

        trace!("Transfering to merge vars for {:?}", op.id);
        {
            let Some(merges) = ds.analyzer.get_while_merges(op.id) else {
                panic!("ICE: While block doesn't have merges");
            };
            for merge in &merges.body {
                let type_ids = ds
                    .analyzer
                    .value_types([merge.condition_value, merge.pre_value])
                    .unwrap();
                let type_info_kinds = type_ids.map(|id| ds.type_store.get_type_info(id).kind);

                let data = value_store.load_value(self, merge.condition_value, ds)?;

                let data = if let [TypeKind::Integer(condition_int), TypeKind::Integer(pre_int)] =
                    type_info_kinds
                {
                    let int = data.into_int_value();
                    let target_type = pre_int.width.get_int_type(self.ctx);
                    self.cast_int(int, target_type, condition_int.signed)?
                        .as_basic_value_enum()
                } else {
                    data
                };

                value_store.store_value(self, merge.pre_value, data)?;
            }
        }

        self.builder.build_unconditional_branch(condition_block)?;

        self.builder.position_at_end(post_block);

        Ok(())
    }
}
