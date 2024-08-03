use inkwell::values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue};
use intcast::IntCast;
use tracing::trace;

use crate::{
    ir::{If, While},
    stores::{
        item::{ItemId, ItemKind},
        ops::OpId,
        source::Spanned,
        types::TypeKind,
        Stores,
    },
};

use super::{CodeGen, InkwellResult, SsaMap};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_function_call(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        callee_id: ItemId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let args: Vec<BasicMetadataValueEnum> = op_io
            .inputs()
            .iter()
            .zip(&ds.items.trir().get_item_signature(callee_id).entry)
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

        let callee_name = ds.strings.get_mangled_name(callee_id);
        let callee_value = self.item_function_map[&callee_id];

        let result =
            self.builder
                .build_call(callee_value, &args, &format!("call_{callee_name}"))?;

        let callee_header = ds.items.get_item_header(callee_id);
        if matches!(callee_header.kind, ItemKind::Function { .. }) {
            self.enqueue_function(callee_id);
        }

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

        let sig = ds.items.trir().get_item_signature(self_id);

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
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        function: FunctionValue<'ctx>,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let params = function.get_param_iter();
        for (id, param) in op_io.outputs().iter().zip(params) {
            value_store.store_value(self, *id, param)?;
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

    pub(super) fn build_if(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        function: FunctionValue<'ctx>,
        id: ItemId,
        op_id: OpId,
        if_op: &If,
    ) -> InkwellResult {
        let current_block = self.builder.get_insert_block().unwrap();

        // Generate new blocks for Then, Else, and Post.
        let then_basic_block = self
            .ctx
            .append_basic_block(function, &format!("if_{op_id}_then"));
        let else_basic_block = self
            .ctx
            .append_basic_block(function, &format!("if_{op_id}_else"));

        let post_basic_block =
            if ds.blocks.is_terminal(if_op.then_block) && ds.blocks.is_terminal(if_op.else_block) {
                None
            } else {
                Some(
                    self.ctx
                        .append_basic_block(function, &format!("if_{op_id}_post")),
                )
            };

        self.builder.position_at_end(current_block);
        // Compile condition
        trace!("Compiling condition for {:?}", op_id);
        self.compile_block(ds, value_store, id, if_op.condition, function)?;

        if ds.blocks.is_terminal(if_op.condition) {
            return Ok(());
        }

        trace!("Compiling jump for {:?}", op_id);
        // Make conditional jump.
        let op_io = ds.ops.get_op_io(op_id);
        let bool_value = value_store
            .load_value(self, op_io.inputs()[0], ds.values, ds.types)?
            .into_int_value();
        self.builder
            .build_conditional_branch(bool_value, then_basic_block, else_basic_block)?;

        // Compile Then
        self.builder.position_at_end(then_basic_block);
        trace!("Compiling then-block for {:?}", op_id);
        self.compile_block(ds, value_store, id, if_op.then_block, function)?;

        trace!("Transfering to merge vars for {:?}", op_id);
        if !ds.blocks.is_terminal(if_op.then_block) {
            let Some(merges) = ds.values.get_if_merges(op_id).cloned() else {
                panic!("ICE: If block doesn't have merges");
            };
            for merge in merges {
                let type_ids = ds
                    .values
                    .value_types([merge.then_value, merge.output_value])
                    .unwrap();
                let type_info_kinds = type_ids.map(|id| ds.types.get_type_info(id).kind);

                let data = value_store.load_value(self, merge.then_value, ds.values, ds.types)?;

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
        trace!("Compiling else-block for {:?}", op_id);
        self.compile_block(ds, value_store, id, if_op.else_block, function)?;

        trace!("Transfering to merge vars for {:?}", op_id);
        if !ds.blocks.is_terminal(if_op.else_block) {
            let Some(merges) = ds.values.get_if_merges(op_id).cloned() else {
                panic!("ICE: If block doesn't have merges");
            };
            for merge in merges {
                let type_ids = ds
                    .values
                    .value_types([merge.else_value, merge.output_value])
                    .unwrap();
                let type_info_kinds = type_ids.map(|id| ds.types.get_type_info(id).kind);

                let data = value_store.load_value(self, merge.else_value, ds.values, ds.types)?;

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
        self.builder.build_unconditional_branch(condition_block)?;

        trace!("Compiling condition for {:?}", op_id);
        self.builder.position_at_end(condition_block);
        self.compile_block(ds, value_store, id, while_op.condition, function)?;

        trace!("Transfering to merge vars for {:?}", op_id);
        {
            let Some(merges) = ds.values.get_while_merges(op_id).cloned() else {
                panic!("ICE: While block doesn't have merges");
            };
            for merge in &merges.condition {
                let type_ids = ds
                    .values
                    .value_types([merge.condition_value, merge.pre_value])
                    .unwrap();
                let type_info_kinds = type_ids.map(|id| ds.types.get_type_info(id).kind);

                let data =
                    value_store.load_value(self, merge.condition_value, ds.values, ds.types)?;

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
            let Some(merges) = ds.values.get_while_merges(op_id).cloned() else {
                panic!("ICE: While block doesn't have merges");
            };
            for merge in &merges.body {
                let type_ids = ds
                    .values
                    .value_types([merge.condition_value, merge.pre_value])
                    .unwrap();
                let type_info_kinds = type_ids.map(|id| ds.types.get_type_info(id).kind);

                let data =
                    value_store.load_value(self, merge.condition_value, ds.values, ds.types)?;

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
