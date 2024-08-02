use inkwell::{values::BasicValueEnum, AddressSpace, IntPredicate};
use intcast::IntCast;

use crate::{
    ir::{Arithmetic, Basic, OpCode, TypeResolvedOp},
    n_ops::SliceNOps,
    pass_manager::static_analysis::promote_int_type_bidirectional,
    stores::{
        ops::OpId,
        types::{IntSignedness, TypeKind},
        Stores,
    },
};

use super::{CodeGen, InkwellResult, SsaMap};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_add_sub(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        op_code: &OpCode<TypeResolvedOp>,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let input_value_ids @ [a, b] = *op_io.inputs().as_arr();
        let input_type_ids = ds.values.value_types(input_value_ids).unwrap();
        let input_type_infos = input_type_ids.map(|id| ds.types.get_type_info(id));

        let output_name = format!("{}", op_io.outputs()[0]);

        let res: BasicValueEnum = match input_type_infos.map(|ti| ti.kind) {
            [TypeKind::Integer(a_from), TypeKind::Integer(b_from)] => {
                let [output_type_id] = ds.values.value_types([op_io.outputs()[0]]).unwrap();
                let output_type_info = ds.types.get_type_info(output_type_id);

                let TypeKind::Integer(to_int) = output_type_info.kind else {
                    panic!("ICE: Non-int output of int-int arithmetic");
                };

                let a_val = value_store
                    .load_value(self, a, &mut ds.values, &mut ds.types)?
                    .into_int_value();
                let b_val = value_store
                    .load_value(self, b, &mut ds.values, &mut ds.types)?
                    .into_int_value();

                let target_type = to_int.width.get_int_type(self.ctx);
                let a_val = self.cast_int(a_val, target_type, a_from.signed)?;
                let b_val = self.cast_int(b_val, target_type, b_from.signed)?;

                let func = op_code.get_int_arith_fn();
                func(&self.builder, a_val, b_val, &output_name)?.into()
            }
            [TypeKind::Integer(int_type), TypeKind::MultiPointer(ptee_type)] => {
                assert!(matches!(
                    op_code,
                    OpCode::Basic(Basic::Arithmetic(Arithmetic::Add))
                ));
                assert_eq!(int_type.signed, IntSignedness::Unsigned);
                let offset = value_store
                    .load_value(self, a, &mut ds.values, &mut ds.types)?
                    .into_int_value();

                let offset = self.cast_int(offset, self.ctx.i64_type(), IntSignedness::Unsigned)?;
                let ptr = value_store
                    .load_value(self, b, &mut ds.values, &mut ds.types)?
                    .into_pointer_value();

                unsafe {
                    let ptee_type = self.get_type(&mut ds.types, ptee_type);
                    self.builder
                        .build_gep(ptee_type, ptr, &[offset], &output_name)?
                }
                .into()
            }
            [TypeKind::MultiPointer(ptee_type), TypeKind::Integer(int_type)] => {
                assert_eq!(int_type.signed, IntSignedness::Unsigned);
                let offset = value_store
                    .load_value(self, b, &mut ds.values, &mut ds.types)?
                    .into_int_value();

                let offset = self.cast_int(offset, self.ctx.i64_type(), IntSignedness::Unsigned)?;
                let ptr = value_store
                    .load_value(self, a, &mut ds.values, &mut ds.types)?
                    .into_pointer_value();

                // If we're subtracting, then we need to negate the offset.
                let offset =
                    if let OpCode::Basic(Basic::Arithmetic(Arithmetic::Subtract)) = &op_code {
                        self.builder.build_int_neg(offset, &output_name)?
                    } else {
                        offset
                    };

                unsafe {
                    let ptee_type = self.get_type(&mut ds.types, ptee_type);
                    self.builder
                        .build_gep(ptee_type, ptr, &[offset], &output_name)?
                }
                .into()
            }
            [TypeKind::MultiPointer(ptee_type), TypeKind::MultiPointer(_)] => {
                assert!(matches!(
                    op_code,
                    OpCode::Basic(Basic::Arithmetic(Arithmetic::Subtract))
                ));

                let lhs = value_store
                    .load_value(self, a, &mut ds.values, &mut ds.types)?
                    .into_pointer_value();
                let rhs = value_store
                    .load_value(self, b, &mut ds.values, &mut ds.types)?
                    .into_pointer_value();
                let ptee_type = self.get_type(&mut ds.types, ptee_type);
                let diff = self
                    .builder
                    .build_ptr_diff(ptee_type, lhs, rhs, &output_name)?;
                self.builder
                    .build_int_cast(diff, self.ctx.i64_type(), &output_name)?
                    .into()
            }
            [TypeKind::Float(a_from), TypeKind::Float(b_from)] => {
                let to_float = a_from.max(b_from);

                let a_val = value_store
                    .load_value(self, a, &mut ds.values, &mut ds.types)?
                    .into_float_value();
                let b_val = value_store
                    .load_value(self, b, &mut ds.values, &mut ds.types)?
                    .into_float_value();

                let target_type = to_float.get_float_type(self.ctx);
                let a_val = self.builder.build_float_cast(a_val, target_type, "")?;
                let b_val = self.builder.build_float_cast(b_val, target_type, "")?;

                let func = op_code.get_float_arith_fn();
                func(&self.builder, a_val, b_val, &output_name)?.into()
            }
            _ => panic!("ICE: Unexpected types"),
        };

        value_store.store_value(self, op_io.outputs()[0], res)?;

        Ok(())
    }

    pub(super) fn build_multiply_and_or_xor(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        op_code: &OpCode<TypeResolvedOp>,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let [a, b] = *op_io.inputs().as_arr();
        let input_type_ids = ds.values.value_types([a, b]).unwrap();
        let input_type_infos = input_type_ids.map(|ti| ds.types.get_type_info(ti));
        let [output_type_id] = ds.values.value_types([op_io.outputs()[0]]).unwrap();
        let output_type_info = ds.types.get_type_info(output_type_id);
        let output_name = format!("{}", op_io.outputs()[0]);

        let output_value = match output_type_info.kind {
            TypeKind::Integer(output_int) => {
                let a_val = value_store
                    .load_value(self, a, &mut ds.values, &mut ds.types)?
                    .into_int_value();
                let b_val = value_store
                    .load_value(self, b, &mut ds.values, &mut ds.types)?
                    .into_int_value();

                let [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] =
                    input_type_infos.map(|ti| ti.kind)
                else {
                    unreachable!()
                };

                let target_type = output_int.width.get_int_type(self.ctx);
                let a_val = self.cast_int(a_val, target_type, a_int.signed)?;
                let b_val = self.cast_int(b_val, target_type, b_int.signed)?;

                let func = op_code.get_int_arith_fn();
                let sum = func(&self.builder, a_val, b_val, &output_name)?;
                sum.into()
            }
            TypeKind::Bool => {
                let a_val = value_store
                    .load_value(self, a, &mut ds.values, &mut ds.types)?
                    .into_int_value();
                let b_val = value_store
                    .load_value(self, b, &mut ds.values, &mut ds.types)?
                    .into_int_value();

                let func = op_code.get_int_arith_fn();
                let sum = func(&self.builder, a_val, b_val, &output_name)?;
                sum.into()
            }
            TypeKind::Float(output_float) => {
                let a_val = value_store
                    .load_value(self, a, &mut ds.values, &mut ds.types)?
                    .into_float_value();
                let b_val = value_store
                    .load_value(self, b, &mut ds.values, &mut ds.types)?
                    .into_float_value();

                let target_type = output_float.get_float_type(self.ctx);
                let a_val = self.builder.build_float_cast(a_val, target_type, "")?;
                let b_val = self.builder.build_float_cast(b_val, target_type, "")?;

                let func = op_code.get_float_arith_fn();
                let sum = func(&self.builder, a_val, b_val, &output_name)?;

                sum.into()
            }
            _ => unreachable!(),
        };

        value_store.store_value(self, op_io.outputs()[0], output_value)?;

        Ok(())
    }

    pub(super) fn build_div_rem(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        op_code: &OpCode<TypeResolvedOp>,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let inputs @ [a, b] = *op_io.inputs().as_arr();
        let input_type_ids = ds.values.value_types(inputs).unwrap();

        let [output_type_id] = ds.values.value_types([op_io.outputs()[0]]).unwrap();
        let output_type_info = ds.types.get_type_info(output_type_id);
        let output_name = format!("{}", op_io.outputs()[0]);

        let input_type_kinds = input_type_ids.map(|id| ds.types.get_type_info(id).kind);
        let result = match input_type_kinds {
            [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] => {
                let TypeKind::Integer(output_int) = output_type_info.kind else {
                    panic!("ICE: Non-int output of int-int arithmetic");
                };

                let a_val = value_store
                    .load_value(self, a, &mut ds.values, &mut ds.types)?
                    .into_int_value();
                let b_val = value_store
                    .load_value(self, b, &mut ds.values, &mut ds.types)?
                    .into_int_value();

                let target_type = output_int.width.get_int_type(self.ctx);
                let a_val = self.cast_int(a_val, target_type, a_int.signed)?;
                let b_val = self.cast_int(b_val, target_type, b_int.signed)?;

                let func = op_code.get_int_div_rem_fn(output_int.signed);
                let res = func(&self.builder, a_val, b_val, &output_name)?;
                res.into()
            }

            [TypeKind::Float(a_float), TypeKind::Float(b_float)] => {
                let output_float = a_float.max(b_float);

                let a_val = value_store
                    .load_value(self, a, &mut ds.values, &mut ds.types)?
                    .into_float_value();
                let b_val = value_store
                    .load_value(self, b, &mut ds.values, &mut ds.types)?
                    .into_float_value();

                let target_type = output_float.get_float_type(self.ctx);
                let a_val = self.builder.build_float_cast(a_val, target_type, "")?;
                let b_val = self.builder.build_float_cast(b_val, target_type, "")?;

                let func = op_code.get_float_arith_fn();
                let res = func(&self.builder, a_val, b_val, &output_name)?;
                res.into()
            }

            _ => unreachable!(),
        };

        let [res_value_id] = *op_io.outputs().as_arr();
        value_store.store_value(self, res_value_id, result)?;

        Ok(())
    }

    pub(super) fn build_shift_left_right(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        op_code: &OpCode<TypeResolvedOp>,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let inputs @ [a, b] = *op_io.inputs().as_arr();
        let input_ids = ds.values.value_types(inputs).unwrap();
        let [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] =
            input_ids.map(|id| ds.types.get_type_info(id).kind)
        else {
            panic!("ICE: Non-int input of int-int arithmetic");
        };

        let [output_type_id] = ds.values.value_types([op_io.outputs()[0]]).unwrap();
        let output_type_info = ds.types.get_type_info(output_type_id);
        let output_name = format!("{}", op_io.outputs()[0]);

        let TypeKind::Integer(output_int) = output_type_info.kind else {
            panic!("ICE: Non-int output of int-int arithmetic");
        };

        let a_val = value_store
            .load_value(self, a, &mut ds.values, &mut ds.types)?
            .into_int_value();
        let b_val = value_store
            .load_value(self, b, &mut ds.values, &mut ds.types)?
            .into_int_value();

        // Mask the shift value to be within the bit-size of the target type.
        // This matches the semantics used during the ConstProp pass.
        let b_int_type = b_int.width.get_int_type(self.ctx);
        let mask = b_int_type.const_int(output_int.width.bit_width().to_u64() - 1, false);
        let b_val = self.builder.build_and(b_val, mask, "")?;

        let target_type = output_int.width.get_int_type(self.ctx);
        let a_val = self.cast_int(a_val, target_type, a_int.signed)?;
        let b_val = self.cast_int(b_val, target_type, b_int.signed)?;

        let res = match op_code {
            OpCode::Basic(Basic::Arithmetic(Arithmetic::ShiftLeft)) => {
                self.builder.build_left_shift(a_val, b_val, &output_name)?
            }
            OpCode::Basic(Basic::Arithmetic(Arithmetic::ShiftRight)) => {
                self.builder.build_right_shift(
                    a_val,
                    b_val,
                    output_int.signed == IntSignedness::Signed,
                    &output_name,
                )?
            }
            _ => unreachable!(),
        };
        value_store.store_value(self, op_io.outputs()[0], res.into())?;

        Ok(())
    }

    pub(super) fn build_bit_not(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let output_name = format!("{}", op_io.outputs()[0]);

        let a = op_io.inputs()[0];
        let a_val = value_store
            .load_value(self, a, &mut ds.values, &mut ds.types)?
            .into_int_value();

        let res = self.builder.build_not(a_val, &output_name)?;
        value_store.store_value(self, op_io.outputs()[0], res.into())?;

        Ok(())
    }

    pub(super) fn build_compare(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        op_code: &OpCode<TypeResolvedOp>,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let [a, b] = *op_io.inputs().as_arr();
        let input_types = ds.values.value_types([a, b]).unwrap();
        let input_type_infos = input_types.map(|id| ds.types.get_type_info(id));

        let a_val = value_store.load_value(self, a, &mut ds.values, &mut ds.types)?;
        let b_val = value_store.load_value(self, b, &mut ds.values, &mut ds.types)?;
        let output_name = format!("{}", op_io.outputs()[0]);

        let comp_result = match input_type_infos.map(|ti| ti.kind) {
            [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] => {
                let to_int = promote_int_type_bidirectional(a_int, b_int).unwrap();
                let target_type = to_int.width.get_int_type(self.ctx);

                let a_val = a_val.into_int_value();
                let b_val = b_val.into_int_value();

                let a_val = self.cast_int(a_val, target_type, a_int.signed)?;
                let b_val = self.cast_int(b_val, target_type, b_int.signed)?;

                let pred = op_code.get_int_predicate(to_int.signed);
                self.builder
                    .build_int_compare(pred, a_val, b_val, &output_name)?
            }
            [TypeKind::MultiPointer(_), TypeKind::MultiPointer(_)]
            | [TypeKind::SinglePointer(_), TypeKind::SinglePointer(_)] => todo!(),
            [TypeKind::Bool, TypeKind::Bool] => {
                let pred = op_code.get_int_predicate(IntSignedness::Unsigned);
                self.builder.build_int_compare(
                    pred,
                    a_val.into_int_value(),
                    b_val.into_int_value(),
                    &output_name,
                )?
            }
            [TypeKind::Float(a_float), TypeKind::Float(b_float)] => {
                let to_float = a_float.max(b_float);
                let target_type = to_float.get_float_type(self.ctx);

                let a_val = a_val.into_float_value();
                let b_val = b_val.into_float_value();

                let a_val = self.builder.build_float_cast(a_val, target_type, "")?;
                let b_val = self.builder.build_float_cast(b_val, target_type, "")?;

                let pred = op_code.get_float_predicate();
                self.builder
                    .build_float_compare(pred, a_val, b_val, &output_name)?
            }
            _ => unreachable!(),
        };

        value_store.store_value(self, op_io.outputs()[0], comp_result.into())?;

        Ok(())
    }

    pub(super) fn build_is_null(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let input_value_id = op_io.inputs()[0];
        let [input_type_id] = ds.values.value_types([input_value_id]).unwrap();
        let input_type_info = ds.types.get_type_info(input_type_id);
        let (TypeKind::MultiPointer(ptee_id) | TypeKind::SinglePointer(ptee_id)) =
            input_type_info.kind
        else {
            unreachable!()
        };
        let ptee_type = self.get_type(&mut ds.types, ptee_id);

        let ptr_val = value_store
            .load_value(self, input_value_id, &mut ds.values, &mut ds.types)?
            .into_pointer_value();

        let null_ptr = self.ctx.ptr_type(AddressSpace::default()).const_null();
        let zero = self.ctx.i64_type().const_zero();

        let name = format!("{}", op_io.outputs()[0]);
        let ptr_diff = self
            .builder
            .build_ptr_diff(ptee_type, ptr_val, null_ptr, &name)?;
        let result = self
            .builder
            .build_int_compare(IntPredicate::EQ, ptr_diff, zero, &name)?;

        value_store.store_value(self, op_io.outputs()[0], result.into())?;

        Ok(())
    }
}
