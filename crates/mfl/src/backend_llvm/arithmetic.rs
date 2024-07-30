use inkwell::{values::BasicValueEnum, AddressSpace, IntPredicate};
use intcast::IntCast;

use crate::{
    ir::{Arithmetic, Basic, OpCode, TypeResolvedOp},
    n_ops::SliceNOps,
    pass_manager::static_analysis::promote_int_type_bidirectional,
    stores::{
        ops::OpId,
        types::{IntSignedness, TypeKind},
    },
};

use super::{CodeGen, DataStore, InkwellResult, SsaMap};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_add_sub(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        op_code: &OpCode<TypeResolvedOp>,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);

        let input_value_ids @ [a, b] = *op_io.inputs().as_arr();
        let input_type_ids = ds.analyzer.value_types(input_value_ids).unwrap();
        let input_type_infos = input_type_ids.map(|id| ds.type_store.get_type_info(id));

        let output_name = format!("{}", op_io.outputs()[0]);

        let res: BasicValueEnum = match input_type_infos.map(|ti| ti.kind) {
            [TypeKind::Integer(a_from), TypeKind::Integer(b_from)] => {
                let [output_type_id] = ds.analyzer.value_types([op_io.outputs()[0]]).unwrap();
                let output_type_info = ds.type_store.get_type_info(output_type_id);

                let TypeKind::Integer(to_int) = output_type_info.kind else {
                    panic!("ICE: Non-int output of int-int arithmetic");
                };

                let a_val = value_store.load_value(self, a, ds)?.into_int_value();
                let b_val = value_store.load_value(self, b, ds)?.into_int_value();

                let target_type = to_int.width.get_int_type(self.ctx);
                let a_val = self.cast_int(a_val, target_type, a_from.signed)?;
                let b_val = self.cast_int(b_val, target_type, b_from.signed)?;

                let func = op_code.get_arith_fn();
                func(&self.builder, a_val, b_val, &output_name)?.into()
            }
            [TypeKind::Integer(int_type), TypeKind::MultiPointer(ptee_type)] => {
                assert!(matches!(
                    op_code,
                    OpCode::Basic(Basic::Arithmetic(Arithmetic::Add))
                ));
                assert_eq!(int_type.signed, IntSignedness::Unsigned);
                let offset = value_store.load_value(self, a, ds)?.into_int_value();

                let offset = self.cast_int(offset, self.ctx.i64_type(), IntSignedness::Unsigned)?;
                let ptr = value_store.load_value(self, b, ds)?.into_pointer_value();

                unsafe {
                    let ptee_type = self.get_type(ds.type_store, ptee_type);
                    self.builder
                        .build_gep(ptee_type, ptr, &[offset], &output_name)?
                }
                .into()
            }
            [TypeKind::MultiPointer(ptee_type), TypeKind::Integer(int_type)] => {
                assert_eq!(int_type.signed, IntSignedness::Unsigned);
                let offset = value_store.load_value(self, b, ds)?.into_int_value();

                let offset = self.cast_int(offset, self.ctx.i64_type(), IntSignedness::Unsigned)?;
                let ptr = value_store.load_value(self, a, ds)?.into_pointer_value();

                // If we're subtracting, then we need to negate the offset.
                let offset =
                    if let OpCode::Basic(Basic::Arithmetic(Arithmetic::Subtract)) = &op_code {
                        self.builder.build_int_neg(offset, &output_name)?
                    } else {
                        offset
                    };

                unsafe {
                    let ptee_type = self.get_type(ds.type_store, ptee_type);
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

                let lhs = value_store.load_value(self, a, ds)?.into_pointer_value();
                let rhs = value_store.load_value(self, b, ds)?.into_pointer_value();
                let ptee_type = self.get_type(ds.type_store, ptee_type);
                let diff = self
                    .builder
                    .build_ptr_diff(ptee_type, lhs, rhs, &output_name)?;
                self.builder
                    .build_int_cast(diff, self.ctx.i64_type(), &output_name)?
                    .into()
            }
            _ => panic!("ICE: Unexpected types"),
        };

        value_store.store_value(self, op_io.outputs()[0], res)?;

        Ok(())
    }

    pub(super) fn build_multiply_and_or_xor(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        op_code: &OpCode<TypeResolvedOp>,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);

        let [a, b] = *op_io.inputs().as_arr();
        let input_type_ids = ds.analyzer.value_types([a, b]).unwrap();
        let input_type_infos = input_type_ids.map(|ti| ds.type_store.get_type_info(ti));
        let [output_type_id] = ds.analyzer.value_types([op_io.outputs()[0]]).unwrap();
        let output_type_info = ds.type_store.get_type_info(output_type_id);
        let output_name = format!("{}", op_io.outputs()[0]);

        let a_val = value_store.load_value(self, a, ds)?.into_int_value();
        let b_val = value_store.load_value(self, b, ds)?.into_int_value();

        let (a_val, b_val) = if let TypeKind::Integer(output_int) = output_type_info.kind {
            let [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] =
                input_type_infos.map(|ti| ti.kind)
            else {
                unreachable!()
            };

            let target_type = output_int.width.get_int_type(self.ctx);
            let a_val = self.cast_int(a_val, target_type, a_int.signed)?;
            let b_val = self.cast_int(b_val, target_type, b_int.signed)?;

            (a_val, b_val)
        } else {
            (a_val, b_val)
        };

        let func = op_code.get_arith_fn();
        let sum = func(&self.builder, a_val, b_val, &output_name)?;
        value_store.store_value(self, op_io.outputs()[0], sum.into())?;

        Ok(())
    }

    pub(super) fn build_div_rem(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        op_code: &OpCode<TypeResolvedOp>,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);

        let inputs @ [a, b] = *op_io.inputs().as_arr();
        let input_type_ids = ds.analyzer.value_types(inputs).unwrap();
        let [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] =
            input_type_ids.map(|id| ds.type_store.get_type_info(id).kind)
        else {
            panic!("ICE: DivMod has non-int inputs");
        };

        let [output_type_id] = ds.analyzer.value_types([op_io.outputs()[0]]).unwrap();
        let output_type_info = ds.type_store.get_type_info(output_type_id);
        let output_name = format!("{}", op_io.outputs()[0]);

        let TypeKind::Integer(output_int) = output_type_info.kind else {
            panic!("ICE: Non-int output of int-int arithmetic");
        };

        let a_val = value_store.load_value(self, a, ds)?.into_int_value();
        let b_val = value_store.load_value(self, b, ds)?.into_int_value();

        let target_type = output_int.width.get_int_type(self.ctx);
        let a_val = self.cast_int(a_val, target_type, a_int.signed)?;
        let b_val = self.cast_int(b_val, target_type, b_int.signed)?;

        let func = op_code.get_div_rem_fn(output_int.signed);
        let res = func(&self.builder, a_val, b_val, &output_name)?;

        let [res_val] = *op_io.outputs().as_arr();
        value_store.store_value(self, res_val, res.into())?;

        Ok(())
    }

    pub(super) fn build_shift_left_right(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        op_code: &OpCode<TypeResolvedOp>,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);

        let inputs @ [a, b] = *op_io.inputs().as_arr();
        let input_ids = ds.analyzer.value_types(inputs).unwrap();
        let [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] =
            input_ids.map(|id| ds.type_store.get_type_info(id).kind)
        else {
            panic!("ICE: Non-int input of int-int arithmetic");
        };

        let [output_type_id] = ds.analyzer.value_types([op_io.outputs()[0]]).unwrap();
        let output_type_info = ds.type_store.get_type_info(output_type_id);
        let output_name = format!("{}", op_io.outputs()[0]);

        let TypeKind::Integer(output_int) = output_type_info.kind else {
            panic!("ICE: Non-int output of int-int arithmetic");
        };

        let a_val = value_store.load_value(self, a, ds)?.into_int_value();
        let b_val = value_store.load_value(self, b, ds)?.into_int_value();

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
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);
        let output_name = format!("{}", op_io.outputs()[0]);

        let a = op_io.inputs()[0];
        let a_val = value_store.load_value(self, a, ds)?.into_int_value();

        let res = self.builder.build_not(a_val, &output_name)?;
        value_store.store_value(self, op_io.outputs()[0], res.into())?;

        Ok(())
    }

    pub(super) fn build_compare(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        op_code: &OpCode<TypeResolvedOp>,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);

        let [a, b] = *op_io.inputs().as_arr();
        let input_types = ds.analyzer.value_types([a, b]).unwrap();
        let input_type_infos = input_types.map(|id| ds.type_store.get_type_info(id));

        let a_val = value_store.load_value(self, a, ds)?;
        let b_val = value_store.load_value(self, b, ds)?;
        let output_name = format!("{}", op_io.outputs()[0]);

        let (a_val, b_val, signed) = match input_type_infos.map(|ti| ti.kind) {
            [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] => {
                let to_int = promote_int_type_bidirectional(a_int, b_int).unwrap();
                let target_type = to_int.width.get_int_type(self.ctx);

                let a_val = a_val.into_int_value();
                let b_val = b_val.into_int_value();

                let a_val = self.cast_int(a_val, target_type, a_int.signed)?;
                let b_val = self.cast_int(b_val, target_type, b_int.signed)?;

                (a_val, b_val, to_int.signed)
            }
            [TypeKind::MultiPointer(_), TypeKind::MultiPointer(_)]
            | [TypeKind::SinglePointer(_), TypeKind::SinglePointer(_)] => todo!(),
            [TypeKind::Bool, TypeKind::Bool] => (
                a_val.into_int_value(),
                b_val.into_int_value(),
                IntSignedness::Unsigned,
            ),
            _ => unreachable!(),
        };

        let pred = op_code.get_predicate(signed);
        let res = self
            .builder
            .build_int_compare(pred, a_val, b_val, &output_name)?;
        value_store.store_value(self, op_io.outputs()[0], res.into())?;

        Ok(())
    }

    pub(super) fn build_is_null(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);
        let input_value_id = op_io.inputs()[0];
        let [input_type_id] = ds.analyzer.value_types([input_value_id]).unwrap();
        let input_type_info = ds.type_store.get_type_info(input_type_id);
        let (TypeKind::MultiPointer(ptee_id) | TypeKind::SinglePointer(ptee_id)) =
            input_type_info.kind
        else {
            unreachable!()
        };
        let ptee_type = self.get_type(ds.type_store, ptee_id);

        let ptr_val = value_store
            .load_value(self, input_value_id, ds)?
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
