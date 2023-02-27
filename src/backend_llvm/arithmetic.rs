use inkwell::values::BasicValueEnum;

use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{Op, OpCode},
    program::{
        static_analysis::{promote_int_type, Analyzer},
        type_store::{Signedness, TypeKind, TypeStore},
    },
};

use super::{CodeGen, ValueStore};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_add_sub(
        &mut self,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let input_value_ids @ [a, b] = *op_io.inputs().as_arr();
        let input_type_ids = analyzer.value_types(input_value_ids).unwrap();
        let input_type_infos = input_type_ids.map(|id| type_store.get_type_info(id));

        let res: BasicValueEnum = match input_type_infos.map(|ti| ti.kind) {
            [TypeKind::Integer {
                signed: a_from_signed,
                ..
            }, TypeKind::Integer {
                signed: b_from_signed,
                ..
            }] => {
                let [output_type_id] = analyzer.value_types([op_io.outputs()[0]]).unwrap();
                let output_type_info = type_store.get_type_info(output_type_id);

                let TypeKind::Integer{ width: to_width, signed: to_signed } = output_type_info.kind else {
                                panic!("ICE: Non-int output of int-int arithmetic");
                            };

                let a_val = value_store
                    .load_value(self, a, analyzer, type_store, interner)
                    .into_int_value();
                let b_val = value_store
                    .load_value(self, b, analyzer, type_store, interner)
                    .into_int_value();

                let target_type = to_width.get_int_type(self.ctx);
                let a_val = self.cast_int(a_val, target_type, a_from_signed, to_signed);
                let b_val = self.cast_int(b_val, target_type, b_from_signed, to_signed);

                let (func, name) = op.code.get_arith_fn();
                func(&self.builder, a_val, b_val, name).into()
            }
            [TypeKind::Integer { signed, .. }, TypeKind::Pointer] => {
                assert!(matches!(op.code, OpCode::Add));
                assert_eq!(signed, Signedness::Unsigned);
                let offset = value_store
                    .load_value(self, a, analyzer, type_store, interner)
                    .into_int_value();

                let offset = self.cast_int(
                    offset,
                    self.ctx.i64_type(),
                    Signedness::Unsigned,
                    Signedness::Unsigned,
                );
                let ptr = value_store
                    .load_value(self, b, analyzer, type_store, interner)
                    .into_pointer_value();

                unsafe { self.builder.build_gep(ptr, &[offset], "ptr_offset") }.into()
            }
            [TypeKind::Pointer, TypeKind::Integer { signed, .. }] => {
                assert_eq!(signed, Signedness::Unsigned);
                let offset = value_store
                    .load_value(self, b, analyzer, type_store, interner)
                    .into_int_value();

                let offset = self.cast_int(
                    offset,
                    self.ctx.i64_type(),
                    Signedness::Unsigned,
                    Signedness::Unsigned,
                );
                let ptr = value_store
                    .load_value(self, a, analyzer, type_store, interner)
                    .into_pointer_value();

                // If we're subtracting, then we need to negate the offset.
                let offset = if let OpCode::Subtract = &op.code {
                    self.builder.build_int_neg(offset, "neg")
                } else {
                    offset
                };

                unsafe { self.builder.build_gep(ptr, &[offset], "ptr_offset") }.into()
            }
            [TypeKind::Pointer, TypeKind::Pointer] => {
                assert!(matches!(op.code, OpCode::Subtract));

                let lhs = value_store
                    .load_value(self, a, analyzer, type_store, interner)
                    .into_pointer_value();
                let rhs = value_store
                    .load_value(self, b, analyzer, type_store, interner)
                    .into_pointer_value();
                let diff = self.builder.build_ptr_diff(lhs, rhs, "ptr_diff");
                self.builder
                    .build_int_cast(diff, self.ctx.i64_type(), "wide_diff")
                    .into()
            }
            _ => panic!("ICE: Unexpected types"),
        };

        value_store.store_value(self, op_io.outputs()[0], res);
    }

    pub(super) fn build_multiply_and_or(
        &mut self,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let [a, b] = *op_io.inputs().as_arr();
        let input_type_ids = analyzer.value_types([a, b]).unwrap();
        let input_type_infos = input_type_ids.map(|ti| type_store.get_type_info(ti));
        let [output_type_id] = analyzer.value_types([op_io.outputs()[0]]).unwrap();
        let output_type_info = type_store.get_type_info(output_type_id);

        let a_val = value_store
            .load_value(self, a, analyzer, type_store, interner)
            .into_int_value();
        let b_val = value_store
            .load_value(self, b, analyzer, type_store, interner)
            .into_int_value();

        let (a_val, b_val) = if let TypeKind::Integer {
            width,
            signed: to_signed,
        } = output_type_info.kind
        {
            let [TypeKind::Integer {
                signed: a_signed,..
            }, TypeKind::Integer {
                signed: b_signed,..
            }] = input_type_infos.map(|ti| ti.kind) else {
                unreachable!()
            };

            let target_type = width.get_int_type(self.ctx);
            let a_val = self.cast_int(a_val, target_type, a_signed, to_signed);
            let b_val = self.cast_int(b_val, target_type, b_signed, to_signed);

            (a_val, b_val)
        } else {
            (a_val, b_val)
        };

        let (func, name) = op.code.get_arith_fn();
        let sum = func(&self.builder, a_val, b_val, name);
        value_store.store_value(self, op_io.outputs()[0], sum.into());
    }

    pub(super) fn build_div_rem(
        &mut self,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let inputs @ [a, b] = *op_io.inputs().as_arr();
        let input_type_ids = analyzer.value_types(inputs).unwrap();
        let [TypeKind::Integer {
            signed: a_signed,
            ..
        }, TypeKind::Integer {
            signed: b_signed,
            ..
        }] = input_type_ids.map(|id| type_store.get_type_info(id).kind) else {
            panic!("ICE: DivMod has non-int inputs");
        };

        let [output_type_id] = analyzer.value_types([op_io.outputs()[0]]).unwrap();
        let output_type_info = type_store.get_type_info(output_type_id);

        let TypeKind::Integer{ width: output_width, signed: output_signed } = output_type_info.kind else {
            panic!("ICE: Non-int output of int-int arithmetic");
        };

        let a_val = value_store
            .load_value(self, a, analyzer, type_store, interner)
            .into_int_value();
        let b_val = value_store
            .load_value(self, b, analyzer, type_store, interner)
            .into_int_value();

        let target_type = output_width.get_int_type(self.ctx);
        let a_val = self.cast_int(a_val, target_type, a_signed, output_signed);
        let b_val = self.cast_int(b_val, target_type, b_signed, output_signed);

        let (func, name) = op.code.get_div_rem_fn(output_signed);
        let res = func(&self.builder, a_val, b_val, name);

        let [res_val] = *op_io.outputs().as_arr();
        value_store.store_value(self, res_val, res.into());
    }

    pub(super) fn build_shift_left_right(
        &mut self,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let inputs @ [a, b] = *op_io.inputs().as_arr();
        let input_ids = analyzer.value_types(inputs).unwrap();
        let [TypeKind::Integer {
            signed: a_signed,
            ..
        }, TypeKind::Integer {
            signed: b_signed,
            ..
        }] = input_ids.map(|id| type_store.get_type_info(id).kind) else {
            panic!("ICE: Non-int input of int-int arithmetic");
        };

        let [output_type_id] = analyzer.value_types([op_io.outputs()[0]]).unwrap();
        let output_type_info = type_store.get_type_info(output_type_id);

        let TypeKind::Integer{ width: output_width, signed: output_signed } = output_type_info.kind else {
            panic!("ICE: Non-int output of int-int arithmetic");
        };

        let a_val = value_store
            .load_value(self, a, analyzer, type_store, interner)
            .into_int_value();
        let b_val = value_store
            .load_value(self, b, analyzer, type_store, interner)
            .into_int_value();

        let target_type = output_width.get_int_type(self.ctx);
        let a_val = self.cast_int(a_val, target_type, a_signed, output_signed);
        let b_val = self.cast_int(b_val, target_type, b_signed, output_signed);

        let res = match &op.code {
            OpCode::ShiftLeft => self.builder.build_left_shift(a_val, b_val, "shl"),
            OpCode::ShiftRight => self.builder.build_right_shift(
                a_val,
                b_val,
                output_signed == Signedness::Signed,
                "shr",
            ),
            _ => unreachable!(),
        };
        value_store.store_value(self, op_io.outputs()[0], res.into());
    }

    pub(super) fn build_bit_not(
        &mut self,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let a = op_io.inputs()[0];
        let a_val = value_store
            .load_value(self, a, analyzer, type_store, interner)
            .into_int_value();

        let res = self.builder.build_not(a_val, "not");
        value_store.store_value(self, op_io.outputs()[0], res.into());
    }

    pub(super) fn build_compare(
        &mut self,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let [a, b] = *op_io.inputs().as_arr();
        let input_types = analyzer.value_types([a, b]).unwrap();
        let input_type_infos = input_types.map(|id| type_store.get_type_info(id));

        let a_val = value_store.load_value(self, a, analyzer, type_store, interner);
        let b_val = value_store.load_value(self, b, analyzer, type_store, interner);

        let (a_val, b_val, signed) = match input_type_infos.map(|ti| ti.kind) {
            [TypeKind::Integer {
                width: a_width,
                signed: a_signed,
            }, TypeKind::Integer {
                width: b_width,
                signed: b_signed,
            }] => {
                let (to_signed, to_width) =
                    promote_int_type(a_width, a_signed, b_width, b_signed).unwrap();
                let target_type = to_width.get_int_type(self.ctx);

                let a_val = a_val.into_int_value();
                let b_val = b_val.into_int_value();

                let a_val = self.cast_int(a_val, target_type, a_signed, to_signed);
                let b_val = self.cast_int(b_val, target_type, b_signed, to_signed);

                (a_val, b_val, to_signed)
            }
            [TypeKind::Pointer, TypeKind::Pointer] => todo!(),
            [TypeKind::Bool, TypeKind::Bool] => (
                a_val.into_int_value(),
                b_val.into_int_value(),
                Signedness::Unsigned,
            ),
            _ => unreachable!(),
        };

        let (pred, name) = op.code.get_predicate(signed);
        let res = self.builder.build_int_compare(pred, a_val, b_val, name);
        value_store.store_value(self, op_io.outputs()[0], res.into());
    }
}
