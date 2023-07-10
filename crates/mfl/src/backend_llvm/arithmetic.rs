use inkwell::{types::BasicType, values::BasicValueEnum, AddressSpace, IntPredicate};

use crate::{
    interners::Interner,
    n_ops::SliceNOps,
    opcode::{Op, OpCode},
    program::{
        static_analysis::{promote_int_type_bidirectional, Analyzer},
        Program,
    },
    type_store::{Signedness, TypeKind, TypeStore},
};

use super::{CodeGen, ValueStore};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_add_sub(
        &mut self,
        program: &Program,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let input_value_ids @ [a, b] = *op_io.inputs().as_arr();
        let input_type_ids = analyzer.value_types(input_value_ids).unwrap();
        let input_type_infos = input_type_ids.map(|id| type_store.get_type_info(id));

        let output_name = format!("{}", op_io.outputs()[0]);

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

                let TypeKind::Integer{ width: to_width, .. } = output_type_info.kind else {
                    panic!("ICE: Non-int output of int-int arithmetic");
                };

                let a_val = value_store
                    .load_value(self, a, analyzer, type_store, interner, program)
                    .into_int_value();
                let b_val = value_store
                    .load_value(self, b, analyzer, type_store, interner, program)
                    .into_int_value();

                let target_type = to_width.get_int_type(self.ctx);
                let a_val = self.cast_int(a_val, target_type, a_from_signed);
                let b_val = self.cast_int(b_val, target_type, b_from_signed);

                let func = op.code.get_arith_fn();
                func(&self.builder, a_val, b_val, &output_name).into()
            }
            [TypeKind::Integer { signed, .. }, TypeKind::Pointer(ptee_type)] => {
                assert!(matches!(op.code, OpCode::Add));
                assert_eq!(signed, Signedness::Unsigned);
                let offset = value_store
                    .load_value(self, a, analyzer, type_store, interner, program)
                    .into_int_value();

                let offset = self.cast_int(offset, self.ctx.i64_type(), Signedness::Unsigned);
                let ptr = value_store
                    .load_value(self, b, analyzer, type_store, interner, program)
                    .into_pointer_value();

                unsafe {
                    let ptee_type = self.get_type(type_store, ptee_type);
                    self.builder
                        .build_gep(ptee_type, ptr, &[offset], &output_name)
                }
                .into()
            }
            [TypeKind::Pointer(ptee_type), TypeKind::Integer { signed, .. }] => {
                assert_eq!(signed, Signedness::Unsigned);
                let offset = value_store
                    .load_value(self, b, analyzer, type_store, interner, program)
                    .into_int_value();

                let offset = self.cast_int(offset, self.ctx.i64_type(), Signedness::Unsigned);
                let ptr = value_store
                    .load_value(self, a, analyzer, type_store, interner, program)
                    .into_pointer_value();

                // If we're subtracting, then we need to negate the offset.
                let offset = if let OpCode::Subtract = &op.code {
                    self.builder.build_int_neg(offset, &output_name)
                } else {
                    offset
                };

                unsafe {
                    let ptee_type = self.get_type(type_store, ptee_type);
                    self.builder
                        .build_gep(ptee_type, ptr, &[offset], &output_name)
                }
                .into()
            }
            [TypeKind::Pointer(ptee_type), TypeKind::Pointer(_)] => {
                assert!(matches!(op.code, OpCode::Subtract));

                let lhs = value_store
                    .load_value(self, a, analyzer, type_store, interner, program)
                    .into_pointer_value();
                let rhs = value_store
                    .load_value(self, b, analyzer, type_store, interner, program)
                    .into_pointer_value();
                let ptee_type = self.get_type(type_store, ptee_type);
                let diff = self
                    .builder
                    .build_ptr_diff(ptee_type, lhs, rhs, &output_name);
                self.builder
                    .build_int_cast(diff, self.ctx.i64_type(), &output_name)
                    .into()
            }
            _ => panic!("ICE: Unexpected types"),
        };

        value_store.store_value(self, op_io.outputs()[0], res);
    }

    pub(super) fn build_multiply_and_or_xor(
        &mut self,
        program: &Program,
        interner: &mut Interner,
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
        let output_name = format!("{}", op_io.outputs()[0]);

        let a_val = value_store
            .load_value(self, a, analyzer, type_store, interner, program)
            .into_int_value();
        let b_val = value_store
            .load_value(self, b, analyzer, type_store, interner, program)
            .into_int_value();

        let (a_val, b_val) = if let TypeKind::Integer { width, .. } = output_type_info.kind {
            let [TypeKind::Integer {
                signed: a_signed,..
            }, TypeKind::Integer {
                signed: b_signed,..
            }] = input_type_infos.map(|ti| ti.kind) else {
                unreachable!()
            };

            let target_type = width.get_int_type(self.ctx);
            let a_val = self.cast_int(a_val, target_type, a_signed);
            let b_val = self.cast_int(b_val, target_type, b_signed);

            (a_val, b_val)
        } else {
            (a_val, b_val)
        };

        let func = op.code.get_arith_fn();
        let sum = func(&self.builder, a_val, b_val, &output_name);
        value_store.store_value(self, op_io.outputs()[0], sum.into());
    }

    pub(super) fn build_div_rem(
        &mut self,
        program: &Program,
        interner: &mut Interner,
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
        let output_name = format!("{}", op_io.outputs()[0]);

        let TypeKind::Integer{ width: output_width, signed: output_signed } = output_type_info.kind else {
            panic!("ICE: Non-int output of int-int arithmetic");
        };

        let a_val = value_store
            .load_value(self, a, analyzer, type_store, interner, program)
            .into_int_value();
        let b_val = value_store
            .load_value(self, b, analyzer, type_store, interner, program)
            .into_int_value();

        let target_type = output_width.get_int_type(self.ctx);
        let a_val = self.cast_int(a_val, target_type, a_signed);
        let b_val = self.cast_int(b_val, target_type, b_signed);

        let func = op.code.get_div_rem_fn(output_signed);
        let res = func(&self.builder, a_val, b_val, &output_name);

        let [res_val] = *op_io.outputs().as_arr();
        value_store.store_value(self, res_val, res.into());
    }

    pub(super) fn build_shift_left_right(
        &mut self,
        program: &Program,
        interner: &mut Interner,
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
        let output_name = format!("{}", op_io.outputs()[0]);

        let TypeKind::Integer{ width: output_width, signed: output_signed } = output_type_info.kind else {
            panic!("ICE: Non-int output of int-int arithmetic");
        };

        let a_val = value_store
            .load_value(self, a, analyzer, type_store, interner, program)
            .into_int_value();
        let b_val = value_store
            .load_value(self, b, analyzer, type_store, interner, program)
            .into_int_value();

        let target_type = output_width.get_int_type(self.ctx);
        let a_val = self.cast_int(a_val, target_type, a_signed);
        let b_val = self.cast_int(b_val, target_type, b_signed);

        let res = match &op.code {
            OpCode::ShiftLeft => self.builder.build_left_shift(a_val, b_val, &output_name),
            OpCode::ShiftRight => self.builder.build_right_shift(
                a_val,
                b_val,
                output_signed == Signedness::Signed,
                &output_name,
            ),
            _ => unreachable!(),
        };
        value_store.store_value(self, op_io.outputs()[0], res.into());
    }

    pub(super) fn build_bit_not(
        &mut self,
        program: &Program,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let output_name = format!("{}", op_io.outputs()[0]);

        let a = op_io.inputs()[0];
        let a_val = value_store
            .load_value(self, a, analyzer, type_store, interner, program)
            .into_int_value();

        let res = self.builder.build_not(a_val, &output_name);
        value_store.store_value(self, op_io.outputs()[0], res.into());
    }

    pub(super) fn build_compare(
        &mut self,
        program: &Program,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let [a, b] = *op_io.inputs().as_arr();
        let input_types = analyzer.value_types([a, b]).unwrap();
        let input_type_infos = input_types.map(|id| type_store.get_type_info(id));

        let a_val = value_store.load_value(self, a, analyzer, type_store, interner, program);
        let b_val = value_store.load_value(self, b, analyzer, type_store, interner, program);
        let output_name = format!("{}", op_io.outputs()[0]);

        let (a_val, b_val, signed) = match input_type_infos.map(|ti| ti.kind) {
            [TypeKind::Integer {
                width: a_width,
                signed: a_signed,
            }, TypeKind::Integer {
                width: b_width,
                signed: b_signed,
            }] => {
                let (to_signed, to_width) =
                    promote_int_type_bidirectional(a_width, a_signed, b_width, b_signed).unwrap();
                let target_type = to_width.get_int_type(self.ctx);

                let a_val = a_val.into_int_value();
                let b_val = b_val.into_int_value();

                let a_val = self.cast_int(a_val, target_type, a_signed);
                let b_val = self.cast_int(b_val, target_type, b_signed);

                (a_val, b_val, to_signed)
            }
            [TypeKind::Pointer(_), TypeKind::Pointer(_)] => todo!(),
            [TypeKind::Bool, TypeKind::Bool] => (
                a_val.into_int_value(),
                b_val.into_int_value(),
                Signedness::Unsigned,
            ),
            _ => unreachable!(),
        };

        let pred = op.code.get_predicate(signed);
        let res = self
            .builder
            .build_int_compare(pred, a_val, b_val, &output_name);
        value_store.store_value(self, op_io.outputs()[0], res.into());
    }

    pub(super) fn build_is_null(
        &mut self,
        program: &Program,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let input_value_id = op_io.inputs()[0];
        let [input_type_id] = analyzer.value_types([input_value_id]).unwrap();
        let input_type_info = type_store.get_type_info(input_type_id);
        let TypeKind::Pointer(ptee_id) = input_type_info.kind else { unreachable!() };
        let ptee_type = self.get_type(type_store, ptee_id);

        let ptr_val = value_store
            .load_value(
                self,
                input_value_id,
                analyzer,
                type_store,
                interner,
                program,
            )
            .into_pointer_value();

        let null_ptr = ptee_type.ptr_type(AddressSpace::default()).const_null();
        let zero = self.ctx.i64_type().const_zero();

        let name = format!("{}", op_io.outputs()[0]);
        let ptr_diff = self
            .builder
            .build_ptr_diff(ptee_type, ptr_val, null_ptr, &name);
        let result = self
            .builder
            .build_int_compare(IntPredicate::EQ, ptr_diff, zero, &name);

        value_store.store_value(self, op_io.outputs()[0], result.into());
    }
}
