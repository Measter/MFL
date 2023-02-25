use inkwell::AddressSpace;

use crate::{
    interners::Interners,
    opcode::{IntKind, Op},
    program::{
        static_analysis::Analyzer,
        type_store::{IntWidth, Signedness, TypeId, TypeKind, TypeStore},
        Program,
    },
};

use super::{CodeGen, ValueStore};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_cast(
        &mut self,
        program: &Program,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
        type_id: TypeId,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let type_info = type_store.get_type_info(type_id);
        match type_info.kind {
            TypeKind::Integer {
                width: output_width,
                signed: output_signed,
            } => {
                let input_id = op_io.inputs()[0];
                let input_type_id = analyzer.value_types([input_id]).unwrap()[0];
                let input_type_info = program.get_type_store().get_type_info(input_type_id);

                let input_data = value_store.load_value(
                    self,
                    input_id,
                    analyzer,
                    program.get_type_store(),
                    interner,
                );

                let output = match input_type_info.kind {
                    TypeKind::Integer {
                        signed: input_signed,
                        ..
                    } => {
                        let val = input_data.into_int_value();
                        let target_type = output_width.get_int_type(self.ctx);
                        self.cast_int(val, target_type, input_signed, output_signed)
                    }
                    TypeKind::Bool => {
                        let val = input_data.into_int_value();
                        let target_type = output_width.get_int_type(self.ctx);

                        self.cast_int(val, target_type, Signedness::Unsigned, output_signed)
                    }
                    TypeKind::Pointer => self.builder.build_ptr_to_int(
                        input_data.into_pointer_value(),
                        self.ctx.i64_type(),
                        "cast_ptr",
                    ),
                };

                value_store.store_value(self, op_io.outputs()[0], output.into());
            }
            TypeKind::Pointer => {
                let input_id = op_io.inputs()[0];
                let input_type_id = analyzer.value_types([input_id]).unwrap()[0];
                let input_type_info = program.get_type_store().get_type_info(input_type_id);
                let input_data = value_store.load_value(
                    self,
                    input_id,
                    analyzer,
                    program.get_type_store(),
                    interner,
                );

                let output = match input_type_info.kind {
                    TypeKind::Integer {
                        width: IntWidth::I64,
                        signed: Signedness::Unsigned,
                    } => self.builder.build_int_to_ptr(
                        input_data.into_int_value(),
                        self.ctx.i8_type().ptr_type(AddressSpace::default()),
                        "cast_int",
                    ),
                    TypeKind::Pointer => input_data.into_pointer_value(),

                    TypeKind::Integer { .. } | TypeKind::Bool => {
                        unreachable!()
                    }
                };

                value_store.store_value(self, op_io.outputs()[0], output.into());
            }
            TypeKind::Bool => unreachable!(),
        }
    }

    pub(super) fn build_dup_over(
        &mut self,
        program: &Program,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        for (&input_id, &output_id) in op_io.inputs().iter().zip(op_io.outputs()) {
            let value = value_store.load_value(
                self,
                input_id,
                analyzer,
                program.get_type_store(),
                interner,
            );
            value_store.store_value(self, output_id, value);
        }
    }

    pub(super) fn build_push_int(
        &mut self,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        op: &Op,
        width: IntWidth,
        value: IntKind,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let int_type = width.get_int_type(self.ctx);
        let value = match value {
            IntKind::Signed(v) => int_type
                .const_int(v as _, false)
                .const_cast(int_type, true)
                .into(),
            IntKind::Unsigned(v) => int_type
                .const_int(v, false)
                .const_cast(int_type, false)
                .into(),
        };
        value_store.store_value(self, op_io.outputs()[0], value);
    }

    pub(super) fn build_push_bool(
        &mut self,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        op: &Op,
        value: bool,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let value = self.ctx.bool_type().const_int(value as _, false).into();
        value_store.store_value(self, op_io.outputs()[0], value);
    }
}
