use inkwell::{types::BasicType, values::BasicValue, AddressSpace};
use intcast::IntCast;
use lasso::Spur;

use crate::{
    interners::Interners,
    opcode::{IntKind, Op},
    program::static_analysis::Analyzer,
    type_store::{BuiltinTypes, IntWidth, Signedness, TypeId, TypeKind, TypeStore},
};

use super::{CodeGen, ValueStore};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_cast(
        &mut self,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
        to_type_id: TypeId,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let to_type_info = type_store.get_type_info(to_type_id);
        match to_type_info.kind {
            TypeKind::Integer {
                width: output_width,
                ..
            } => {
                let input_id = op_io.inputs()[0];
                let input_type_id = analyzer.value_types([input_id]).unwrap()[0];
                let input_type_info = type_store.get_type_info(input_type_id);

                let input_data =
                    value_store.load_value(self, input_id, analyzer, type_store, interner);

                let output = match input_type_info.kind {
                    TypeKind::Integer {
                        signed: input_signed,
                        ..
                    } => {
                        let val = input_data.into_int_value();
                        let target_type = output_width.get_int_type(self.ctx);
                        self.cast_int(val, target_type, input_signed)
                    }
                    TypeKind::Bool => {
                        let val = input_data.into_int_value();
                        let target_type = output_width.get_int_type(self.ctx);

                        self.cast_int(val, target_type, Signedness::Unsigned)
                    }
                    TypeKind::Pointer(_) => self.builder.build_ptr_to_int(
                        input_data.into_pointer_value(),
                        self.ctx.i64_type(),
                        "cast_ptr",
                    ),
                    TypeKind::Array { .. } | TypeKind::Struct(_) => unreachable!(),
                };

                value_store.store_value(self, op_io.outputs()[0], output.into());
            }
            TypeKind::Pointer(to_ptr_type) => {
                let input_id = op_io.inputs()[0];
                let input_type_id = analyzer.value_types([input_id]).unwrap()[0];
                let input_type_info = type_store.get_type_info(input_type_id);
                let input_data =
                    value_store.load_value(self, input_id, analyzer, type_store, interner);

                let output = match input_type_info.kind {
                    TypeKind::Integer {
                        width: IntWidth::I64,
                        signed: Signedness::Unsigned,
                    } => {
                        let ptr_type = self
                            .get_type(type_store, to_ptr_type)
                            .ptr_type(AddressSpace::default());
                        self.builder.build_int_to_ptr(
                            input_data.into_int_value(),
                            ptr_type,
                            "cast_int",
                        )
                    }
                    TypeKind::Pointer(_) => {
                        let to_ptr_type = self
                            .get_type(type_store, to_ptr_type)
                            .ptr_type(AddressSpace::default());
                        self.builder.build_pointer_cast(
                            input_data.into_pointer_value(),
                            to_ptr_type,
                            "cast_ptr",
                        )
                    }

                    TypeKind::Integer { .. }
                    | TypeKind::Bool
                    | TypeKind::Array { .. }
                    | TypeKind::Struct(_) => {
                        unreachable!()
                    }
                };

                value_store.store_value(self, op_io.outputs()[0], output.into());
            }
            TypeKind::Bool => unreachable!(),
            TypeKind::Array { .. } => unreachable!(),
            TypeKind::Struct(_) => unreachable!(),
        }
    }

    pub(super) fn build_dup_over(
        &mut self,
        interner: &mut Interners,
        type_store: &TypeStore,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        for (&input_id, &output_id) in op_io.inputs().iter().zip(op_io.outputs()) {
            let value = value_store.load_value(self, input_id, analyzer, type_store, interner);
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

    pub(super) fn build_push_str(
        &mut self,
        analyzer: &Analyzer,
        interner: &mut Interners,
        type_store: &TypeStore,
        value_store: &mut ValueStore<'ctx>,
        op: &Op,
        str_id: Spur,
        is_c_str: bool,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let str_ptr = value_store.get_string_literal(self, interner, str_id);

        let store_value = if is_c_str {
            str_ptr.as_basic_value_enum()
        } else {
            let string = interner.resolve_literal(str_id);
            let len = string.len() - 1; // It's null-terminated.
            let len_value = self.ctx.i64_type().const_int(len.to_u64(), false);

            let struct_type =
                self.get_type(type_store, type_store.get_builtin(BuiltinTypes::String).id);

            struct_type
                .into_struct_type()
                .const_named_struct(&[
                    len_value.as_basic_value_enum(),
                    str_ptr.as_basic_value_enum(),
                ])
                .as_basic_value_enum()
        };

        value_store.store_value(self, op_io.outputs()[0], store_value);
    }
}
