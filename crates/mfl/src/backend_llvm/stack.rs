use inkwell::{values::BasicValue, AddressSpace};
use intcast::IntCast;
use lasso::Spur;

use crate::{
    context::ItemId,
    stores::{
        ops::OpId,
        types::{BuiltinTypes, IntKind, IntSignedness, IntWidth, Integer, TypeId, TypeKind},
    },
};

use super::{CodeGen, DataStore, InkwellResult, SsaMap};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_cast(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        to_type_id: TypeId,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);

        let to_type_info = ds.type_store.get_type_info(to_type_id);
        match to_type_info.kind {
            TypeKind::Integer(output_int) => {
                let input_id = op_io.inputs()[0];
                let input_type_id = ds.analyzer.value_types([input_id]).unwrap()[0];
                let input_type_info = ds.type_store.get_type_info(input_type_id);

                let input_data = value_store.load_value(self, input_id, ds)?;

                let output = match input_type_info.kind {
                    TypeKind::Integer(input_int) => {
                        let val = input_data.into_int_value();
                        let target_type = output_int.width.get_int_type(self.ctx);
                        self.cast_int(val, target_type, input_int.signed)?
                    }
                    TypeKind::Float(_) => todo!(),
                    TypeKind::Bool => {
                        let val = input_data.into_int_value();
                        let target_type = output_int.width.get_int_type(self.ctx);

                        self.cast_int(val, target_type, IntSignedness::Unsigned)?
                    }
                    TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) => {
                        self.builder.build_ptr_to_int(
                            input_data.into_pointer_value(),
                            self.ctx.i64_type(),
                            "cast_ptr",
                        )?
                    }
                    TypeKind::Array { .. }
                    | TypeKind::Struct(_)
                    | TypeKind::GenericStructBase(_)
                    | TypeKind::GenericStructInstance(_) => {
                        unreachable!()
                    }
                };

                value_store.store_value(self, op_io.outputs()[0], output.into())?;
            }
            TypeKind::Float(_) => todo!(),
            TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) => {
                let input_id = op_io.inputs()[0];
                let input_type_id = ds.analyzer.value_types([input_id]).unwrap()[0];
                let input_type_info = ds.type_store.get_type_info(input_type_id);
                let input_data = value_store.load_value(self, input_id, ds)?;

                let output = match input_type_info.kind {
                    TypeKind::Integer(IntKind::U64) => {
                        let ptr_type = self.ctx.ptr_type(AddressSpace::default());
                        self.builder.build_int_to_ptr(
                            input_data.into_int_value(),
                            ptr_type,
                            "cast_int",
                        )?
                    }
                    TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) => {
                        let to_ptr_type = self.ctx.ptr_type(AddressSpace::default());
                        self.builder.build_pointer_cast(
                            input_data.into_pointer_value(),
                            to_ptr_type,
                            "cast_ptr",
                        )?
                    }

                    TypeKind::Integer { .. }
                    | TypeKind::Float(_)
                    | TypeKind::Bool
                    | TypeKind::Array { .. }
                    | TypeKind::Struct(_)
                    | TypeKind::GenericStructBase(_)
                    | TypeKind::GenericStructInstance(_) => {
                        unreachable!()
                    }
                };

                value_store.store_value(self, op_io.outputs()[0], output.into())?;
            }
            TypeKind::Bool
            | TypeKind::Array { .. }
            | TypeKind::Struct(_)
            | TypeKind::GenericStructBase(_)
            | TypeKind::GenericStructInstance(_) => unreachable!(),
        }

        Ok(())
    }

    pub(super) fn build_dup_over(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);

        for (&input_id, &output_id) in op_io.inputs().iter().zip(op_io.outputs()) {
            let value = value_store.load_value(self, input_id, ds)?;
            value_store.store_value(self, output_id, value)?;
        }

        Ok(())
    }

    pub(super) fn build_push_int(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        width: IntWidth,
        value: Integer,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);

        let int_type = width.get_int_type(self.ctx);
        let value = match value {
            Integer::Signed(v) => int_type
                .const_int(v as _, false)
                .const_cast(int_type, true)
                .into(),
            Integer::Unsigned(v) => int_type
                .const_int(v, false)
                .const_cast(int_type, false)
                .into(),
        };
        value_store.store_value(self, op_io.outputs()[0], value)?;

        Ok(())
    }

    pub(super) fn build_push_bool(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        value: bool,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);

        let value = self.ctx.bool_type().const_int(value as _, false).into();
        value_store.store_value(self, op_io.outputs()[0], value)?;

        Ok(())
    }

    pub(super) fn build_push_str(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        str_id: Spur,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);
        let str_ptr = value_store.get_string_literal(self, ds, str_id)?;

        let string = ds.strings_store.resolve(str_id);
        let len = string.len() - 1; // It's null-terminated.
        let len_value = self.ctx.i64_type().const_int(len.to_u64(), false);

        let struct_type = self.get_type(
            ds.type_store,
            ds.type_store.get_builtin(BuiltinTypes::String).id,
        );

        let store_value = struct_type
            .into_struct_type()
            .const_named_struct(&[
                len_value.as_basic_value_enum(),
                str_ptr.as_basic_value_enum(),
            ])
            .as_basic_value_enum();

        value_store.store_value(self, op_io.outputs()[0], store_value)?;

        Ok(())
    }

    pub(super) fn build_const(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        const_id: ItemId,
    ) -> InkwellResult {
        let op_io = ds.op_store.get_op_io(op_id);
        let output_ids = op_io.outputs();

        let Some(const_vals) = ds.context.get_consts(const_id) else {
            panic!("ICE: Const wasn't ready during codegen");
        };

        for (&out_id, sim_val) in output_ids.iter().zip(const_vals) {
            use crate::simulate::SimulatorValue;
            // These can't use the build_push_bool and build_push_int functions above because they
            // assume a single output value.
            match sim_val {
                SimulatorValue::Int { width, kind } => {
                    let int_type = width.get_int_type(self.ctx);
                    let value = match kind {
                        Integer::Signed(v) => int_type
                            .const_int(*v as _, false)
                            .const_cast(int_type, true)
                            .into(),
                        Integer::Unsigned(v) => int_type
                            .const_int(*v, false)
                            .const_cast(int_type, false)
                            .into(),
                    };

                    value_store.store_value(self, out_id, value)?;
                }
                SimulatorValue::Bool(b) => {
                    let value = self.ctx.bool_type().const_int(*b as _, false).into();
                    value_store.store_value(self, out_id, value)?;
                }
            }
        }

        Ok(())
    }
}
