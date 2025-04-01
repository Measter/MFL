use inkwell::{
    values::{BasicValue, FunctionValue},
    AddressSpace,
};
use intcast::IntCast;
use lasso::Spur;
use stores::items::ItemId;

use crate::stores::{
    item::ItemAttribute,
    ops::OpId,
    types::{
        BuiltinTypes, Float, FloatWidth, IntKind, IntSignedness, IntWidth, Integer, TypeId,
        TypeKind,
    },
    Stores,
};

use super::{CodeGen, InkwellResult, SsaMap};

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_cast(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        to_type_id: TypeId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let to_type_info = ds.types.get_type_info(to_type_id);
        match to_type_info.kind {
            TypeKind::Integer(output_int) => {
                let input_id = op_io.inputs()[0];
                let input_type_id = ds.values.value_types([input_id]).unwrap()[0];
                let input_type_info = ds.types.get_type_info(input_type_id);

                let input_data = value_store.load_value(self, input_id, ds.values, ds.types)?;

                let output = match input_type_info.kind {
                    TypeKind::Integer(input_int) => {
                        let val = input_data.into_int_value();
                        let target_type = output_int.width.get_int_type(self.ctx);
                        self.cast_int(val, target_type, input_int.signed)?
                    }
                    TypeKind::Enum(_) => {
                        let val = input_data.into_int_value();
                        let target_type = output_int.width.get_int_type(self.ctx);
                        self.cast_int(val, target_type, IntSignedness::Unsigned)?
                    }
                    TypeKind::Float(_) => {
                        let val = input_data.into_float_value();
                        let target_type = output_int.width.get_int_type(self.ctx);
                        match output_int.signed {
                            IntSignedness::Signed => {
                                self.builder
                                    .build_float_to_signed_int(val, target_type, "")?
                            }
                            IntSignedness::Unsigned => {
                                self.builder
                                    .build_float_to_unsigned_int(val, target_type, "")?
                            }
                        }
                    }
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
                    | TypeKind::GenericStructInstance(_)
                    | TypeKind::FunctionPointer => {
                        unreachable!()
                    }
                };

                value_store.store_value(self, op_io.outputs()[0], output.into())?;
            }
            TypeKind::Float(output_float) => {
                let input_id = op_io.inputs()[0];
                let input_type_id = ds.values.value_types([input_id]).unwrap()[0];
                let input_type_info = ds.types.get_type_info(input_type_id);

                let input_data = value_store.load_value(self, input_id, ds.values, ds.types)?;

                let output = match input_type_info.kind {
                    TypeKind::Integer(input_int) => {
                        let val = input_data.into_int_value();
                        let target_type = output_float.get_float_type(self.ctx);
                        match input_int.signed {
                            IntSignedness::Signed => {
                                self.builder
                                    .build_signed_int_to_float(val, target_type, "")?
                            }
                            IntSignedness::Unsigned => {
                                self.builder
                                    .build_unsigned_int_to_float(val, target_type, "")?
                            }
                        }
                    }
                    TypeKind::Float(_) => {
                        let val = input_data.into_float_value();
                        let target_type = output_float.get_float_type(self.ctx);
                        self.builder.build_float_cast(val, target_type, "")?
                    }

                    TypeKind::Array { .. }
                    | TypeKind::MultiPointer(_)
                    | TypeKind::SinglePointer(_)
                    | TypeKind::Bool
                    | TypeKind::Struct(_)
                    | TypeKind::GenericStructBase(_)
                    | TypeKind::GenericStructInstance(_)
                    | TypeKind::Enum(_)
                    | TypeKind::FunctionPointer => unreachable!(),
                };

                value_store.store_value(self, op_io.outputs[0], output.into())?;
            }
            TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) => {
                let input_id = op_io.inputs()[0];
                let input_type_id = ds.values.value_types([input_id]).unwrap()[0];
                let input_type_info = ds.types.get_type_info(input_type_id);
                let input_data = value_store.load_value(self, input_id, ds.values, ds.types)?;

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
                    | TypeKind::GenericStructInstance(_)
                    | TypeKind::Enum(_)
                    | TypeKind::FunctionPointer => {
                        unreachable!()
                    }
                };

                value_store.store_value(self, op_io.outputs()[0], output.into())?;
            }
            TypeKind::Bool
            | TypeKind::Array { .. }
            | TypeKind::Struct(_)
            | TypeKind::GenericStructBase(_)
            | TypeKind::GenericStructInstance(_)
            | TypeKind::Enum(_)
            | TypeKind::FunctionPointer => unreachable!(),
        }

        Ok(())
    }

    pub(super) fn build_dup_over_rotate_swap_reverse(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        for (&input_id, &output_id) in op_io.inputs().iter().zip(op_io.outputs()) {
            let value = value_store.load_value(self, input_id, ds.values, ds.types)?;
            value_store.store_value(self, output_id, value)?;
        }

        Ok(())
    }

    pub(super) fn build_push_int(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        width: IntWidth,
        value: Integer,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

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
    pub(super) fn build_push_float(
        &self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        width: FloatWidth,
        value: Float,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let float_type = width.get_float_type(self.ctx);
        let value = float_type
            .const_float(value.0)
            .const_cast(float_type)
            .into();
        value_store.store_value(self, op_io.outputs[0], value)?;

        Ok(())
    }

    pub(super) fn build_push_bool(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        value: bool,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let value = self.ctx.bool_type().const_int(value as _, false).into();
        value_store.store_value(self, op_io.outputs()[0], value)?;

        Ok(())
    }

    pub(super) fn build_push_str(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        str_id: Spur,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let str_ptr = value_store.get_string_literal(self, ds.strings, str_id)?;

        let string = ds.strings.get_escaped_string(str_id).unwrap();
        let len = string.string.len() - 1; // It's null-terminated.
        let len_value = self.ctx.i64_type().const_int(len.to_u64(), false);

        let type_id = ds.types.get_builtin(BuiltinTypes::String).id;
        let struct_type = self.get_type(ds.types, type_id);

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

    pub(super) fn build_here(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        item_id: ItemId,
        function: FunctionValue<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_loc = ds.ops.get_token(op_id).location;
        let this_header = ds.items.get_item_header(item_id);

        let store_value = if this_header.attributes.contains(ItemAttribute::TrackCaller) {
            function.get_last_param().unwrap()
        } else {
            self.get_here_string(ds, value_store, op_loc)?
        };

        let op_io = ds.ops.get_op_io(op_id);
        value_store.store_value(self, op_io.outputs()[0], store_value)?;

        Ok(())
    }

    pub(super) fn build_const(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        const_id: ItemId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let output_ids = op_io.outputs();

        let Some(const_vals) = ds.items.get_consts(const_id) else {
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
                SimulatorValue::EnumValue { discrim, .. } => {
                    let value = self.ctx.i16_type().const_int(*discrim as _, false).into();
                    value_store.store_value(self, out_id, value)?;
                }
            }
        }

        Ok(())
    }
}
