use ariadne::Cache;
use inkwell::{
    types::BasicMetadataTypeEnum,
    values::{
        AggregateValue, AggregateValueEnum, BasicMetadataValueEnum, BasicValue, FunctionValue,
        IntValue, PointerValue, StructValue,
    },
    AddressSpace, IntPredicate,
};
use intcast::IntCast;
use lasso::Spur;
use stores::{items::ItemId, source::Spanned, strings::StringStore};

use crate::{
    n_ops::SliceNOps,
    stores::{
        ops::OpId,
        types::{BuiltinTypes, IntSignedness, TypeId, TypeInfo, TypeKind, TypeStore},
        values::ValueId,
        Stores,
    },
};

use super::{CodeGen, InkwellResult, SsaMap};

enum ArrayPtrKind {
    Indirect, // T[N]&
    Direct,   // T&
}

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_variable(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        item_id: ItemId,
        is_global: bool,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let ptr = if is_global {
            self.get_global_variable(item_id).as_pointer_value()
        } else {
            value_store.variable_map[&item_id]
        };
        value_store.store_value(self, op_io.outputs()[0], ptr.into())?;

        Ok(())
    }

    pub(super) fn build_init_array(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        count: u32,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let output_value_id = op_io.outputs()[0];
        let [output_type_id] = ds.values.value_types([output_value_id]).unwrap();

        let aggr_llvm_type = self.get_type(ds.types, output_type_id);
        let aggr_value = aggr_llvm_type
            .const_zero()
            .into_array_value()
            .as_aggregate_value_enum();
        let input_value = value_store.load_value(self, op_io.inputs[0], ds.values, ds.types)?;

        let array = (0..count).fold(aggr_value, |aggr, idx| {
            self.builder
                .build_insert_value(aggr, input_value, idx, "")
                .unwrap()
        });

        value_store.store_value(self, output_value_id, array.as_basic_value_enum())?;

        Ok(())
    }

    fn build_pack_aggregate(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        mut aggr_value: AggregateValueEnum<'ctx>,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let output_id = op_io.outputs()[0];
        let [output_type_id] = ds.values.value_types([output_id]).unwrap();
        let output_type_info = ds.types.get_type_info(output_type_id);

        for (value_id, idx) in op_io.inputs().iter().zip(0..) {
            let [input_type_id] = ds.values.value_types([*value_id]).unwrap();
            let input_type_info = ds.types.get_type_info(input_type_id);

            let field_store_type_info = match output_type_info.kind {
                TypeKind::Array { type_id, .. } => ds.types.get_type_info(type_id),
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                    let struct_info = ds.types.get_struct_def(output_type_id);
                    let field_kind = struct_info.fields[idx].kind;
                    ds.types.get_type_info(field_kind.inner)
                }
                _ => unreachable!(),
            };

            let value = value_store.load_value(self, *value_id, ds.values, ds.types)?;
            let value = if let (TypeKind::Integer(to_int), TypeKind::Integer(from_int)) =
                (field_store_type_info.kind, input_type_info.kind)
            {
                self.cast_int(
                    value.into_int_value(),
                    to_int.width.get_int_type(self.ctx),
                    from_int.signed,
                )?
                .as_basic_value_enum()
            } else {
                value
            };

            aggr_value = self
                .builder
                .build_insert_value(aggr_value, value, idx.to_u32().unwrap(), "insert")
                .unwrap();
        }

        value_store.store_value(self, output_id, aggr_value.as_basic_value_enum())?;
        Ok(())
    }

    fn build_pack_union(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let output_id = op_io.outputs()[0];
        let input_id = op_io.inputs()[0];
        let [output_type_id] = ds.values.value_types([output_id]).unwrap();

        let union_type = self.get_type(ds.types, output_type_id).into_array_type();
        // We need to alloca the union, then cast its pointer.
        let data_ptr_type = self.ctx.ptr_type(AddressSpace::default());

        let union_alloc = value_store.new_alloca(self, ds.types, output_type_id)?;
        let value_ptr = self
            .builder
            .build_pointer_cast(union_alloc, data_ptr_type, "")?;
        let input_value = value_store.load_value(self, input_id, ds.values, ds.types)?;
        self.builder.build_store(value_ptr, input_value)?;

        let union_value = self.builder.build_load(union_type, union_alloc, "")?;
        value_store.store_value(self, output_id, union_value)?;

        Ok(())
    }

    pub(super) fn build_pack(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let output_id = op_io.outputs()[0];
        let [output_type_id] = ds.values.value_types([output_id]).unwrap();
        let output_type_info = ds.types.get_type_info(output_type_id);

        let aggr_llvm_type = self.get_type(ds.types, output_type_id);
        let aggr_value = aggr_llvm_type.const_zero();
        match output_type_info.kind {
            TypeKind::Array { .. } => {
                let aggr_value = aggr_value.into_array_value().as_aggregate_value_enum();
                self.build_pack_aggregate(ds, value_store, op_id, aggr_value)?;
            }
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let struct_info = ds.types.get_struct_def(output_type_id);
                if struct_info.is_union {
                    self.build_pack_union(ds, value_store, op_id)?;
                } else {
                    let aggr_value = aggr_value.into_struct_value().as_aggregate_value_enum();
                    self.build_pack_aggregate(ds, value_store, op_id, aggr_value)?;
                }
            }
            _ => unreachable!(),
        }

        Ok(())
    }

    pub(super) fn build_unpack(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let input_value_id = op_io.inputs()[0];
        let [input_type_id] = ds.values.value_types([input_value_id]).unwrap();
        let input_type_info = ds.types.get_type_info(input_type_id);

        let aggr = value_store.load_value(self, input_value_id, ds.values, ds.types)?;

        let aggr = match input_type_info.kind {
            TypeKind::Array { .. } => aggr.into_array_value().as_aggregate_value_enum(),
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                aggr.into_struct_value().as_aggregate_value_enum()
            }
            _ => unreachable!(),
        };

        for (output_value_id, idx) in op_io.outputs().iter().zip(0..) {
            let output_value = self
                .builder
                .build_extract_value(aggr, idx, &format!("{output_value_id}"))
                .unwrap();

            value_store.store_value(self, *output_value_id, output_value)?;
        }

        Ok(())
    }

    fn build_bounds_check(
        &mut self,
        ds: &mut Stores,
        op_id: OpId,
        function: FunctionValue,
        idx: IntValue,
        length: IntValue,
    ) -> InkwellResult {
        let current_block = self.builder.get_insert_block().unwrap();
        let success_block = self
            .ctx
            .append_basic_block(function, "bounds_check_success");
        let fail_block = self.ctx.append_basic_block(function, "bounds_check_fail");

        self.builder.position_at_end(current_block);
        let cmp_res =
            self.builder
                .build_int_compare(IntPredicate::ULT, idx, length, "bounds_check_cmp")?;

        self.builder
            .build_conditional_branch(cmp_res, success_block, fail_block)?;

        self.builder.position_at_end(fail_block);
        // Crash and burn
        let op_loc = ds.ops.get_token_location(op_id);
        let file_name = ds.source.name(op_loc.file_id);
        let (_, line, column) = (&*ds.source)
            .fetch(&op_loc.file_id)
            .unwrap()
            .get_offset_line(op_loc.source_start.to_usize())
            .unwrap();
        let location_string = format!("{file_name}:{}:{}", line + 1, column + 1);
        let string = self
            .builder
            .build_global_string_ptr(&location_string, "oob_loc")?;
        let string_pointer = string
            .as_pointer_value()
            .const_cast(self.ctx.ptr_type(AddressSpace::default()));

        let type_id = ds.types.get_builtin(BuiltinTypes::String).id;
        let str_type = self.get_type(ds.types, type_id).into_struct_type();
        let str_value = str_type.const_named_struct(&[
            self.ctx
                .i64_type()
                .const_int(location_string.len().to_u64(), false)
                .into(),
            string_pointer.into(),
        ]);

        let args = [str_value.into(), idx.into(), length.into()];

        self.builder.build_call(self.oob_handler, &args, "oob")?;
        self.builder.build_unreachable()?;

        self.builder.position_at_end(success_block);

        Ok(())
    }

    fn get_slice_like_struct_fields(
        &mut self,
        types: &mut TypeStore,
        strings: &mut StringStore,
        struct_value_id: ValueId,
        struct_type_id: TypeId,
        struct_value: StructValue<'ctx>,
    ) -> InkwellResult<(PointerValue<'ctx>, TypeInfo, IntValue<'ctx>)> {
        let struct_def = types.get_struct_def(struct_type_id);

        let pointer_field_name = strings.intern("pointer");
        let (ptr_field_idx, ptr_field_info) = struct_def
            .fields
            .iter()
            .enumerate()
            .find(|(_, fi)| fi.name.inner == pointer_field_name)
            .unwrap();

        let (TypeKind::MultiPointer(store_type) | TypeKind::SinglePointer(store_type)) =
            types.get_type_info(ptr_field_info.kind.inner).kind
        else {
            unreachable!()
        };

        let ptr_name = format!("{struct_value_id}_pointer");
        let ptr_value = self
            .builder
            .build_extract_value(struct_value, ptr_field_idx.to_u32().unwrap(), &ptr_name)?
            .into_pointer_value();

        let length_field_name = strings.intern("length");
        let length_field_idx = struct_def
            .fields
            .iter()
            .position(|fi| fi.name.inner == length_field_name)
            .unwrap();

        let length_name = format!("{struct_value_id}_length");
        let length_value = self
            .builder
            .build_extract_value(
                struct_value,
                length_field_idx.to_u32().unwrap(),
                &length_name,
            )?
            .into_int_value();

        Ok((ptr_value, types.get_type_info(store_type), length_value))
    }

    pub(super) fn build_extract_array(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        function: FunctionValue<'ctx>,
        op_id: OpId,
        emit_array: bool,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id).clone();
        let [array_value_id, idx_value_id] = *op_io.inputs().as_arr();
        let array_val = value_store.load_value(self, array_value_id, ds.values, ds.types)?;
        let idx_val = value_store.load_value(self, idx_value_id, ds.values, ds.types)?;

        let [array_type_id] = ds.values.value_types([array_value_id]).unwrap();
        let array_type_info = ds.types.get_type_info(array_type_id);

        let (arr_ptr, length, ptr_kind, arr_ptee_kind, stored_kind) = match array_type_info.kind {
            TypeKind::Array {
                length,
                type_id: stored_ptee_type,
            } => {
                // Ugh, this sucks!
                let store_location = value_store.new_alloca(self, ds.types, array_type_id)?;
                self.builder.build_store(store_location, array_val)?;

                let length_value = self.ctx.i64_type().const_int(length.to_u64(), false);

                (
                    store_location,
                    length_value,
                    ArrayPtrKind::Indirect,
                    array_type_id,
                    stored_ptee_type,
                )
            }
            TypeKind::MultiPointer(sub_type_id) | TypeKind::SinglePointer(sub_type_id) => {
                let sub_type_info = ds.types.get_type_info(sub_type_id);
                match sub_type_info.kind {
                    TypeKind::Array {
                        length,
                        type_id: stored_ptee_type,
                    } => {
                        let length_value = self.ctx.i64_type().const_int(length.to_u64(), false);

                        (
                            array_val.into_pointer_value(),
                            length_value,
                            ArrayPtrKind::Indirect,
                            sub_type_id,
                            stored_ptee_type,
                        )
                    }
                    TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                        let ptee_type = self.get_type(ds.types, sub_type_id);
                        let struct_val = self.builder.build_load(
                            ptee_type,
                            array_val.into_pointer_value(),
                            "",
                        )?;
                        let (ptr_field, store_type_info, length) = self
                            .get_slice_like_struct_fields(
                                ds.types,
                                ds.strings,
                                array_value_id,
                                sub_type_id,
                                struct_val.into_struct_value(),
                            )?;
                        (
                            ptr_field,
                            length,
                            ArrayPtrKind::Direct,
                            store_type_info.id,
                            store_type_info.id,
                        )
                    }
                    _ => unreachable!(),
                }
            }
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let (ptr_field, store_type_info, length) = self.get_slice_like_struct_fields(
                    ds.types,
                    ds.strings,
                    array_value_id,
                    array_type_id,
                    array_val.into_struct_value(),
                )?;

                (
                    ptr_field,
                    length,
                    ArrayPtrKind::Direct,
                    store_type_info.id,
                    store_type_info.id,
                )
            }
            _ => unreachable!(),
        };

        let idx_val = self.cast_int(
            idx_val.into_int_value(),
            self.ctx.i64_type(),
            IntSignedness::Unsigned,
        )?;

        self.build_bounds_check(ds, op_id, function, idx_val, length)?;

        let idxs = [self.ctx.i64_type().const_zero(), idx_val];
        let offset_idxs: &[IntValue] = match ptr_kind {
            ArrayPtrKind::Indirect => &idxs,
            ArrayPtrKind::Direct => &idxs[1..],
        };

        let offset_ptr = unsafe {
            let ptee_type = self.get_type(ds.types, arr_ptee_kind);
            self.builder
                .build_in_bounds_gep(ptee_type, arr_ptr, offset_idxs, "")?
        };

        let output_value_id = if emit_array {
            let output_array_id = op_io.outputs()[0];
            value_store.store_value(self, output_array_id, array_val)?;
            op_io.outputs()[1]
        } else {
            op_io.outputs()[0]
        };

        let output_value_name = format!("{output_value_id}");
        let ptee_type = self.get_type(ds.types, stored_kind);
        let loaded_value = self
            .builder
            .build_load(ptee_type, offset_ptr, &output_value_name)?;
        value_store.store_value(self, output_value_id, loaded_value)?;

        Ok(())
    }

    pub(super) fn build_index(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        function: FunctionValue<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id).clone();
        let [idx_value_id, array_value_id] = *op_io.inputs().as_arr();
        let output_value_id = op_io.outputs[0];
        let idx_val = value_store.load_value(self, idx_value_id, ds.values, ds.types)?;
        let array_val = value_store.load_value(self, array_value_id, ds.values, ds.types)?;

        let [array_type_id] = ds.values.value_types([array_value_id]).unwrap();
        let array_type_info = ds.types.get_type_info(array_type_id);

        let (arr_ptr, length, ptr_kind, ptee_type_id) = match array_type_info.kind {
            TypeKind::MultiPointer(sub_type_id) | TypeKind::SinglePointer(sub_type_id) => {
                let sub_type_info = ds.types.get_type_info(sub_type_id);
                match sub_type_info.kind {
                    TypeKind::Array { length, .. } => {
                        let length_value = self.ctx.i64_type().const_int(length.to_u64(), false);
                        (
                            array_val.into_pointer_value(),
                            length_value,
                            ArrayPtrKind::Indirect,
                            sub_type_id,
                        )
                    }
                    TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                        let ptee_type = self.get_type(ds.types, sub_type_id);
                        let struct_val = self.builder.build_load(
                            ptee_type,
                            array_val.into_pointer_value(),
                            "",
                        )?;
                        let (ptr_field, store_type_info, length) = self
                            .get_slice_like_struct_fields(
                                ds.types,
                                ds.strings,
                                array_value_id,
                                sub_type_id,
                                struct_val.into_struct_value(),
                            )?;
                        (ptr_field, length, ArrayPtrKind::Direct, store_type_info.id)
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        };

        let idx_val = self.cast_int(
            idx_val.into_int_value(),
            self.ctx.i64_type(),
            IntSignedness::Unsigned,
        )?;

        self.build_bounds_check(ds, op_id, function, idx_val, length)?;

        let idxs = [self.ctx.i64_type().const_zero(), idx_val];
        let idxs: &[IntValue] = match ptr_kind {
            ArrayPtrKind::Indirect => &idxs,
            ArrayPtrKind::Direct => &idxs[1..],
        };
        let offset_ptr = unsafe {
            let ptee_type = self.get_type(ds.types, ptee_type_id);
            self.builder
                .build_in_bounds_gep(ptee_type, arr_ptr, idxs, "")?
        };

        value_store.store_value(self, output_value_id, offset_ptr.into())?;

        Ok(())
    }

    pub(super) fn build_insert_array(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        function: FunctionValue<'ctx>,
        op_id: OpId,
        emit_array: bool,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id).clone();
        let [data_value_id, array_value_id, idx_value_id] = *op_io.inputs().as_arr();
        let data_val = value_store.load_value(self, data_value_id, ds.values, ds.types)?;
        let array_val = value_store.load_value(self, array_value_id, ds.values, ds.types)?;
        let idx_val = value_store.load_value(self, idx_value_id, ds.values, ds.types)?;

        let [data_type_id, array_type_id] = ds
            .values
            .value_types([data_value_id, array_value_id])
            .unwrap();
        let array_type_info = ds.types.get_type_info(array_type_id);
        let data_type_info = ds.types.get_type_info(data_type_id);

        let (arr_ptr, store_type_info, length, ptr_kind, ptee_kind) = match array_type_info.kind {
            TypeKind::Array { type_id, length } => {
                // Ugh, this sucks!
                let store_location = value_store.new_alloca(self, ds.types, array_type_id)?;
                self.builder.build_store(store_location, array_val)?;
                let store_type_info = ds.types.get_type_info(type_id);

                let length_value = self.ctx.i64_type().const_int(length.to_u64(), false);

                (
                    store_location,
                    store_type_info,
                    length_value,
                    ArrayPtrKind::Indirect,
                    array_type_id,
                )
            }
            TypeKind::MultiPointer(sub_type_id) | TypeKind::SinglePointer(sub_type_id) => {
                let sub_type_info = ds.types.get_type_info(sub_type_id);
                match sub_type_info.kind {
                    TypeKind::Array {
                        type_id: store_type_id,
                        length,
                    } => {
                        let store_type_info = ds.types.get_type_info(store_type_id);
                        let length_value = self.ctx.i64_type().const_int(length.to_u64(), false);

                        (
                            array_val.into_pointer_value(),
                            store_type_info,
                            length_value,
                            ArrayPtrKind::Indirect,
                            sub_type_id,
                        )
                    }
                    TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                        let ptee_type = self.get_type(ds.types, sub_type_id);
                        let struct_val = self.builder.build_load(
                            ptee_type,
                            array_val.into_pointer_value(),
                            "",
                        )?;
                        let (ptr_field, store_type_info, length) = self
                            .get_slice_like_struct_fields(
                                ds.types,
                                ds.strings,
                                array_value_id,
                                sub_type_id,
                                struct_val.into_struct_value(),
                            )?;
                        (
                            ptr_field,
                            store_type_info,
                            length,
                            ArrayPtrKind::Direct,
                            store_type_info.id,
                        )
                    }
                    _ => unreachable!(),
                }
            }
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let (ptr_field, store_type_info, length) = self.get_slice_like_struct_fields(
                    ds.types,
                    ds.strings,
                    array_value_id,
                    array_type_id,
                    array_val.into_struct_value(),
                )?;
                (
                    ptr_field,
                    store_type_info,
                    length,
                    ArrayPtrKind::Direct,
                    store_type_info.id,
                )
            }
            _ => unreachable!(),
        };

        let idx_val = self.cast_int(
            idx_val.into_int_value(),
            self.ctx.i64_type(),
            IntSignedness::Unsigned,
        )?;

        self.build_bounds_check(ds, op_id, function, idx_val, length)?;

        // And finally actually build the insert
        let idxs = [self.ctx.i64_type().const_zero(), idx_val];
        let offset_idxs: &[IntValue] = match ptr_kind {
            ArrayPtrKind::Indirect => &idxs,
            ArrayPtrKind::Direct => &idxs[1..],
        };

        let offset_ptr = unsafe {
            let ptee_type = self.get_type(ds.types, ptee_kind);
            self.builder
                .build_in_bounds_gep(ptee_type, arr_ptr, offset_idxs, "")?
        };

        let data_val = if let (TypeKind::Integer(to_int), TypeKind::Integer(from_int)) =
            (store_type_info.kind, data_type_info.kind)
        {
            self.cast_int(
                data_val.into_int_value(),
                to_int.width.get_int_type(self.ctx),
                from_int.signed,
            )?
            .as_basic_value_enum()
        } else {
            data_val
        };

        self.builder.build_store(offset_ptr, data_val)?;

        if emit_array {
            if let TypeKind::Array { .. } = array_type_info.kind {
                let array_type = self.get_type(ds.types, array_type_id);
                let cast_ptr = self.builder.build_pointer_cast(
                    arr_ptr,
                    self.ctx.ptr_type(AddressSpace::default()),
                    "",
                )?;
                let array_value = self.builder.build_load(array_type, cast_ptr, "")?;
                value_store.store_value(self, op_io.outputs()[0], array_value)?;
            } else {
                // We know our array input was a pointer. Because it was a pointer, we can just shove
                // the pointer back in.
                value_store.store_value(self, op_io.outputs()[0], array_val)?;
            }
        }

        Ok(())
    }

    pub(super) fn build_insert_struct(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        field_name: Spanned<Spur>,
        emit_struct: bool,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let [data_value_id, input_struct_value_id] = *op_io.inputs().as_arr();
        let data_val = value_store.load_value(self, data_value_id, ds.values, ds.types)?;
        let input_struct_val =
            value_store.load_value(self, input_struct_value_id, ds.values, ds.types)?;

        let [data_type_id, input_struct_type_id] = ds
            .values
            .value_types([data_value_id, input_struct_value_id])
            .unwrap();
        let input_struct_type_info = ds.types.get_type_info(input_struct_type_id);
        let data_type_info = ds.types.get_type_info(data_type_id);

        let (struct_value, struct_def, struct_def_type_id) = match input_struct_type_info.kind {
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let struct_def = ds.types.get_struct_def(input_struct_type_id).clone();
                let aggr_value = if struct_def.is_union {
                    input_struct_val
                        .into_array_value()
                        .as_aggregate_value_enum()
                } else {
                    input_struct_val
                        .into_struct_value()
                        .as_aggregate_value_enum()
                };
                (aggr_value, struct_def, input_struct_type_id)
            }
            TypeKind::MultiPointer(sub_type_id) | TypeKind::SinglePointer(sub_type_id) => {
                let struct_def = ds.types.get_struct_def(sub_type_id).clone();
                let ptee_type = self.get_type(ds.types, sub_type_id);
                let aggr_value = if struct_def.is_union {
                    self.builder
                        .build_load(ptee_type, input_struct_val.into_pointer_value(), "")?
                        .into_array_value()
                        .as_aggregate_value_enum()
                } else {
                    self.builder
                        .build_load(ptee_type, input_struct_val.into_pointer_value(), "")?
                        .into_struct_value()
                        .as_aggregate_value_enum()
                };

                (aggr_value, struct_def, sub_type_id)
            }
            _ => unreachable!(),
        };

        let field_idx = struct_def
            .fields
            .iter()
            .position(|fi| fi.name.inner == field_name.inner)
            .unwrap();
        let field_info = &struct_def.fields[field_idx];
        let field_type_info = ds.types.get_type_info(field_info.kind.inner);

        let data_val = if let (TypeKind::Integer(to_int), TypeKind::Integer(from_int)) =
            (field_type_info.kind, data_type_info.kind)
        {
            self.cast_int(
                data_val.into_int_value(),
                to_int.width.get_int_type(self.ctx),
                from_int.signed,
            )?
            .as_basic_value_enum()
        } else {
            data_val
        };

        let new_value_name = if emit_struct {
            format!("{}", op_io.outputs()[0])
        } else {
            String::new()
        };

        let new_struct_val = if struct_def.is_union {
            let union_type = self.get_type(ds.types, struct_def_type_id);
            let union_alloc = value_store.new_alloca(self, ds.types, struct_def_type_id)?;
            let union_value = struct_value.into_array_value();
            self.builder.build_store(union_alloc, union_value)?;

            let cast_union_ptr = self.builder.build_pointer_cast(
                union_alloc,
                self.ctx.ptr_type(AddressSpace::default()),
                "",
            )?;

            self.builder.build_store(cast_union_ptr, data_val)?;

            let union_value = self.builder.build_load(union_type, union_alloc, "")?;
            union_value.into_array_value().as_aggregate_value_enum()
        } else {
            self.builder.build_insert_value(
                struct_value,
                data_val,
                field_idx.to_u32().unwrap(),
                &new_value_name,
            )?
        };

        if let TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) =
            input_struct_type_info.kind
        {
            // In this case we just store the struct directly.
            if emit_struct {
                value_store.store_value(
                    self,
                    op_io.outputs()[0],
                    new_struct_val.as_basic_value_enum(),
                )?;
            }
        } else {
            self.builder
                .build_store(input_struct_val.into_pointer_value(), new_struct_val)?;
            if emit_struct {
                value_store.store_value(self, op_io.outputs()[0], input_struct_val)?;
            }
        }

        Ok(())
    }

    pub(super) fn build_extract_struct(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        field_name: Spanned<Spur>,
        emit_struct: bool,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let [input_struct_value_id] = *op_io.inputs().as_arr();
        let input_struct_val =
            value_store.load_value(self, input_struct_value_id, ds.values, ds.types)?;

        let [input_struct_type_id] = ds.values.value_types([input_struct_value_id]).unwrap();
        let input_struct_type_info = ds.types.get_type_info(input_struct_type_id);

        let (struct_value, struct_def, struct_def_type_id) = match input_struct_type_info.kind {
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let struct_def = ds.types.get_struct_def(input_struct_type_id).clone();
                let aggr_value = if struct_def.is_union {
                    input_struct_val
                        .into_array_value()
                        .as_aggregate_value_enum()
                } else {
                    input_struct_val
                        .into_struct_value()
                        .as_aggregate_value_enum()
                };
                (aggr_value, struct_def, input_struct_type_id)
            }
            TypeKind::MultiPointer(sub_type_id) | TypeKind::SinglePointer(sub_type_id) => {
                let struct_def = ds.types.get_struct_def(sub_type_id).clone();
                let ptee_type = self.get_type(ds.types, sub_type_id);
                let aggr_value = if struct_def.is_union {
                    self.builder
                        .build_load(ptee_type, input_struct_val.into_pointer_value(), "")?
                        .into_array_value()
                        .as_aggregate_value_enum()
                } else {
                    self.builder
                        .build_load(ptee_type, input_struct_val.into_pointer_value(), "")?
                        .into_struct_value()
                        .as_aggregate_value_enum()
                };

                (aggr_value, struct_def, sub_type_id)
            }
            _ => unreachable!(),
        };

        let data_value_id = if emit_struct {
            value_store.store_value(self, op_io.outputs()[0], input_struct_val)?;
            op_io.outputs()[1]
        } else {
            op_io.outputs()[0]
        };

        let data_value = if struct_def.is_union {
            let union_alloc = value_store.new_alloca(self, ds.types, struct_def_type_id)?;

            self.builder.build_store(union_alloc, struct_value)?;

            let [data_value_type] = ds.values.value_types([data_value_id]).unwrap();
            let data_type = self.get_type(ds.types, data_value_type);
            let data_ptr_type = self.ctx.ptr_type(AddressSpace::default());

            let value_ptr = self
                .builder
                .build_pointer_cast(union_alloc, data_ptr_type, "")?;

            self.builder.build_load(data_type, value_ptr, "")?
        } else {
            let field_idx = struct_def
                .fields
                .iter()
                .position(|fi| fi.name.inner == field_name.inner)
                .unwrap();

            self.builder
                .build_extract_value(
                    struct_value,
                    field_idx.to_u32().unwrap(),
                    &format!("{data_value_id}"),
                )
                .unwrap()
        };

        value_store.store_value(self, data_value_id, data_value)?;

        Ok(())
    }

    pub(super) fn build_field_access(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
        field_name: Spanned<Spur>,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);
        let [input_struct_value_id] = *op_io.inputs().as_arr();
        let input_struct_ptr =
            value_store.load_value(self, input_struct_value_id, ds.values, ds.types)?;

        let [input_struct_type_id] = ds.values.value_types([input_struct_value_id]).unwrap();
        let input_struct_type_info = ds.types.get_type_info(input_struct_type_id);

        let (TypeKind::MultiPointer(ptee_struct_type_id)
        | TypeKind::SinglePointer(ptee_struct_type_id)) = input_struct_type_info.kind
        else {
            unreachable!()
        };
        let ptee_llvm_type = self.get_type(ds.types, ptee_struct_type_id);
        let struct_def = ds.types.get_struct_def(ptee_struct_type_id);

        let output_ptr = if struct_def.is_union {
            input_struct_ptr.into_pointer_value()
        } else {
            let field_index = struct_def
                .fields
                .iter()
                .position(|f| f.name.inner == field_name.inner)
                .unwrap();

            self.builder.build_struct_gep(
                ptee_llvm_type,
                input_struct_ptr.into_pointer_value(),
                field_index.to_u32().unwrap(),
                "",
            )?
        };

        value_store.store_value(self, op_io.outputs[0], output_ptr.into())?;

        Ok(())
    }

    pub(super) fn build_load(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let [inputs @ .., ptr_value_id] = op_io.inputs.as_slice() else {
            unreachable!()
        };
        let [ptr_type_id] = ds.values.value_types([*ptr_value_id]).unwrap();
        let ptr_type_info = ds.types.get_type_info(ptr_type_id);

        let ptr = value_store
            .load_value(self, *ptr_value_id, ds.values, ds.types)?
            .into_pointer_value();

        match ptr_type_info.kind {
            TypeKind::MultiPointer(ptee_id) | TypeKind::SinglePointer(ptee_id) => {
                let ptee_type = self.get_type(ds.types, ptee_id);
                let value = self.builder.build_load(ptee_type, ptr, "load")?;
                value_store.store_value(self, op_io.outputs()[0], value)?;
            }
            TypeKind::FunctionPointer => {
                let function_args = ds.types.get_function_pointer_args(ptr_type_id).clone();

                let entry_stack: Vec<BasicMetadataTypeEnum> = function_args
                    .inputs
                    .iter()
                    .map(|t| self.get_type(ds.types, *t).into())
                    .collect();

                let function_type = if function_args.outputs.is_empty() {
                    self.ctx.void_type().fn_type(&entry_stack, false)
                } else {
                    let exit_stack: Vec<_> = function_args
                        .outputs
                        .iter()
                        .map(|t| self.get_type(ds.types, *t))
                        .collect();
                    self.ctx
                        .struct_type(&exit_stack, false)
                        .fn_type(entry_stack.as_slice(), false)
                };

                let args: Vec<BasicMetadataValueEnum> = inputs
                    .iter()
                    .zip(&function_args.inputs)
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

                self.builder
                    .build_indirect_call(function_type, ptr, &args, "indirect_call")?;
            }

            _ => unreachable!(),
        }

        Ok(())
    }

    pub(super) fn build_store(
        &mut self,
        ds: &mut Stores,
        value_store: &mut SsaMap<'ctx>,
        op_id: OpId,
    ) -> InkwellResult {
        let op_io = ds.ops.get_op_io(op_id);

        let input_ids @ [data, ptr] = *op_io.inputs().as_arr();
        let input_type_ids = ds.values.value_types(input_ids).unwrap();
        let [data_type_kind, ptr_type_kind] =
            input_type_ids.map(|id| ds.types.get_type_info(id).kind);
        let (TypeKind::MultiPointer(pointee_type_id) | TypeKind::SinglePointer(pointee_type_id)) =
            ptr_type_kind
        else {
            unreachable!()
        };
        let pointee_type_kind = ds.types.get_type_info(pointee_type_id).kind;

        let data = value_store.load_value(self, data, ds.values, ds.types)?;

        let data = match [data_type_kind, pointee_type_kind] {
            [TypeKind::Integer(data_int), TypeKind::Integer(ptr_int)] => {
                let data = data.into_int_value();
                let target_type = ptr_int.width.get_int_type(self.ctx);
                self.cast_int(data, target_type, data_int.signed)?.into()
            }
            _ => data,
        };

        let ptr = value_store
            .load_value(self, ptr, ds.values, ds.types)?
            .into_pointer_value();

        self.builder.build_store(ptr, data)?;

        Ok(())
    }
}
