use ariadne::Cache;
use inkwell::{
    types::BasicType,
    values::{AggregateValue, BasicValue, FunctionValue, IntValue, PointerValue, StructValue},
    AddressSpace, IntPredicate,
};
use intcast::IntCast;
use lasso::Spur;

use crate::{
    interners::Interner,
    n_ops::SliceNOps,
    opcode::Op,
    program::{
        static_analysis::{Analyzer, ValueId},
        ItemId,
    },
    source_file::{SourceLocation, SourceStorage, Spanned},
    type_store::{BuiltinTypes, Signedness, TypeId, TypeInfo, TypeKind, TypeStore},
};

use super::{CodeGen, ValueStore};

enum ArrayPtrKind {
    Array,  // ptr(T[N])
    Direct, // ptr(T)
}

impl<'ctx> CodeGen<'ctx> {
    pub(super) fn build_memory_local(
        &mut self,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        op: &Op,
        item_id: ItemId,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let ptr = value_store.variable_map[&item_id];
        value_store.store_value(self, op_io.outputs()[0], ptr.into());
    }

    pub(super) fn build_pack(
        &mut self,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let output_id = op_io.outputs()[0];
        let [output_type_id] = analyzer.value_types([output_id]).unwrap();
        let output_type_info = type_store.get_type_info(output_type_id);

        let aggr_llvm_type = self.get_type(type_store, output_type_id);
        let aggr_value = aggr_llvm_type.const_zero();
        let mut aggr_value = match output_type_info.kind {
            TypeKind::Array { .. } => aggr_value.into_array_value().as_aggregate_value_enum(),
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                aggr_value.into_struct_value().as_aggregate_value_enum()
            }
            _ => unreachable!(),
        };

        for (value_id, idx) in op_io.inputs().iter().zip(0..) {
            let [input_type_id] = analyzer.value_types([*value_id]).unwrap();
            let input_type_info = type_store.get_type_info(input_type_id);

            let field_store_type_info = match output_type_info.kind {
                TypeKind::Array { type_id, .. } => type_store.get_type_info(type_id),
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                    let struct_info = type_store.get_struct_def(output_type_id);
                    let field_kind = struct_info.fields[idx].kind;
                    type_store.get_type_info(field_kind)
                }
                _ => unreachable!(),
            };

            let value = value_store.load_value(self, *value_id, analyzer, type_store, interner);
            let value = if let (
                TypeKind::Integer {
                    width: to_width, ..
                },
                TypeKind::Integer {
                    signed: from_signed,
                    ..
                },
            ) = (field_store_type_info.kind, input_type_info.kind)
            {
                self.cast_int(
                    value.into_int_value(),
                    to_width.get_int_type(self.ctx),
                    from_signed,
                )
                .as_basic_value_enum()
            } else {
                value
            };

            aggr_value = self
                .builder
                .build_insert_value(aggr_value, value, idx.to_u32().unwrap(), "insert")
                .unwrap();
        }

        value_store.store_value(self, output_id, aggr_value.as_basic_value_enum());
    }

    pub(super) fn build_unpack(
        &mut self,
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

        let aggr = value_store.load_value(self, input_value_id, analyzer, type_store, interner);

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

            value_store.store_value(self, *output_value_id, output_value);
        }
    }

    fn build_bounds_check(
        &mut self,
        mut source_store: &SourceStorage,
        type_store: &TypeStore,
        op_loc: SourceLocation,
        function: FunctionValue,
        idx: IntValue,
        length: IntValue,
    ) {
        let current_block = self.builder.get_insert_block().unwrap();
        let success_block = self
            .ctx
            .append_basic_block(function, "bounds_check_success");
        let fail_block = self.ctx.append_basic_block(function, "bounds_check_fail");

        self.builder.position_at_end(current_block);
        let cmp_res =
            self.builder
                .build_int_compare(IntPredicate::ULT, idx, length, "bounds_check_cmp");

        self.builder
            .build_conditional_branch(cmp_res, success_block, fail_block);

        self.builder.position_at_end(fail_block);
        // Crash and burn
        let file_name = source_store.name(op_loc.file_id);
        let (_, line, column) = source_store
            .fetch(&op_loc.file_id)
            .unwrap()
            .get_offset_line(op_loc.source_start.to_usize())
            .unwrap();
        let location_string = format!("{file_name}:{}:{}", line + 1, column + 1);
        let string = self
            .builder
            .build_global_string_ptr(&location_string, "oob_loc");
        let string_pointer = string
            .as_pointer_value()
            .const_cast(self.ctx.i8_type().ptr_type(AddressSpace::default()));

        let str_type = self
            .get_type(type_store, type_store.get_builtin(BuiltinTypes::String).id)
            .into_struct_type();
        let str_value = str_type.const_named_struct(&[
            self.ctx
                .i64_type()
                .const_int(location_string.len().to_u64(), false)
                .into(),
            string_pointer.into(),
        ]);

        let args = [str_value.into(), idx.into(), length.into()];

        self.builder.build_call(self.oob_handler, &args, "oob");
        self.builder.build_unreachable();

        self.builder.position_at_end(success_block);
    }

    fn get_slice_like_struct_fields(
        &mut self,
        interner: &mut Interner,
        type_store: &TypeStore,
        struct_value_id: ValueId,
        struct_type_id: TypeId,
        struct_value: StructValue<'ctx>,
    ) -> (PointerValue<'ctx>, TypeInfo, IntValue<'ctx>) {
        let struct_def = type_store.get_struct_def(struct_type_id);

        let pointer_field_name = interner.intern("pointer");
        let (ptr_field_idx, ptr_field_info) = struct_def
            .fields
            .iter()
            .enumerate()
            .find(|(_, fi)| fi.name.inner == pointer_field_name)
            .unwrap();

        let TypeKind::Pointer(store_type) = type_store.get_type_info(ptr_field_info.kind).kind else { unreachable!() };

        let ptr_name = format!("{struct_value_id}_pointer");
        let ptr_value = self
            .builder
            .build_extract_value(struct_value, ptr_field_idx.to_u32().unwrap(), &ptr_name)
            .unwrap()
            .into_pointer_value();

        let length_field_name = interner.intern("length");
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
            )
            .unwrap()
            .into_int_value();

        (
            ptr_value,
            type_store.get_type_info(store_type),
            length_value,
        )
    }

    pub(super) fn build_extract_array(
        &mut self,
        source_store: &SourceStorage,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        function: FunctionValue<'ctx>,
        op: &Op,
        emit_array: bool,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let inputs @ [array_value_id, _] = *op_io.inputs().as_arr();
        let [array_val, idx_val] =
            inputs.map(|id| value_store.load_value(self, id, analyzer, type_store, interner));

        let [array_type_id] = analyzer.value_types([array_value_id]).unwrap();
        let array_type_info = type_store.get_type_info(array_type_id);

        let (arr_ptr, length, ptr_kind) = match array_type_info.kind {
            TypeKind::Array { length, .. } => {
                // Ugh, this sucks!
                let store_location = value_store.get_temp_alloca(self, type_store, array_type_id);
                self.builder.build_store(store_location, array_val);

                let length_value = self.ctx.i64_type().const_int(length.to_u64(), false);

                (store_location, length_value, ArrayPtrKind::Array)
            }
            TypeKind::Pointer(sub_type_id) => {
                let sub_type_info = type_store.get_type_info(sub_type_id);
                match sub_type_info.kind {
                    TypeKind::Array { length, .. } => {
                        let length_value = self.ctx.i64_type().const_int(length.to_u64(), false);

                        (
                            array_val.into_pointer_value(),
                            length_value,
                            ArrayPtrKind::Array,
                        )
                    }
                    TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                        let struct_val =
                            self.builder.build_load(array_val.into_pointer_value(), "");
                        let (arr_ptr, _, length) = self.get_slice_like_struct_fields(
                            interner,
                            type_store,
                            array_value_id,
                            sub_type_id,
                            struct_val.into_struct_value(),
                        );
                        (arr_ptr, length, ArrayPtrKind::Direct)
                    }
                    _ => unreachable!(),
                }
            }
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let (arr_ptr, _, length) = self.get_slice_like_struct_fields(
                    interner,
                    type_store,
                    array_value_id,
                    array_type_id,
                    array_val.into_struct_value(),
                );

                (arr_ptr, length, ArrayPtrKind::Direct)
            }
            _ => unreachable!(),
        };

        let idx_val = self.cast_int(
            idx_val.into_int_value(),
            self.ctx.i64_type(),
            Signedness::Unsigned,
        );

        self.build_bounds_check(
            source_store,
            type_store,
            op.token.location,
            function,
            idx_val,
            length,
        );

        let idxs = [self.ctx.i64_type().const_zero(), idx_val];
        let offset_idxs: &[IntValue] = match ptr_kind {
            ArrayPtrKind::Array => &idxs,
            ArrayPtrKind::Direct => &idxs[1..],
        };

        let offset_ptr = unsafe { self.builder.build_in_bounds_gep(arr_ptr, offset_idxs, "") };

        let output_value_id = if emit_array {
            let output_array_id = op_io.outputs()[0];
            value_store.store_value(self, output_array_id, array_val);
            op_io.outputs()[1]
        } else {
            op_io.outputs()[0]
        };

        let output_value_name = format!("{output_value_id}");
        let loaded_value = self.builder.build_load(offset_ptr, &output_value_name);
        value_store.store_value(self, output_value_id, loaded_value);

        if let TypeKind::Array { .. } = array_type_info.kind {
            value_store.release_temp_alloca(array_type_id, arr_ptr);
        }
    }

    pub(super) fn build_insert_array(
        &mut self,
        source_store: &SourceStorage,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        function: FunctionValue<'ctx>,
        op: &Op,
        emit_array: bool,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let inputs @ [data_value_id, array_value_id, _] = *op_io.inputs().as_arr();
        let [data_val, array_val, idx_val] =
            inputs.map(|id| value_store.load_value(self, id, analyzer, type_store, interner));

        let [data_type_id, array_type_id] = analyzer
            .value_types([data_value_id, array_value_id])
            .unwrap();
        let array_type_info = type_store.get_type_info(array_type_id);
        let data_type_info = type_store.get_type_info(data_type_id);

        let (arr_ptr, store_type_info, length, ptr_kind) = match array_type_info.kind {
            TypeKind::Array { type_id, length } => {
                // Ugh, this sucks!
                let store_location = value_store.get_temp_alloca(self, type_store, array_type_id);
                self.builder.build_store(store_location, array_val);
                let store_type_info = type_store.get_type_info(type_id);

                let length_value = self.ctx.i64_type().const_int(length.to_u64(), false);

                (
                    store_location,
                    store_type_info,
                    length_value,
                    ArrayPtrKind::Array,
                )
            }
            TypeKind::Pointer(sub_type_id) => {
                let sub_type_info = type_store.get_type_info(sub_type_id);
                match sub_type_info.kind {
                    TypeKind::Array {
                        type_id: store_type_id,
                        length,
                    } => {
                        let store_type_info = type_store.get_type_info(store_type_id);

                        let length_value = self.ctx.i64_type().const_int(length.to_u64(), false);

                        (
                            array_val.into_pointer_value(),
                            store_type_info,
                            length_value,
                            ArrayPtrKind::Array,
                        )
                    }
                    TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                        let struct_val =
                            self.builder.build_load(array_val.into_pointer_value(), "");
                        let (ptr_field, store_type_info, length) = self
                            .get_slice_like_struct_fields(
                                interner,
                                type_store,
                                array_value_id,
                                sub_type_id,
                                struct_val.into_struct_value(),
                            );
                        (ptr_field, store_type_info, length, ArrayPtrKind::Direct)
                    }
                    _ => unreachable!(),
                }
            }
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let (ptr_field, store_type_info, length) = self.get_slice_like_struct_fields(
                    interner,
                    type_store,
                    array_value_id,
                    array_type_id,
                    array_val.into_struct_value(),
                );
                (ptr_field, store_type_info, length, ArrayPtrKind::Direct)
            }
            _ => unreachable!(),
        };

        let idx_val = self.cast_int(
            idx_val.into_int_value(),
            self.ctx.i64_type(),
            Signedness::Unsigned,
        );

        self.build_bounds_check(
            source_store,
            type_store,
            op.token.location,
            function,
            idx_val,
            length,
        );

        // And finally actually build the insert
        let idxs = [self.ctx.i64_type().const_zero(), idx_val];
        let offset_idxs: &[IntValue] = match ptr_kind {
            ArrayPtrKind::Array => &idxs,
            ArrayPtrKind::Direct => &idxs[1..],
        };

        let offset_ptr = unsafe { self.builder.build_in_bounds_gep(arr_ptr, offset_idxs, "") };

        let data_val = if let (
            TypeKind::Integer {
                width: to_width, ..
            },
            TypeKind::Integer {
                signed: from_signed,
                ..
            },
        ) = (store_type_info.kind, data_type_info.kind)
        {
            self.cast_int(
                data_val.into_int_value(),
                to_width.get_int_type(self.ctx),
                from_signed,
            )
            .as_basic_value_enum()
        } else {
            data_val
        };

        self.builder.build_store(offset_ptr, data_val);

        if emit_array {
            if let TypeKind::Array { .. } = array_type_info.kind {
                let array_type = self.get_type(type_store, array_type_id);
                let cast_ptr = self.builder.build_pointer_cast(
                    arr_ptr,
                    array_type.ptr_type(AddressSpace::default()),
                    "",
                );
                let array_value = self.builder.build_load(cast_ptr, "");
                value_store.release_temp_alloca(array_type_id, arr_ptr);
                value_store.store_value(self, op_io.outputs()[0], array_value);
            } else {
                // We know our array input was a pointer. Because it was a pointer, we can just shove
                // the pointer back in.
                value_store.store_value(self, op_io.outputs()[0], array_val);
            }
        }
    }

    pub(super) fn build_insert_struct(
        &mut self,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
        field_name: Spanned<Spur>,
        emit_struct: bool,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let inputs @ [data_value_id, input_struct_value_id] = *op_io.inputs().as_arr();
        let [data_val, input_struct_val] =
            inputs.map(|id| value_store.load_value(self, id, analyzer, type_store, interner));

        let [data_type_id, input_struct_type_id] = analyzer
            .value_types([data_value_id, input_struct_value_id])
            .unwrap();
        let input_struct_type_info = type_store.get_type_info(input_struct_type_id);
        let data_type_info = type_store.get_type_info(data_type_id);

        let (struct_value, struct_def) = match input_struct_type_info.kind {
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let struct_def = type_store.get_struct_def(input_struct_type_id);
                (input_struct_val.into_struct_value(), struct_def)
            }
            TypeKind::Pointer(sub_type_id) => {
                let struct_def = type_store.get_struct_def(sub_type_id);
                let struct_value = self
                    .builder
                    .build_load(input_struct_val.into_pointer_value(), "")
                    .into_struct_value();

                (struct_value, struct_def)
            }
            _ => unreachable!(),
        };

        let field_idx = struct_def
            .fields
            .iter()
            .position(|fi| fi.name.inner == field_name.inner)
            .unwrap();
        let field_info = &struct_def.fields[field_idx];
        let field_type_info = type_store.get_type_info(field_info.kind);

        let data_val = if let (
            TypeKind::Integer {
                width: to_width, ..
            },
            TypeKind::Integer {
                signed: from_signed,
                ..
            },
        ) = (field_type_info.kind, data_type_info.kind)
        {
            self.cast_int(
                data_val.into_int_value(),
                to_width.get_int_type(self.ctx),
                from_signed,
            )
            .as_basic_value_enum()
        } else {
            data_val
        };

        let new_value_name = if emit_struct {
            format!("{}", op_io.outputs()[0])
        } else {
            struct_value.get_name().to_str().unwrap().to_owned()
        };
        let new_struct_val = self
            .builder
            .build_insert_value(
                struct_value,
                data_val,
                field_idx.to_u32().unwrap(),
                &new_value_name,
            )
            .unwrap();

        if let TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) =
            input_struct_type_info.kind
        {
            // In this case we just store the struct directly.
            if emit_struct {
                value_store.store_value(
                    self,
                    op_io.outputs()[0],
                    new_struct_val.as_basic_value_enum(),
                );
            }
        } else {
            self.builder
                .build_store(input_struct_val.into_pointer_value(), new_struct_val);
            if emit_struct {
                value_store.store_value(self, op_io.outputs()[0], input_struct_val);
            }
        }
    }

    pub(super) fn build_extract_struct(
        &mut self,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
        field_name: Spanned<Spur>,
        emit_struct: bool,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let [input_struct_value_id] = *op_io.inputs().as_arr();
        let input_struct_val =
            value_store.load_value(self, input_struct_value_id, analyzer, type_store, interner);

        let [input_struct_type_id] = analyzer.value_types([input_struct_value_id]).unwrap();
        let input_struct_type_info = type_store.get_type_info(input_struct_type_id);

        let (struct_value, struct_def) = match input_struct_type_info.kind {
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let struct_def = type_store.get_struct_def(input_struct_type_id);
                (input_struct_val.into_struct_value(), struct_def)
            }
            TypeKind::Pointer(sub_type_id) => {
                let struct_def = type_store.get_struct_def(sub_type_id);
                let struct_value = self
                    .builder
                    .build_load(input_struct_val.into_pointer_value(), "")
                    .into_struct_value();

                (struct_value, struct_def)
            }
            _ => unreachable!(),
        };

        let field_idx = struct_def
            .fields
            .iter()
            .position(|fi| fi.name.inner == field_name.inner)
            .unwrap();

        let data_value_id = if emit_struct {
            value_store.store_value(self, op_io.outputs()[0], input_struct_val);
            op_io.outputs()[1]
        } else {
            op_io.outputs()[0]
        };

        let data_value = self
            .builder
            .build_extract_value(
                struct_value,
                field_idx.to_u32().unwrap(),
                &format!("{data_value_id}"),
            )
            .unwrap();

        value_store.store_value(self, data_value_id, data_value);
    }

    pub(super) fn build_load(
        &mut self,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let ptr_value_id = op_io.inputs()[0];
        let ptr = value_store
            .load_value(self, ptr_value_id, analyzer, type_store, interner)
            .into_pointer_value();

        let value = self.builder.build_load(ptr, "load");
        value_store.store_value(self, op_io.outputs()[0], value);
    }

    pub(super) fn build_store(
        &mut self,
        interner: &mut Interner,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let input_ids @ [data, ptr] = *op_io.inputs().as_arr();
        let input_type_ids = analyzer.value_types(input_ids).unwrap();
        let [data_type_kind, ptr_type_kind] =
            input_type_ids.map(|id| type_store.get_type_info(id).kind);
        let TypeKind::Pointer(pointee_type_id) = ptr_type_kind else { unreachable!() };
        let pointee_type_kind = type_store.get_type_info(pointee_type_id).kind;

        let data = value_store.load_value(self, data, analyzer, type_store, interner);

        let data = match [data_type_kind, pointee_type_kind] {
            [TypeKind::Integer {
                signed: data_signed,
                ..
            }, TypeKind::Integer {
                width: ptr_width, ..
            }] => {
                let data = data.into_int_value();
                let target_type = ptr_width.get_int_type(self.ctx);
                self.cast_int(data, target_type, data_signed).into()
            }
            _ => data,
        };

        let ptr = value_store
            .load_value(self, ptr, analyzer, type_store, interner)
            .into_pointer_value();

        self.builder.build_store(ptr, data);
    }
}
