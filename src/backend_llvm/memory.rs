use inkwell::{types::BasicType, AddressSpace};

use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::{static_analysis::Analyzer, ItemId},
    type_store::{TypeKind, TypeStore},
};

use super::{CodeGen, ValueStore};

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
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let output_id = op_io.outputs()[0];
        let [output_type_id] = analyzer.value_types([output_id]).unwrap();

        let llvm_array_type = self.get_type(type_store, output_type_id).into_array_type();
        let output_name = format!("{output_id}");

        let array_ptr = self.builder.build_alloca(llvm_array_type, &output_name);
        let mut array_value = self
            .builder
            .build_load(array_ptr, &output_name)
            .into_array_value();

        for (value_id, idx) in op_io.inputs().iter().zip(0..) {
            let value = value_store.load_value(self, *value_id, analyzer, type_store, interner);
            array_value = self
                .builder
                .build_insert_value(array_value, value, idx, "insert")
                .unwrap()
                .into_array_value();
        }

        value_store.store_value(self, output_id, array_value.into());
    }

    pub(super) fn build_unpack(
        &mut self,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let input_value_id = op_io.inputs()[0];

        let array = value_store
            .load_value(self, input_value_id, analyzer, type_store, interner)
            .into_array_value();

        for (output_value_id, idx) in op_io.outputs().iter().zip(0..) {
            let output_value = self
                .builder
                .build_extract_value(array, idx, &format!("{output_value_id}"))
                .unwrap();

            value_store.store_value(self, *output_value_id, output_value);
        }
    }

    pub(super) fn build_extract_array(
        &mut self,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let inputs @ [array_value_id, _] = *op_io.inputs().as_arr();
        let [array_val, idx_val] =
            inputs.map(|id| value_store.load_value(self, id, analyzer, type_store, interner));

        let [array_type_id] = analyzer.value_types([array_value_id]).unwrap();
        let array_type_info = type_store.get_type_info(array_type_id);

        let arr_ptr = match array_type_info.kind {
            TypeKind::Array { type_id, .. } => {
                // Ugh, this sucks!
                let array_type = self.get_type(type_store, array_type_id);
                let store_type = self.get_type(type_store, type_id);
                let store_location = self.builder.build_alloca(array_type, "");
                self.builder.build_store(store_location, array_val);
                self.builder.build_pointer_cast(
                    store_location,
                    store_type.ptr_type(AddressSpace::default()),
                    "",
                )
            }
            TypeKind::Pointer(ptr_type) => {
                let ptr_type_info = type_store.get_type_info(ptr_type);
                let TypeKind::Array { type_id, .. } = ptr_type_info.kind else {unreachable!()};

                let store_type = self.get_type(type_store, type_id);
                self.builder.build_pointer_cast(
                    array_val.into_pointer_value(),
                    store_type.ptr_type(AddressSpace::default()),
                    "",
                )
            }
            _ => unreachable!(),
        };

        let offset_ptr = unsafe {
            self.builder
                .build_gep(arr_ptr, &[idx_val.into_int_value()], "")
        };

        let output_id = op_io.outputs()[0];
        let output_name = format!("{output_id}");
        let loaded_value = self.builder.build_load(offset_ptr, &output_name);
        value_store.store_value(self, output_id, loaded_value);
    }

    pub(super) fn build_insert_array(
        &mut self,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
    ) {
        let op_io = analyzer.get_op_io(op.id);
        let inputs @ [data_value_id, array_value_id, _] = *op_io.inputs().as_arr();
        let [data_val, array_val, idx_val] =
            inputs.map(|id| value_store.load_value(self, id, analyzer, type_store, interner));

        let [data_type_id, array_type_id] = analyzer
            .value_types([data_value_id, array_value_id])
            .unwrap();
        let array_type_info = type_store.get_type_info(array_type_id);

        let arr_ptr = match array_type_info.kind {
            TypeKind::Array { .. } => {
                // Ugh, this sucks!
                let array_type = self.get_type(type_store, array_type_id);
                let store_type = self.get_type(type_store, data_type_id);
                let store_location = self.builder.build_alloca(array_type, "");
                self.builder.build_store(store_location, array_val);
                self.builder.build_pointer_cast(
                    store_location,
                    store_type.ptr_type(AddressSpace::default()),
                    "",
                )
            }
            TypeKind::Pointer(_) => {
                let store_type = self.get_type(type_store, data_type_id);
                self.builder.build_pointer_cast(
                    array_val.into_pointer_value(),
                    store_type.ptr_type(AddressSpace::default()),
                    "",
                )
            }
            _ => unreachable!(),
        };

        let offset_ptr = unsafe {
            self.builder
                .build_gep(arr_ptr, &[idx_val.into_int_value()], "")
        };

        self.builder.build_store(offset_ptr, data_val);

        if let TypeKind::Array { .. } = array_type_info.kind {
            let array_type = self.get_type(type_store, array_type_id);
            let cast_ptr = self.builder.build_pointer_cast(
                arr_ptr,
                array_type.ptr_type(AddressSpace::default()),
                "",
            );
            let array_value = self.builder.build_load(cast_ptr, "");
            value_store.store_value(self, op_io.outputs()[0], array_value);
        }
    }

    pub(super) fn build_load(
        &mut self,
        interner: &mut Interners,
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
        interner: &mut Interners,
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
