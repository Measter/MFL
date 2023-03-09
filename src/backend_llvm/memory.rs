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
