use inkwell::AddressSpace;

use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::{
        static_analysis::Analyzer,
        type_store::{TypeId, TypeKind, TypeStore},
        ItemId, Program,
    },
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
        program: &Program,
        interner: &mut Interners,
        analyzer: &Analyzer,
        value_store: &mut ValueStore<'ctx>,
        type_store: &TypeStore,
        op: &Op,
        type_id: TypeId,
    ) {
        let op_io = analyzer.get_op_io(op.id);

        let ptr_value_id = op_io.inputs()[0];
        let ptr = value_store
            .load_value(
                self,
                ptr_value_id,
                analyzer,
                program.get_type_store(),
                interner,
            )
            .into_pointer_value();

        let type_info = type_store.get_type_info(type_id);

        let cast_ptr = match type_info.kind {
            TypeKind::Integer { width, .. } => {
                let ptr_type = width
                    .get_int_type(self.ctx)
                    .ptr_type(AddressSpace::default());
                self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
            }
            TypeKind::Pointer => {
                let ptr_type = self
                    .ctx
                    .i8_type()
                    .ptr_type(AddressSpace::default())
                    .ptr_type(AddressSpace::default());

                self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
            }
            TypeKind::Bool => {
                let ptr_type = self.ctx.bool_type().ptr_type(AddressSpace::default());
                self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
            }
        };

        let value = self.builder.build_load(cast_ptr, "load");
        value_store.store_value(self, op_io.outputs()[0], value);
    }

    pub(super) fn build_store(
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

        let [data, ptr] = *op_io.inputs().as_arr();
        let data = value_store.load_value(self, data, analyzer, program.get_type_store(), interner);
        let ptr = value_store
            .load_value(self, ptr, analyzer, program.get_type_store(), interner)
            .into_pointer_value();

        let type_info = type_store.get_type_info(type_id);
        let cast_ptr = match type_info.kind {
            TypeKind::Integer { width, .. } => {
                let ptr_type = width
                    .get_int_type(self.ctx)
                    .ptr_type(AddressSpace::default());
                self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
            }
            TypeKind::Pointer => {
                let ptr_type = self
                    .ctx
                    .i8_type()
                    .ptr_type(AddressSpace::default())
                    .ptr_type(AddressSpace::default());

                self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
            }
            TypeKind::Bool => {
                let ptr_type = self.ctx.bool_type().ptr_type(AddressSpace::default());
                self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
            }
        };

        self.builder.build_store(cast_ptr, data);
    }
}
