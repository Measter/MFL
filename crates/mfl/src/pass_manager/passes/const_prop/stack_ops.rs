use crate::{
    context::Context,
    ir::IntKind,
    pass_manager::{
        static_analysis::{Analyzer, ConstVal},
        PassContext,
    },
    stores::{
        ops::OpId,
        types::{Integer, TypeId, TypeKind},
    },
    Stores,
};

pub(crate) fn dup_over(stores: &mut Stores, analyzer: &mut Analyzer, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id).clone();

    for (input_value_id, output_value_id) in op_data.inputs.into_iter().zip(op_data.outputs) {
        let Some([input_const_val]) = analyzer.value_consts([input_value_id]) else {
            continue;
        };

        analyzer.set_value_const(output_value_id, input_const_val);
    }
}

pub(crate) fn push_bool(stores: &mut Stores, analyzer: &mut Analyzer, op_id: OpId, value: bool) {
    let op_data = stores.ops.get_op_io(op_id);
    analyzer.set_value_const(op_data.outputs[0], ConstVal::Bool(value));
}

pub(crate) fn push_int(stores: &mut Stores, analyzer: &mut Analyzer, op_id: OpId, value: IntKind) {
    let op_data = stores.ops.get_op_io(op_id);
    analyzer.set_value_const(op_data.outputs[0], ConstVal::Int(value));
}

pub(crate) fn cast(
    stores: &mut crate::Stores,
    analyzer: &mut Analyzer,
    op_id: OpId,
    target_type_id: TypeId,
) {
    let target_type_info = stores.types.get_type_info(target_type_id);

    match target_type_info.kind {
        TypeKind::Integer(int_kind) => cast_to_int(stores, analyzer, op_id, int_kind),
        TypeKind::Pointer(_) => cast_to_ptr(stores, analyzer, op_id, target_type_id),
        TypeKind::Array { .. }
        | TypeKind::Bool
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_) => unreachable!(),
    }
}

fn cast_to_ptr(stores: &mut Stores, analyzer: &mut Analyzer, op_id: OpId, ptr_type_id: TypeId) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_id = op_data.inputs[0];
    let Some([input_const_val]) = analyzer.value_consts([input_value_id]) else {
        return;
    };
    let Some([input_type_id]) = analyzer.value_types([input_value_id]) else {
        return;
    };

    // For now only const-prop if the pointers are the same type. Given the warning it might be a
    // bit silly, but this could be expanded later to other casts.
    if input_type_id == ptr_type_id {
        analyzer.set_value_const(op_data.outputs[0], input_const_val);
    }
}

fn cast_to_int(stores: &mut Stores, analyzer: &mut Analyzer, op_id: OpId, int_kind: Integer) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_id = op_data.inputs[0];
    let Some([input_const_val]) = analyzer.value_consts([input_value_id]) else {
        return;
    };

    let output_const_val = match input_const_val {
        ConstVal::Int(v) => ConstVal::Int(v.cast(int_kind)),
        ConstVal::Bool(b) if int_kind.is_unsigned() => ConstVal::Int(IntKind::Unsigned(b as _)),
        ConstVal::Bool(b) => ConstVal::Int(IntKind::Signed(b as _)),
        ConstVal::Ptr { .. } => unreachable!(),
    };

    analyzer.set_value_const(op_data.outputs[0], output_const_val)
}

pub(crate) fn size_of(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    op_id: OpId,
    type_id: TypeId,
) {
    let type_info = stores.types.get_type_info(type_id);

    match type_info.kind {
        TypeKind::Struct(struct_item_id) | TypeKind::GenericStructInstance(struct_item_id) => {
            if pass_ctx
                .ensure_define_structs(ctx, stores, struct_item_id)
                .is_err()
            {
                return;
            }
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Pointer(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_) => {}
    }

    let size_info = stores.types.get_size_info(type_id);
    push_int(
        stores,
        analyzer,
        op_id,
        IntKind::Unsigned(size_info.byte_width),
    );
}
