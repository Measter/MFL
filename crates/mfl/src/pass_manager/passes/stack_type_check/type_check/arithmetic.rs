use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    ir::{Arithmetic, Basic, OpCode},
    n_ops::SliceNOps,
    pass_manager::static_analysis::{
        can_promote_int_bidirectional, generate_type_mismatch_diag, promote_int_type_bidirectional,
    },
    stores::{
        ops::OpId,
        types::{BuiltinTypes, TypeKind},
    },
    Stores,
};

pub(crate) fn add(stores: &mut Stores, had_error: &mut ErrorSignal, item_id: ItemId, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = stores.values.value_types(input_ids) else {
        return;
    };
    let input_type_info = inputs.map(|id| stores.types.get_type_info(id));

    let new_type = match input_type_info.map(|ti| (ti.id, ti.kind)) {
        [(_, TypeKind::Integer(a)), (_, TypeKind::Integer(b))]
            if can_promote_int_bidirectional(a, b) =>
        {
            stores
                .types
                .get_builtin(promote_int_type_bidirectional(a, b).unwrap().into())
                .id
        }

        [(ptr_id, TypeKind::MultiPointer(_)), (_, TypeKind::Integer(int))]
        | [(_, TypeKind::Integer(int)), (ptr_id, TypeKind::MultiPointer(_))]
            if int.is_unsigned() =>
        {
            ptr_id
        }

        [(_, TypeKind::Float(a)), (_, TypeKind::Float(b))] => {
            let output_width = a.max(b);
            stores.types.get_builtin(output_width.into()).id
        }

        // Type mismatch
        _ => {
            had_error.set();
            let op_token = stores.ops.get_token(op_id);
            generate_type_mismatch_diag(stores, item_id, op_token.inner, op_id, &input_ids);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    stores.values.set_value_type(output_id, new_type);
}

pub(crate) fn multiply_div_rem_shift(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = stores.values.value_types(input_ids) else {
        return;
    };
    let input_type_info = inputs.map(|id| stores.types.get_type_info(id));

    let op_kind = stores.ops.get_type_resolved(op_id);
    let is_shift = matches!(
        op_kind,
        OpCode::Basic(Basic::Arithmetic(
            Arithmetic::ShiftLeft | Arithmetic::ShiftRight
        ))
    );

    let new_type = match input_type_info.map(|ti| ti.kind) {
        [TypeKind::Integer(a), TypeKind::Integer(b)] if can_promote_int_bidirectional(a, b) => {
            stores
                .types
                .get_builtin(promote_int_type_bidirectional(a, b).unwrap().into())
                .id
        }
        [TypeKind::Float(a), TypeKind::Float(b)] if !is_shift => {
            let output_width = a.max(b);
            stores.types.get_builtin(output_width.into()).id
        }
        _ => {
            // Type mismatch
            had_error.set();
            let op_token = stores.ops.get_token(op_id);
            generate_type_mismatch_diag(stores, item_id, op_token.inner, op_id, &input_ids);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    stores.values.set_value_type(output_id, new_type);
}

pub(crate) fn subtract(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = stores.values.value_types(input_ids) else {
        return;
    };
    let input_type_info = inputs.map(|id| stores.types.get_type_info(id));

    let new_type = match input_type_info.map(|ti| ti.kind) {
        [TypeKind::Integer(a), TypeKind::Integer(b)] if can_promote_int_bidirectional(a, b) => {
            stores
                .types
                .get_builtin(promote_int_type_bidirectional(a, b).unwrap().into())
                .id
        }
        [TypeKind::Float(a), TypeKind::Float(b)] => {
            let output_width = a.max(b);
            stores.types.get_builtin(output_width.into()).id
        }
        [TypeKind::MultiPointer(a), TypeKind::MultiPointer(b)] if a == b => {
            stores.types.get_builtin(BuiltinTypes::U64).id
        }
        [TypeKind::MultiPointer(_), TypeKind::Integer(int)] if int.is_unsigned() => inputs[0],

        _ => {
            // Type mismatch
            had_error.set();
            let op_token = stores.ops.get_token(op_id);
            generate_type_mismatch_diag(stores, item_id, op_token.inner, op_id, &input_ids);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    stores.values.set_value_type(output_id, new_type);
}

pub(crate) fn bitnot(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_id = op_data.inputs[0];
    let Some([input]) = stores.values.value_types([input_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input);

    let new_type = match input_type_info.kind {
        TypeKind::Integer(_) | TypeKind::Bool => input,
        _ => {
            // Type mismatch
            had_error.set();
            let op_token = stores.ops.get_token(op_id);
            generate_type_mismatch_diag(stores, item_id, op_token.inner, op_id, &[input_id]);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    stores.values.set_value_type(output_id, new_type);
}

pub(crate) fn bitand_bitor_bitxor(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = stores.values.value_types(input_ids) else {
        return;
    };
    let input_type_info = inputs.map(|id| stores.types.get_type_info(id));

    let new_type = match input_type_info.map(|ti| ti.kind) {
        [TypeKind::Integer(a), TypeKind::Integer(b)] if can_promote_int_bidirectional(a, b) => {
            stores
                .types
                .get_builtin(promote_int_type_bidirectional(a, b).unwrap().into())
                .id
        }
        [TypeKind::Bool, TypeKind::Bool] => inputs[0],

        _ => {
            // Type mismatch
            had_error.set();
            let op_token = stores.ops.get_token(op_id);
            generate_type_mismatch_diag(stores, item_id, op_token.inner, op_id, &input_ids);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    stores.values.set_value_type(output_id, new_type);
}
