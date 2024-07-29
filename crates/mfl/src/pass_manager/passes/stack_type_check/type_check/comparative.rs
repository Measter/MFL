use crate::{
    error_signal::ErrorSignal,
    n_ops::SliceNOps,
    pass_manager::static_analysis::{can_promote_int_bidirectional, generate_type_mismatch_diag},
    stores::{
        ops::OpId,
        types::{BuiltinTypes, TypeKind},
    },
    Stores,
};

// Unlike the arithmatic functions, the output of these is always a boolean, so we'll just set the output
// to that type under the assumption that the comparison succeeds.

pub(crate) fn equal(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let output_id = op_data.outputs[0];
    stores
        .values
        .set_value_type(output_id, stores.types.get_builtin(BuiltinTypes::Bool).id);

    let Some(inputs) = stores.values.value_types(input_ids) else {
        return;
    };
    let input_type_info = inputs.map(|id| stores.types.get_type_info(id));
    match input_type_info.map(|ti| ti.kind) {
        [TypeKind::Integer(a), TypeKind::Integer(b)] if can_promote_int_bidirectional(a, b) => {}
        [TypeKind::Bool, TypeKind::Bool] => {}
        [TypeKind::MultiPointer(a) | TypeKind::SinglePointer(a), TypeKind::MultiPointer(b) | TypeKind::SinglePointer(b)]
            if a == b => {}
        _ => {
            // Type mismatch.
            had_error.set();
            let op_token = stores.ops.get_token(op_id);
            let lexeme = stores.strings.resolve(op_token.inner);
            generate_type_mismatch_diag(stores, lexeme, op_id, &input_ids);
        }
    }
}

pub(crate) fn compare(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let output_id = op_data.outputs[0];
    stores
        .values
        .set_value_type(output_id, stores.types.get_builtin(BuiltinTypes::Bool).id);

    let Some(inputs) = stores.values.value_types(input_ids) else {
        return;
    };
    let input_type_info = inputs.map(|id| stores.types.get_type_info(id));
    match input_type_info.map(|ti| ti.kind) {
        [TypeKind::Integer(a), TypeKind::Integer(b)] if can_promote_int_bidirectional(a, b) => {}
        [TypeKind::MultiPointer(a) | TypeKind::SinglePointer(a), TypeKind::MultiPointer(b) | TypeKind::SinglePointer(b)]
            if a == b => {}
        _ => {
            // Type mismatch.
            had_error.set();
            let op_token = stores.ops.get_token(op_id);
            let lexeme = stores.strings.resolve(op_token.inner);
            generate_type_mismatch_diag(stores, lexeme, op_id, &input_ids);
        }
    }
}

pub(crate) fn is_null(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_id = op_data.inputs[0];
    let output_id = op_data.outputs[0];
    stores
        .values
        .set_value_type(output_id, stores.types.get_builtin(BuiltinTypes::Bool).id);

    let Some([input]) = stores.values.value_types([input_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input);
    if !matches!(
        input_type_info.kind,
        TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_)
    ) {
        // Type mismatch.
        had_error.set();
        let op_token = stores.ops.get_token(op_id);
        let lexeme = stores.strings.resolve(op_token.inner);
        generate_type_mismatch_diag(stores, lexeme, op_id, &[input_id]);
    }
}
