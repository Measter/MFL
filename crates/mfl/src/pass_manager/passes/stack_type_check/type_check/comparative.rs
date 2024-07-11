use crate::{
    error_signal::ErrorSignal,
    ir::{Op, TypeResolvedOp},
    n_ops::SliceNOps,
    pass_manager::static_analysis::{
        can_promote_int_bidirectional, generate_type_mismatch_diag, Analyzer,
    },
    type_store::{BuiltinTypes, TypeKind},
    Stores,
};

// Unlike the arithmatic functions, the output of these is always a boolean, so we'll just set the output
// to that type under the assumption that the comparison succeeds.

pub(crate) fn equal(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, stores.types.get_builtin(BuiltinTypes::Bool).id);

    // let op_data = analyzer.get_op_io(op.id);
    let Some(inputs) = analyzer.value_types(input_ids) else {
        return;
    };
    let input_type_info = inputs.map(|id| stores.types.get_type_info(id));
    match input_type_info.map(|ti| ti.kind) {
        [TypeKind::Integer(a), TypeKind::Integer(b)] if can_promote_int_bidirectional(a, b) => {}
        [TypeKind::Bool, TypeKind::Bool] => {}
        [TypeKind::Pointer(a), TypeKind::Pointer(b)] if a == b => {}
        _ => {
            // Type mismatch.
            had_error.set();
            let lexeme = stores.strings.resolve(op.token.inner);
            generate_type_mismatch_diag(stores, analyzer, lexeme, op, &input_ids);
        }
    }
}

pub(crate) fn compare(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, stores.types.get_builtin(BuiltinTypes::Bool).id);

    // let op_data = analyzer.get_op_io(op.id);
    let Some(inputs) = analyzer.value_types(input_ids) else {
        return;
    };
    let input_type_info = inputs.map(|id| stores.types.get_type_info(id));
    match input_type_info.map(|ti| ti.kind) {
        [TypeKind::Integer(a), TypeKind::Integer(b)] if can_promote_int_bidirectional(a, b) => {}
        [TypeKind::Pointer(a), TypeKind::Pointer(b)] if a == b => {}
        _ => {
            // Type mismatch.
            had_error.set();
            let lexeme = stores.strings.resolve(op.token.inner);
            generate_type_mismatch_diag(stores, analyzer, lexeme, op, &input_ids);
        }
    }
}

pub(crate) fn is_null(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs[0];
    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, stores.types.get_builtin(BuiltinTypes::Bool).id);

    // let op_data = analyzer.get_op_io(op.id);
    let Some([input]) = analyzer.value_types([input_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input);
    if !matches!(input_type_info.kind, TypeKind::Pointer(_)) {
        // Type mismatch.
        had_error.set();
        let lexeme = stores.strings.resolve(op.token.inner);
        generate_type_mismatch_diag(stores, analyzer, lexeme, op, &[input_id]);
    }
}
