use crate::{
    error_signal::ErrorSignal,
    ir::{Op, TypeResolvedOp},
    n_ops::SliceNOps,
    pass_manager::static_analysis::{
        can_promote_int_bidirectional, generate_type_mismatch_diag, promote_int_type_bidirectional,
        Analyzer,
    },
    type_store::{BuiltinTypes, TypeKind},
    Stores,
};

pub(crate) fn add(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = analyzer.value_types(input_ids) else {
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

        [(ptr_id, TypeKind::Pointer(_)), (_, TypeKind::Integer(int))]
        | [(_, TypeKind::Integer(int)), (ptr_id, TypeKind::Pointer(_))]
            if int.is_unsigned() =>
        {
            ptr_id
        }

        // Type mismatch
        _ => {
            had_error.set();
            let lexeme = stores.strings.resolve(op.token.inner);
            generate_type_mismatch_diag(stores, analyzer, lexeme, op, &input_ids);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, new_type);
}

pub(crate) fn multiply_div_rem_shift(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = analyzer.value_types(input_ids) else {
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
        _ => {
            // Type mismatch
            had_error.set();
            let lexeme = stores.strings.resolve(op.token.inner);
            generate_type_mismatch_diag(stores, analyzer, lexeme, op, &input_ids);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, new_type);
}

pub(crate) fn subtract(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = analyzer.value_types(input_ids) else {
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
        [TypeKind::Pointer(a), TypeKind::Pointer(b)] if a == b => {
            stores.types.get_builtin(BuiltinTypes::U64).id
        }
        [TypeKind::Pointer(_), TypeKind::Integer(int)] if int.is_unsigned() => inputs[0],

        _ => {
            // Type mismatch
            had_error.set();

            let lexeme = stores.strings.resolve(op.token.inner);
            generate_type_mismatch_diag(stores, analyzer, lexeme, op, &input_ids);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, new_type);
}

pub(crate) fn bitnot(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs[0];
    let Some([input]) = analyzer.value_types([input_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input);

    let new_type = match input_type_info.kind {
        TypeKind::Integer(_) | TypeKind::Bool => input,
        _ => {
            // Type mismatch
            had_error.set();

            let lexeme = stores.strings.resolve(op.token.inner);
            generate_type_mismatch_diag(stores, analyzer, lexeme, op, &[input_id]);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, new_type);
}

pub(crate) fn bitand_bitor_bitxor(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = analyzer.value_types(input_ids) else {
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

            let lexeme = stores.strings.resolve(op.token.inner);
            generate_type_mismatch_diag(stores, analyzer, lexeme, op, &input_ids);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, new_type);
}
