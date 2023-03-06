use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{
        can_promote_int_bidirectional, generate_type_mismatch_diag, promote_int_type_bidirectional,
        Analyzer,
    },
    source_file::SourceStorage,
    type_store::{BuiltinTypes, Signedness, TypeKind, TypeStore},
};

pub(super) fn add(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = analyzer.value_types(input_ids) else { return };
    let input_type_info = inputs.map(|id| type_store.get_type_info(id));

    let new_type = match input_type_info.map(|ti| (ti.id, ti.kind)) {
        [(
            _,
            TypeKind::Integer {
                width: a_width,
                signed: a_signed,
            },
        ), (
            _,
            TypeKind::Integer {
                width: b_width,
                signed: b_signed,
            },
        )] if can_promote_int_bidirectional(a_width, a_signed, b_width, b_signed) => {
            type_store
                .get_builtin(
                    promote_int_type_bidirectional(a_width, a_signed, b_width, b_signed)
                        .unwrap()
                        .into(),
                )
                .id
        }

        [(ptr_id, TypeKind::Pointer(_)), (
            _,
            TypeKind::Integer {
                signed: Signedness::Unsigned,
                ..
            },
        )]
        | [(
            _,
            TypeKind::Integer {
                signed: Signedness::Unsigned,
                ..
            },
        ), (ptr_id, TypeKind::Pointer(_))] => ptr_id,

        _ => {
            // Type mismatch
            *had_error = true;

            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(
                analyzer,
                interner,
                source_store,
                type_store,
                lexeme,
                op,
                &input_ids,
            );
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, new_type);
}

pub(super) fn subtract(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = analyzer.value_types(input_ids) else { return };
    let input_type_info = inputs.map(|id| type_store.get_type_info(id));

    let new_type = match input_type_info.map(|ti| ti.kind) {
        [TypeKind::Integer {
            width: a_width,
            signed: a_signed,
        }, TypeKind::Integer {
            width: b_width,
            signed: b_signed,
        }] if can_promote_int_bidirectional(a_width, a_signed, b_width, b_signed) => {
            type_store
                .get_builtin(
                    promote_int_type_bidirectional(a_width, a_signed, b_width, b_signed)
                        .unwrap()
                        .into(),
                )
                .id
        }

        [TypeKind::Pointer(a), TypeKind::Pointer(b)] if a == b => {
            type_store.get_builtin(BuiltinTypes::U64).id
        }
        [TypeKind::Pointer(_), TypeKind::Integer {
            signed: Signedness::Unsigned,
            ..
        }] => inputs[0],

        _ => {
            // Type mismatch
            *had_error = true;

            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(
                analyzer,
                interner,
                source_store,
                type_store,
                lexeme,
                op,
                &input_ids,
            );
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, new_type);
}

pub(super) fn bitnot(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs[0];
    let Some([input]) = analyzer.value_types([input_id]) else { return };
    let input_type_info = type_store.get_type_info(input);

    let new_type = match input_type_info.kind {
        TypeKind::Integer { .. } | TypeKind::Bool => input,

        _ => {
            // Type mismatch
            *had_error = true;
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(
                analyzer,
                interner,
                source_store,
                type_store,
                lexeme,
                op,
                &[input_id],
            );

            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, new_type);
}

pub(super) fn bitand_bitor(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = analyzer.value_types(input_ids) else { return };
    let input_type_info = inputs.map(|id| type_store.get_type_info(id));

    let new_type = match input_type_info.map(|ti| ti.kind) {
        [TypeKind::Integer {
            width: a_width,
            signed: a_signed,
        }, TypeKind::Integer {
            width: b_width,
            signed: b_signed,
        }] if can_promote_int_bidirectional(a_width, a_signed, b_width, b_signed) => {
            type_store
                .get_builtin(
                    promote_int_type_bidirectional(a_width, a_signed, b_width, b_signed)
                        .unwrap()
                        .into(),
                )
                .id
        }

        [TypeKind::Bool, TypeKind::Bool] => type_store.get_builtin(BuiltinTypes::Bool).id,

        _ => {
            // Type mismatch
            *had_error = true;
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(
                analyzer,
                interner,
                source_store,
                type_store,
                lexeme,
                op,
                &input_ids,
            );
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, new_type);
}

pub(super) fn multiply_div_rem_shift(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = analyzer.value_types(input_ids) else { return };
    let input_type_info = inputs.map(|id| type_store.get_type_info(id));

    let new_type = match input_type_info.map(|ti| ti.kind) {
        [TypeKind::Integer {
            width: a_width,
            signed: a_signed,
        }, TypeKind::Integer {
            width: b_width,
            signed: b_signed,
        }] if can_promote_int_bidirectional(a_width, a_signed, b_width, b_signed) => {
            type_store
                .get_builtin(
                    promote_int_type_bidirectional(a_width, a_signed, b_width, b_signed)
                        .unwrap()
                        .into(),
                )
                .id
        }

        _ => {
            // Type mismatch
            *had_error = true;
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(
                analyzer,
                interner,
                source_store,
                type_store,
                lexeme,
                op,
                &input_ids,
            );
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, new_type);
}
