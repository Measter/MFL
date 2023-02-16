use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::{
        static_analysis::{generate_type_mismatch_diag, Analyzer},
        type_store::{BuiltinTypes, Signedness, TypeKind, TypeStore},
    },
    source_file::SourceStorage,
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

    let new_type = match input_type_info.map(|ti| ti.kind) {
        // One of these was the result of an earlier error. Nothing else to do, just leave.
        [TypeKind::Integer(a), TypeKind::Integer(b)] => {
            let kind = (Signedness::Unsigned, a.max(b)).into();
            type_store.get_builtin(kind).id
        }
        [TypeKind::Pointer, TypeKind::Integer(_)] | [TypeKind::Integer(_), TypeKind::Pointer] => {
            type_store.get_builtin(BuiltinTypes::Pointer).id
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
        [TypeKind::Integer(a), TypeKind::Integer(b)] => {
            let kind = (Signedness::Unsigned, a.max(b)).into();
            type_store.get_builtin(kind).id
        }
        [TypeKind::Pointer, TypeKind::Pointer] => type_store.get_builtin(BuiltinTypes::U64).id,
        [TypeKind::Pointer, TypeKind::Integer(_)] => {
            type_store.get_builtin(BuiltinTypes::Pointer).id
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
        TypeKind::Integer(_) | TypeKind::Bool => input,

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
        [TypeKind::Integer(a), TypeKind::Integer(b)] => {
            let kind = (Signedness::Unsigned, a.max(b)).into();
            type_store.get_builtin(kind).id
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

pub(super) fn multiply_and_shift(
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
        [TypeKind::Integer(a), TypeKind::Integer(b)] => {
            let kind = (Signedness::Unsigned, a.max(b)).into();
            type_store.get_builtin(kind).id
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

pub(super) fn divmod(
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
        [TypeKind::Integer(a), TypeKind::Integer(b)] => {
            let kind = (Signedness::Unsigned, a.max(b)).into();
            type_store.get_builtin(kind).id
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

    let [quot_id, rem_id] = *op_data.outputs.as_arr::<2>();
    analyzer.set_value_type(quot_id, new_type);
    analyzer.set_value_type(rem_id, new_type);
}
