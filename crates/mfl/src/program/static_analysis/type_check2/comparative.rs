use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interner,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{
        can_promote_int_bidirectional, generate_type_mismatch_diag, Analyzer,
    },
    source_file::SourceStorage,
    type_store::{BuiltinTypes, TypeKind, TypeStore},
};

pub fn compare(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interner,
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
            type_store.get_builtin(BuiltinTypes::Bool).id
        }

        [TypeKind::Pointer(a), TypeKind::Pointer(b)] if a == b => {
            type_store.get_builtin(BuiltinTypes::Bool).id
        }

        _ => {
            // Type mismatch
            *had_error = true;
            let lexeme = interner.resolve(op.token.inner);
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

pub fn equal(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interner,
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
            type_store.get_builtin(BuiltinTypes::Bool).id
        }

        [TypeKind::Bool, TypeKind::Bool] => type_store.get_builtin(BuiltinTypes::Bool).id,
        [TypeKind::Pointer(a), TypeKind::Pointer(b)] if a == b => {
            type_store.get_builtin(BuiltinTypes::Bool).id
        }

        _ => {
            // Type mismatch.
            *had_error = true;
            // Don't emit an diagnostic here if any are Unknown, as it's a result of
            // an earlier error.
            let lexeme = interner.resolve(op.token.inner);
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

pub fn is_null(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interner,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs()[0];
    let Some([input_type_id]) = analyzer.value_types([input_id]) else { return };
    let input_type_info = type_store.get_type_info(input_type_id);

    if !matches!(input_type_info.kind, TypeKind::Pointer(_)) {
        *had_error = true;
        let type_name = interner.resolve(input_type_info.name);
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(input_id, 0, type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            op.token.location,
            format!("expected pointer, found `{type_name}`",),
            labels,
            None,
            source_store,
        );
    }

    let output_id = op_data.outputs()[0];
    analyzer.set_value_type(output_id, type_store.get_builtin(BuiltinTypes::Bool).id);
}
