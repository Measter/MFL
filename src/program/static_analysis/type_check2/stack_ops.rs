use ariadne::{Color, Label};
use lasso::Spur;

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{self, generate_type_mismatch_diag, Analyzer, PorthTypeKind},
    source_file::SourceStorage,
};

pub(super) fn cast_int(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<1>();
    let Some([input]) = analyzer.value_types(input_ids) else { return };

    let new_type = match input {
        PorthTypeKind::Bool | PorthTypeKind::Ptr => PorthTypeKind::Int,

        PorthTypeKind::Int => {
            let [value] = analyzer.values(input_ids);

            diagnostics::emit_warning(
                op.token.location,
                "unnecessary cast",
                [
                    Label::new(op.token.location).with_color(Color::Yellow),
                    Label::new(value.creator_token.location)
                        .with_message("already an Int")
                        .with_color(Color::Cyan),
                ],
                None,
                source_store,
            );
            PorthTypeKind::Int
        }

        // No actual failure case at this time, but leaving this here later for if I get
        // round to adding other types where this is invalid.
        _ => {
            *had_error = true;
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(analyzer, source_store, lexeme, op, &input_ids);
            return;
        }
    };

    analyzer.set_value_type(op_data.outputs[0], new_type);
}
pub(super) fn cast_ptr(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<1>();
    let Some([input]) = analyzer.value_types(input_ids) else { return };

    let new_type = match input {
        PorthTypeKind::Int => PorthTypeKind::Ptr,
        PorthTypeKind::Ptr => {
            let [value] = analyzer.values(input_ids);

            diagnostics::emit_warning(
                op.token.location,
                "unnecessary cast",
                [
                    Label::new(op.token.location).with_color(Color::Yellow),
                    Label::new(value.creator_token.location)
                        .with_message("already a Ptr")
                        .with_color(Color::Cyan),
                ],
                None,
                source_store,
            );
            PorthTypeKind::Ptr
        }

        _ => {
            // Type mismatch.
            *had_error = true;
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(analyzer, source_store, lexeme, op, &input_ids);
            return;
        }
    };

    analyzer.set_value_type(op_data.outputs[0], new_type);
}

pub(super) fn dup(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    depth: usize,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<1>();
    let Some([input]) = analyzer.value_types(input_ids) else { return };

    analyzer.set_value_type(op_data.outputs[0], input);
}

pub(super) fn dup_pair(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);

    for (&input_id, &output_id) in op_data.inputs.iter().zip(&op_data.outputs) {
        let Some([input_type]) = analyzer.value_types([input_id]) else { continue };
        analyzer.set_value_type(output_id, input_type);
    }
}

pub(super) fn push_bool(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_type(op_data.outputs[0], PorthTypeKind::Bool);
}

pub(super) fn push_int(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_type(op_data.outputs[0], PorthTypeKind::Int);
}

pub(super) fn push_str(analyzer: &mut Analyzer, op: &Op, is_c_str: bool) {
    let op_data = analyzer.get_op_io(op.id);

    if is_c_str {
        analyzer.set_value_type(op_data.outputs[0], PorthTypeKind::Ptr);
    } else {
        analyzer.set_value_type(op_data.outputs[0], PorthTypeKind::Int);
        analyzer.set_value_type(op_data.outputs[1], PorthTypeKind::Ptr);
    }
}
