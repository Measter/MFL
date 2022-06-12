use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{generate_type_mismatch_diag, Analyzer, PorthTypeKind},
    source_file::SourceStorage,
};

pub(super) fn compare(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = analyzer.value_types(input_ids) else { return };

    let new_type = match inputs {
        [PorthTypeKind::Int, PorthTypeKind::Int] | [PorthTypeKind::Ptr, PorthTypeKind::Ptr] => {
            PorthTypeKind::Bool
        }

        _ => {
            // Type mismatch
            *had_error = true;
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(analyzer, source_store, lexeme, op, &input_ids);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_types([(output_id, new_type)]);
}

pub(super) fn equal(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(inputs) = analyzer.value_types(input_ids) else { return };

    let new_type = match inputs {
        [PorthTypeKind::Bool, PorthTypeKind::Bool]
        | [PorthTypeKind::Ptr, PorthTypeKind::Ptr]
        | [PorthTypeKind::Int, PorthTypeKind::Int] => PorthTypeKind::Bool,

        _ => {
            // Type mismatch.
            *had_error = true;
            // Don't emit an diagnostic here if any are Unknown, as it's a result of
            // an earlier error.
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(analyzer, source_store, lexeme, op, &input_ids);
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_types([(output_id, new_type)]);
}
