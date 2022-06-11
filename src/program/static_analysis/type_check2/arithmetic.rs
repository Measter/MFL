use crate::{
    interners::Interners,
    n_ops::NOps,
    opcode::Op,
    program::static_analysis::{generate_type_mismatch_diag, Analyzer, PorthTypeKind, Value},
    source_file::SourceStorage,
};

pub(super) fn add(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let inputs = analyzer.value_types(input_ids);

    let new_type = match inputs {
        // One of these was the result of an earlier error. Nothing else to do, just leave.
        [PorthTypeKind::Unknown, _] | [_, PorthTypeKind::Unknown] => return,

        [PorthTypeKind::Int, PorthTypeKind::Int] => PorthTypeKind::Int,
        [PorthTypeKind::Ptr, PorthTypeKind::Int] | [PorthTypeKind::Int, PorthTypeKind::Ptr] => {
            PorthTypeKind::Ptr
        }

        _ => {
            // Type mismatch
            *had_error = true;

            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(analyzer, source_store, lexeme, op, &input_ids);
            PorthTypeKind::Unknown
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_types([(output_id, new_type)]);
}

pub(super) fn subtract(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let inputs = analyzer.value_types(input_ids);

    let new_type = match inputs {
        // One of these was the result of an earlier error. Nothing else to do, just leave.
        [PorthTypeKind::Unknown, _] | [_, PorthTypeKind::Unknown] => return,

        [PorthTypeKind::Int, PorthTypeKind::Int] => PorthTypeKind::Int,
        [PorthTypeKind::Ptr, PorthTypeKind::Ptr] => PorthTypeKind::Int,
        [PorthTypeKind::Ptr, PorthTypeKind::Int] => PorthTypeKind::Ptr,

        _ => {
            // Type mismatch
            *had_error = true;

            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(analyzer, source_store, lexeme, op, &input_ids);
            PorthTypeKind::Unknown
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_types([(output_id, new_type)]);
}

pub(super) fn bitnot(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs[0];
    let input = analyzer.value_types([input_id]);

    let new_type = match input[0] {
        // One of these was the result of an earlier error. Nothing else to do, just leave.
        PorthTypeKind::Unknown => return,

        PorthTypeKind::Int | PorthTypeKind::Bool => input[0],

        _ => {
            // Type mismatch
            *had_error = true;
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(analyzer, source_store, lexeme, op, &[input_id]);

            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_types([(output_id, new_type)]);
}

pub(super) fn bitand_bitor(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let inputs = analyzer.value_types(input_ids);

    let new_type = match inputs {
        // One of these was the result of an earlier error. Nothing else to do, just leave.
        [PorthTypeKind::Unknown, _] | [_, PorthTypeKind::Unknown] => return,

        [PorthTypeKind::Int, PorthTypeKind::Int] => PorthTypeKind::Int,
        [PorthTypeKind::Bool, PorthTypeKind::Bool] => PorthTypeKind::Bool,

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

pub(super) fn multiply_and_shift(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let inputs = analyzer.value_types(input_ids);

    let new_type = match inputs {
        // One of these was the result of an earlier error. Nothing else to do, just leave.
        [PorthTypeKind::Unknown, _] | [_, PorthTypeKind::Unknown] => return,

        [PorthTypeKind::Int, PorthTypeKind::Int] => PorthTypeKind::Int,

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

pub(super) fn divmod(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let inputs = analyzer.value_types(input_ids);

    let new_type = match inputs {
        // One of these was the result of an earlier error. Nothing else to do, just leave.
        [PorthTypeKind::Unknown, _] | [_, PorthTypeKind::Unknown] => return,
        [PorthTypeKind::Int, PorthTypeKind::Int] => PorthTypeKind::Int,

        _ => {
            // Type mismatch
            *had_error = true;
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(analyzer, source_store, lexeme, op, &input_ids);
            return;
        }
    };

    let [quot_id, rem_id] = *op_data.outputs.as_arr::<2>();
    analyzer.set_value_types([(quot_id, new_type), (rem_id, new_type)]);
}
