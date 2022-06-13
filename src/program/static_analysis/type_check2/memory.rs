use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{generate_type_mismatch_diag, Analyzer, PorthTypeKind},
    source_file::SourceStorage,
    Width,
};

pub(super) fn load(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    width: Width,
    kind: PorthTypeKind,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input = op_data.inputs[0];
    let Some([input_type]) = analyzer.value_types([input]) else { return };

    if input_type != PorthTypeKind::Ptr {
        *had_error = true;
        let lexeme = interner.resolve_lexeme(op.token.lexeme);
        generate_type_mismatch_diag(analyzer, source_store, lexeme, op, &[input]);
    }

    analyzer.set_value_type(op_data.outputs[0], kind);
}
pub(super) fn store(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    kind: PorthTypeKind,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(input_types) = analyzer.value_types(input_ids) else { return };

    if input_types != [kind, PorthTypeKind::Ptr] {
        // Type mismatch
        *had_error = true;
        let lexeme = interner.resolve_lexeme(op.token.lexeme);
        generate_type_mismatch_diag(analyzer, source_store, lexeme, op, &input_ids);
    }
}
