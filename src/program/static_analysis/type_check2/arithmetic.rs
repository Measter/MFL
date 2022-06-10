use crate::{
    interners::Interners,
    opcode::Op,
    program::static_analysis::{generate_type_mismatch_diag, Analyzer, Value},
    source_file::SourceStorage,
    type_check::PorthTypeKind,
};

pub(super) fn add(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_io(op.id);
    let inputs = analyzer.get_values(op_data.inputs.as_slice().try_into().unwrap());

    let new_type = match inputs {
        // One of these was the result of an earlier error. Nothing else to do, just leave.
        type_pattern2!(PorthTypeKind::Unknown, _) | type_pattern2!(_, PorthTypeKind::Unknown) => {
            return
        }

        type_pattern2!(PorthTypeKind::Int, PorthTypeKind::Int) => PorthTypeKind::Int,
        type_pattern2!(PorthTypeKind::Ptr, PorthTypeKind::Int)
        | type_pattern2!(PorthTypeKind::Int, PorthTypeKind::Ptr) => PorthTypeKind::Ptr,

        _ => {
            // Type mismatch
            *had_error = true;

            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(source_store, lexeme, op, &inputs);
            PorthTypeKind::Unknown
        }
    };

    let output_id = op_data.outputs[0];
    let output = analyzer.value_mut(output_id);
    output.porth_type = new_type;
}

pub(super) fn subtract(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn bitnot(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn bitand_bitor(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn multiply_and_shift(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn divmod(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}
