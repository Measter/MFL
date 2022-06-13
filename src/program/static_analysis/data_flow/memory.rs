use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::{SliceNOps, VecNOps},
    opcode::Op,
    program::static_analysis::PorthTypeKind,
    source_file::SourceStorage,
};

use super::{
    super::{
        generate_stack_length_mismatch_diag, generate_type_mismatch_diag, Analyzer, ConstVal,
        PtrId, Value, ValueId,
    },
    ensure_stack_depth,
};

pub(super) fn store(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    kind: PorthTypeKind,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }

    analyzer.set_op_io(op, &inputs, &[]);
}
