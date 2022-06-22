use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::{SliceNOps, VecNOps},
    opcode::{Op, OpCode},
    source_file::SourceStorage,
};

use super::{
    super::{
        generate_stack_length_mismatch_diag, generate_type_mismatch_diag, Analyzer, ConstVal,
        Value, ValueId,
    },
    ensure_stack_depth,
};

pub(super) fn divmod(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }

    let quot_id = analyzer.new_value(op);
    let rem_id = analyzer.new_value(op);
    analyzer.set_op_io(op, &inputs, &[quot_id, rem_id]);
    stack.push(quot_id);
    stack.push(rem_id);
}
