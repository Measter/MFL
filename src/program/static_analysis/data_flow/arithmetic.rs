use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::{NOps, PopN},
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

pub(super) fn eat_two_make_one(
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
    let new_id = analyzer.new_value(op);

    analyzer.set_op_io(op, &inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn bitnot(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 1);

    let value_id = stack.pop().unwrap();
    analyzer.consume_value(value_id, op.id);
    let new_id = analyzer.new_value(op);

    analyzer.set_op_io(op, &[value_id], &[new_id]);
    stack.push(new_id);
}

pub(super) fn divmod(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
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
