use crate::{n_ops::VecNOps, opcode::Op, source_file::SourceStorage};

use super::{generate_stack_length_mismatch_diag, Analyzer, ValueId};

pub mod control;
pub mod memory;
pub mod stack_ops;

fn ensure_stack_depth(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    depth: usize,
) {
    if stack.len() < depth {
        generate_stack_length_mismatch_diag(
            source_store,
            op.token.location,
            op.token.location,
            stack.len(),
            depth,
        );
        *had_error = true;

        let num_missing = usize::saturating_sub(depth, stack.len());
        for _ in 0..num_missing {
            let pad_value = analyzer.new_value(op.token.location, None);
            stack.push(pad_value);
        }
    }
}

pub(super) fn eat_one_make_one(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 1);

    let value_id = stack.pop().unwrap();
    analyzer.consume_value(value_id, op.id);
    let new_id = analyzer.new_value(op.token.location, None);

    analyzer.set_op_io(op, &[value_id], &[new_id]);
    stack.push(new_id);
}

pub(super) fn eat_two_make_one(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }
    let new_id = analyzer.new_value(op.token.location, None);

    analyzer.set_op_io(op, &inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn make_one(analyzer: &mut Analyzer, stack: &mut Vec<ValueId>, op: &Op) {
    let new_id = analyzer.new_value(op.token.location, None);
    stack.push(new_id);
    analyzer.set_op_io(op, &[], &[new_id]);
}
