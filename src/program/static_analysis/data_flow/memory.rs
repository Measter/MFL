use intcast::IntCast;

use crate::{
    n_ops::{SliceNOps, VecNOps},
    opcode::Op,
    source_file::SourceStorage,
};

use super::{
    super::{Analyzer, ValueId},
    ensure_stack_depth,
};

pub fn pack(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    count: u8,
) {
    ensure_stack_depth(
        analyzer,
        stack,
        source_store,
        had_error,
        op,
        count.to_usize(),
    );

    let mut inputs = Vec::new();
    let input_ids = stack.lastn(count.to_usize()).unwrap();
    for &id in input_ids {
        inputs.push(id);
        analyzer.consume_value(id, op.id);
    }

    stack.truncate(stack.len() - input_ids.len());

    let output = analyzer.new_value(op);
    stack.push(output);
    analyzer.set_op_io(op, &inputs, &[output]);
}

pub fn unpack(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    count: u8,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 1);
    let input_id = stack.pop().unwrap();

    let mut outputs = Vec::new();

    for _ in 0..count {
        let id = analyzer.new_value(op);
        stack.push(id);
        outputs.push(id);
    }

    analyzer.set_op_io(op, &[input_id], &outputs);
}

pub fn store(
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

    analyzer.set_op_io(op, &inputs, &[]);
}
