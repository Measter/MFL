use smallvec::SmallVec;

use crate::{
    ir::{Op, TypeResolvedOp},
    n_ops::VecNOps,
    pass_manager::static_analysis::{Analyzer, ValueId},
    Stores,
};

use super::ensure_stack_depth;

pub(crate) fn extract_array(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    emit_array: bool,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 2);

    let [array_id, idx] = stack.popn().unwrap();
    analyzer.consume_value(array_id, op.id);
    analyzer.consume_value(idx, op.id);

    let mut outputs = SmallVec::<[_; 2]>::new();

    if emit_array {
        let output_array = analyzer.new_value(op.token.location, Some(array_id));
        outputs.push(output_array);
        stack.push(output_array);
    }

    let output_value = analyzer.new_value(op.token.location, None);
    outputs.push(output_value);
    stack.push(output_value);

    analyzer.set_op_io(op, &[array_id, idx], &outputs);
}

pub(crate) fn extract_struct(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    emit_struct: bool,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 1);

    let struct_id = stack.pop().unwrap();
    analyzer.consume_value(struct_id, op.id);
    let mut outputs = SmallVec::<[_; 2]>::new();

    if emit_struct {
        let output_struct = analyzer.new_value(op.token.location, Some(struct_id));
        outputs.push(output_struct);
        stack.push(output_struct);
    }

    let output_value = analyzer.new_value(op.token.location, None);
    outputs.push(output_value);
    stack.push(output_value);

    analyzer.set_op_io(op, &[struct_id], &outputs);
}

pub(crate) fn insert_array(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    emit_array: bool,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 2);

    let inputs = stack.popn::<3>().unwrap();
    for id in inputs {
        analyzer.consume_value(id, op.id);
    }

    let mut output = None;
    if emit_array {
        // Leave the array on the stack so the user can continue using it.
        let output_id = analyzer.new_value(op.token.location, Some(inputs[1]));
        output = Some(output_id);
        stack.push(output_id);
    }

    analyzer.set_op_io(op, &inputs, output.as_slice());
}
