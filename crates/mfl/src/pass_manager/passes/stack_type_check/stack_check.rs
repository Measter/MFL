use crate::{
    ir::{Op, TypeResolvedOp},
    n_ops::VecNOps,
    pass_manager::static_analysis::{generate_stack_length_mismatch_diag, Analyzer, ValueId},
    Stores,
};

fn ensure_stack_depth(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    depth: usize,
) {
    if stack.len() < depth {
        generate_stack_length_mismatch_diag(
            stores,
            op.token.location,
            op.token.location,
            stack.len(),
            depth,
            None,
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
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 1);

    let value_id = stack.pop().unwrap();
    analyzer.consume_value(value_id, op.id);
    let new_id = analyzer.new_value(op.token.location, None);

    analyzer.set_op_io(op, &[value_id], &[new_id]);
    stack.push(new_id);
}

pub(super) fn eat_two_make_one(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
) {
    ensure_stack_depth(stores, analyzer, had_error, stack, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }
    let new_id = analyzer.new_value(op.token.location, None);

    analyzer.set_op_io(op, &inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn make_one(analyzer: &mut Analyzer, stack: &mut Vec<ValueId>, op: &Op<TypeResolvedOp>) {
    let new_id = analyzer.new_value(op.token.location, None);
    stack.push(new_id);
    analyzer.set_op_io(op, &[], &[new_id]);
}
