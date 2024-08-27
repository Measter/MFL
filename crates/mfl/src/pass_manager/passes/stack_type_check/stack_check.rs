use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    n_ops::VecNOps,
    pass_manager::static_analysis::generate_stack_length_mismatch_diag,
    stores::{ops::OpId, values::ValueId},
    Stores,
};

pub mod control;
pub mod memory;
pub mod stack_ops;

fn ensure_stack_depth(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    depth: usize,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    if stack.len() < depth {
        generate_stack_length_mismatch_diag(
            stores,
            item_id,
            op_loc,
            op_loc,
            stack.len(),
            depth,
            None,
        );
        had_error.set();

        let num_missing = usize::saturating_sub(depth, stack.len());
        for _ in 0..num_missing {
            let pad_value = stores.values.new_value(op_loc, None);
            stack.push(pad_value);
        }
    }
}

pub(super) fn eat_one_make_one(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
) {
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, 1);

    let value_id = stack.pop().unwrap();
    stores.values.consume_value(value_id, op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let new_id = stores.values.new_value(op_loc, None);

    stores.ops.set_op_io(op_id, &[value_id], &[new_id]);
    stack.push(new_id);
}

pub(super) fn eat_two_make_one(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
) {
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, 2);

    let inputs = stack.popn::<2>().unwrap();
    for value_id in inputs {
        stores.values.consume_value(value_id, op_id);
    }
    let op_loc = stores.ops.get_token(op_id).location;
    let new_id = stores.values.new_value(op_loc, None);

    stores.ops.set_op_io(op_id, &inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn make_one(stores: &mut Stores, stack: &mut Vec<ValueId>, op_id: OpId) {
    let op_loc = stores.ops.get_token(op_id).location;
    let new_id = stores.values.new_value(op_loc, None);
    stack.push(new_id);
    stores.ops.set_op_io(op_id, &[], &[new_id]);
}
