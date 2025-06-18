use intcast::IntCast;
use smallvec::SmallVec;
use stores::{items::ItemId, source::Spanned};

use crate::{
    error_signal::ErrorSignal,
    ir::Direction,
    stores::{diagnostics::Diagnostic, ops::OpId, values::ValueId},
    Stores,
};

use super::ensure_stack_depth;

pub(crate) fn dup(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    count: Spanned<u8>,
) {
    let op_loc = stores.ops.get_token_location(op_id);

    if count.inner == 0 {
        Diagnostic::error(op_loc, "invalid duplicate count")
            .primary_label_message("cannot duplicate 0 items")
            .attached(stores.diags, item_id);

        had_error.set();
        return;
    }

    let count = count.inner.to_usize();
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, count);

    let input_range = (stack.len() - count)..stack.len();
    let output_range_start = stack.len();
    let input_values: SmallVec<[ValueId; 20]> =
        stack[input_range.clone()].iter().copied().collect();

    for input_id in input_values {
        let new_id = stores.values.new_value(op_loc, Some(input_id));
        stack.push(new_id);
    }

    stores
        .ops
        .set_op_io(op_id, &stack[input_range], &stack[output_range_start..]);
}

pub(crate) fn drop(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    count: Spanned<u8>,
) {
    let op_loc = stores.ops.get_token_location(op_id);
    if count.inner == 0 {
        Diagnostic::error(op_loc, "invalid drop count")
            .primary_label_message("cannot drop 0 items")
            .attached(stores.diags, item_id);
        had_error.set();
        return;
    }

    let count = count.inner.to_usize();
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, count);

    let split_point = stack.len() - count;
    let inputs = stack.split_off(split_point);
    stores.ops.set_op_io(op_id, &inputs, &[]);
}

pub(crate) fn over(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    depth: Spanned<u8>,
) {
    let op_loc = stores.ops.get_token_location(op_id);
    if depth.inner == 0 {
        Diagnostic::warning(op_loc, "unclear stack op")
            .primary_label_message("using `dup` would make intent clearer")
            .attached(stores.diags, item_id);
    };

    let depth = depth.inner.to_usize();
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, depth + 1);

    let src_id = stack[stack.len() - 1 - depth];
    let new_id = stores.values.new_value(op_loc, Some(src_id));
    stack.push(new_id);

    stores.ops.set_op_io(op_id, &[src_id], &[new_id]);
}

pub(crate) fn reverse(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    count: Spanned<u8>,
) {
    let op_loc = stores.ops.get_token_location(op_id);
    match count.inner {
        0 | 1 => {
            Diagnostic::warning(
                op_loc,
                format!("reversing {} items is a no-op", count.inner),
            )
            .attached(stores.diags, item_id);
        }
        2 => {
            Diagnostic::warning(op_loc, "unclear stack op")
                .primary_label_message("using `swap` would make intent clearer")
                .attached(stores.diags, item_id);
        }
        _ => {}
    }

    let count = count.inner.to_usize();
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, count);

    let mut inputs: SmallVec<[_; 8]> = stack.drain(stack.len() - count..).collect();
    assert_eq!(inputs.len(), count);
    inputs.reverse();

    let mut outputs = SmallVec::<[_; 8]>::new();
    for &input in &inputs {
        let new_value = stores.values.new_value(op_loc, Some(input));
        outputs.push(new_value);
        stack.push(new_value);
    }

    stores.ops.set_op_io(op_id, &inputs, &outputs);
}

pub(crate) fn rotate(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    item_count: Spanned<u8>,
    direction: Direction,
    mut shift_count: Spanned<u8>,
) {
    let op_loc = stores.ops.get_token_location(op_id);
    if item_count.inner == 0 {
        Diagnostic::warning(op_loc, "rotating 0 items is a no-op").attached(stores.diags, item_id);
        return;
    }
    if shift_count.inner >= item_count.inner {
        shift_count.inner %= item_count.inner;
        Diagnostic::warning(op_loc, "truncated shift count")
            .primary_label_message(format!(
                "shift count has been truncated to {}",
                shift_count.inner
            ))
            .attached(stores.diags, item_id);
    }

    if shift_count.inner == 0 {
        Diagnostic::warning(op_loc, "rotate is a no-op")
            .primary_label_message("no items wills be rotate")
            .attached(stores.diags, item_id);
    }

    let item_count = item_count.inner.to_usize();
    let shift_count = shift_count.inner.to_usize();
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, item_count);

    let mut inputs: SmallVec<[_; 8]> = stack.drain(stack.len() - item_count..).collect();
    assert_eq!(inputs.len(), item_count);
    match direction {
        Direction::Left => inputs.rotate_left(shift_count),
        Direction::Right => inputs.rotate_right(shift_count),
    }

    let mut outputs = SmallVec::<[_; 8]>::new();
    for &input in &inputs {
        let new_value = stores.values.new_value(op_loc, Some(input));
        outputs.push(new_value);
        stack.push(new_value);
    }

    stores.ops.set_op_io(op_id, &inputs, &outputs);
}

pub(crate) fn swap(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    item_id: ItemId,
    op_id: OpId,
    count: Spanned<u8>,
) {
    let op_loc = stores.ops.get_token_location(op_id);

    if count.inner == 0 {
        Diagnostic::warning(op_loc, "swapping 0 items is a no-op").attached(stores.diags, item_id);
        return;
    }

    let count = count.inner.to_usize();
    ensure_stack_depth(stores, had_error, stack, item_id, op_id, count * 2);

    let mut inputs: SmallVec<[_; 8]> = stack.drain(stack.len() - count * 2..).collect();
    assert_eq!(inputs.len(), count * 2);
    inputs.rotate_left(count);

    let mut outputs = SmallVec::<[_; 8]>::new();
    for &input in &inputs {
        let new_value = stores.values.new_value(op_loc, Some(input));
        outputs.push(new_value);
        stack.push(new_value);
    }

    stores.ops.set_op_io(op_id, &inputs, &outputs);
}
