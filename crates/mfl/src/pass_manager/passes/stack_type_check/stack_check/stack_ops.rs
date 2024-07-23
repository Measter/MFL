use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{Direction, Op, TypeResolvedOp},
    n_ops::SliceNOps,
    pass_manager::static_analysis::{Analyzer, ValueId},
    stores::source::Spanned,
    Stores,
};

use super::ensure_stack_depth;

pub(crate) fn dup(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    count: Spanned<u8>,
) {
    if count.inner == 0 {
        diagnostics::emit_error(
            stores,
            op.token.location,
            "invalid duplicate count",
            [Label::new(count.location)
                .with_color(Color::Red)
                .with_message("cannot duplicate 0 item")],
            None,
        );
        had_error.set();
        return;
    }

    let count = count.inner.to_usize();
    ensure_stack_depth(stores, analyzer, had_error, stack, op, count);

    let input_range = (stack.len() - count)..stack.len();
    let output_range_start = stack.len();
    let input_values: SmallVec<[ValueId; 20]> =
        stack[input_range.clone()].iter().copied().collect();

    for input_id in input_values {
        let new_id = analyzer.new_value(op.token.location, Some(input_id));
        stack.push(new_id);
    }

    analyzer.set_op_io(op, &stack[input_range], &stack[output_range_start..]);
}

pub(crate) fn drop(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    count: Spanned<u8>,
) {
    if count.inner == 0 {
        diagnostics::emit_error(
            stores,
            op.token.location,
            "invalid drop count",
            [Label::new(count.location)
                .with_color(Color::Red)
                .with_message("cannot drop 0 items")],
            None,
        );
        had_error.set();
        return;
    }

    let count = count.inner.to_usize();
    ensure_stack_depth(stores, analyzer, had_error, stack, op, count);

    let split_point = stack.len() - count;
    let inputs = stack.split_off(split_point);

    for &input in &inputs {
        analyzer.consume_value(input, op.id);
    }

    analyzer.set_op_io(op, &inputs, &[]);
}

pub(crate) fn over(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    depth: Spanned<u8>,
) {
    if depth.inner == 0 {
        diagnostics::emit_warning(
            stores,
            op.token.location,
            "unclear stack op",
            [Label::new(op.token.location)
                .with_color(Color::Yellow)
                .with_message("using `dup` would be intent clearer")],
            None,
        )
    };

    let depth = depth.inner.to_usize();
    ensure_stack_depth(stores, analyzer, had_error, stack, op, depth + 1);

    let src_id = stack[stack.len() - 1 - depth];
    let new_id = analyzer.new_value(op.token.location, Some(src_id));
    stack.push(new_id);

    analyzer.set_op_io(op, &[src_id], &[new_id]);
}

pub(crate) fn reverse(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    count: Spanned<u8>,
) {
    match count.inner {
        0 | 1 => {
            // TODO: Change this message to say it's a noop.
            diagnostics::emit_warning(
                stores,
                op.token.location,
                "invalid reverse count",
                [Label::new(count.location)
                    .with_color(Color::Yellow)
                    .with_message(format!("cannot reverse {} items", count.inner))],
                None,
            );
        }
        2 => diagnostics::emit_warning(
            stores,
            op.token.location,
            "unclear stack op",
            [Label::new(count.location)
                .with_color(Color::Yellow)
                .with_message("using `swat would make intent clearer")],
            None,
        ),
        _ => {}
    }

    let count = count.inner.to_usize();
    ensure_stack_depth(stores, analyzer, had_error, stack, op, count);

    stack.lastn_mut(count).unwrap().reverse();
}

pub(crate) fn rotate(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    item_count: Spanned<u8>,
    direction: crate::ir::Direction,
    mut shift_count: Spanned<u8>,
) {
    if item_count.inner == 0 {
        diagnostics::emit_error(
            stores,
            op.token.location,
            "invalid item count",
            [Label::new(item_count.location)
                .with_color(Color::Red)
                .with_message("cannot rotate 0 items")],
            None,
        );
        had_error.set();
        return;
    }
    if shift_count.inner >= item_count.inner {
        shift_count.inner %= item_count.inner;
        diagnostics::emit_warning(
            stores,
            op.token.location,
            "truncated shift count",
            [Label::new(shift_count.location)
                .with_color(Color::Yellow)
                .with_message(format!(
                    "shift count has been truncated to {}",
                    shift_count.inner
                ))],
            None,
        );
    }

    if shift_count.inner == 0 {
        diagnostics::emit_warning(
            stores,
            op.token.location,
            "rotate is a no-op",
            [Label::new(shift_count.location)
                .with_color(Color::Yellow)
                .with_message("no items will be rotate")],
            None,
        );
    }

    let item_count = item_count.inner.to_usize();
    let shift_count = shift_count.inner.to_usize();
    ensure_stack_depth(stores, analyzer, had_error, stack, op, item_count);

    let items = stack.lastn_mut(item_count).unwrap();
    match direction {
        Direction::Left => items.rotate_left(shift_count),
        Direction::Right => items.rotate_right(shift_count),
    }
}

pub(crate) fn swap(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    count: Spanned<u8>,
) {
    if count.inner == 0 {
        diagnostics::emit_warning(
            stores,
            op.token.location,
            "invalid swap count",
            [Label::new(count.location)
                .with_color(Color::Yellow)
                .with_message("cannot swap 0 items")],
            None,
        );
        return;
    }

    let count = count.inner.to_usize();
    ensure_stack_depth(stores, analyzer, had_error, stack, op, count * 2);

    let slice_start = stack.len() - count;
    let (rest, a_slice) = stack.split_at_mut(slice_start);
    let (_, b_slice) = rest.split_at_mut(rest.len() - count);

    a_slice.swap_with_slice(b_slice);
}
