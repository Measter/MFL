use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;

use crate::{
    diagnostics,
    n_ops::SliceNOps,
    opcode::{Direction, Op},
    source_file::{SourceStorage, Spanned},
};

use super::{
    super::{Analyzer, ValueId},
    ensure_stack_depth,
};

pub fn drop(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    count: Spanned<u8>,
) {
    if count.inner == 0 {
        diagnostics::emit_error(
            op.token.location,
            "invalid drop count",
            [Label::new(count.location)
                .with_color(Color::Red)
                .with_message("cannot drop 0 items")],
            None,
            source_store,
        );
        *had_error = true;
        return;
    }

    let count = count.inner.to_usize();

    ensure_stack_depth(analyzer, stack, source_store, had_error, op, count);

    let split_point = stack.len() - count;
    let inputs = stack.split_off(split_point);

    for &input in &inputs {
        analyzer.consume_value(input, op.id);
    }
    analyzer.set_op_io(op, &inputs, &[]);
}

pub fn dup(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    count: Spanned<u8>,
) {
    if count.inner == 0 {
        diagnostics::emit_error(
            op.token.location,
            "invalid duplicate count",
            [Label::new(count.location)
                .with_color(Color::Red)
                .with_message("cannot duplicate 0 items")],
            None,
            source_store,
        );
        *had_error = true;
        return;
    }

    let count = count.inner.to_usize();

    ensure_stack_depth(analyzer, stack, source_store, had_error, op, count);

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

pub fn over(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    depth: Spanned<u8>,
) {
    if depth.inner == 0 {
        diagnostics::emit_warning(
            op.token.location,
            "unclear stack op",
            [Label::new(op.token.location)
                .with_color(Color::Yellow)
                .with_message("using `dup` would make intent clearer")],
            None,
            source_store,
        );
    }

    let depth = depth.inner.to_usize();

    ensure_stack_depth(analyzer, stack, source_store, had_error, op, depth + 1);

    let src_id = stack[stack.len() - 1 - depth];
    let new_id = analyzer.new_value(op.token.location, Some(src_id));
    stack.push(new_id);

    analyzer.set_op_io(op, &[src_id], &[new_id]);
}

pub fn push_str(analyzer: &mut Analyzer, stack: &mut Vec<ValueId>, op: &Op) {
    let str_id = analyzer.new_value(op.token.location, None);
    stack.push(str_id);
    analyzer.set_op_io(op, &[], &[str_id]);
}

pub fn reverse(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    count: Spanned<u8>,
) {
    match count.inner {
        0 | 1 => {
            diagnostics::emit_warning(
                op.token.location,
                "invalid reverse count",
                [Label::new(count.location)
                    .with_color(Color::Yellow)
                    .with_message(format!("cannot reverse {} items", count.inner))],
                None,
                source_store,
            );
        }
        2 => {
            diagnostics::emit_warning(
                op.token.location,
                "unclear stack op",
                [Label::new(count.location)
                    .with_color(Color::Yellow)
                    .with_message("using `swap` wolud make intent clearer")],
                None,
                source_store,
            );
        }
        _ => {}
    }

    let count = count.inner.to_usize();
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, count);

    stack.lastn_mut(count).unwrap().reverse();
}

pub fn rot(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    item_count: Spanned<u8>,
    direction: Direction,
    mut shift_count: Spanned<u8>,
) {
    if item_count.inner == 0 {
        diagnostics::emit_error(
            op.token.location,
            "invalid item count",
            [Label::new(item_count.location)
                .with_color(Color::Red)
                .with_message("cannot rotate 0 items")],
            None,
            source_store,
        );
        *had_error = true;
        return;
    }
    if shift_count.inner > item_count.inner {
        shift_count.inner %= item_count.inner;
        diagnostics::emit_warning(
            op.token.location,
            "truncated shift count",
            [Label::new(shift_count.location)
                .with_color(Color::Red)
                .with_message(format!(
                    "shift count has been truncated to {}",
                    shift_count.inner
                ))],
            None,
            source_store,
        );
    }

    if shift_count.inner == item_count.inner {
        diagnostics::emit_warning(
            op.token.location,
            "rotate is a no-op",
            [Label::new(shift_count.location)
                .with_color(Color::Yellow)
                .with_message(format!(
                    "shift count equals item count ({})",
                    item_count.inner
                ))],
            None,
            source_store,
        );
        return;
    }
    let item_count = item_count.inner.to_usize();
    let shift_count = shift_count.inner.to_usize();
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, item_count);

    let start = stack.len() - item_count;
    match direction {
        Direction::Left => stack[start..].rotate_left(shift_count),
        Direction::Right => stack[start..].rotate_right(shift_count),
    }
}

pub fn swap(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    count: Spanned<u8>,
) {
    if count.inner == 0 {
        diagnostics::emit_warning(
            op.token.location,
            "invalid swap count",
            [Label::new(count.location)
                .with_color(Color::Yellow)
                .with_message("cannot swap 0 items")],
            None,
            source_store,
        );
        return;
    }

    let count = count.inner.to_usize();
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, count * 2);

    let slice_start = stack.len() - count;
    let (rest, a_slice) = stack.split_at_mut(slice_start);
    let (_, b_slice) = rest.split_at_mut(rest.len() - count);

    a_slice.swap_with_slice(b_slice);
}
