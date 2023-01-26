use ariadne::{Color, Label};

use crate::{
    diagnostics,
    lexer::Token,
    opcode::{Direction, Op},
    source_file::SourceStorage,
};

use super::{
    super::{Analyzer, ValueId},
    ensure_stack_depth,
};

pub(super) fn drop(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    count: usize,
    count_token: Token,
) {
    if count == 0 {
        diagnostics::emit_error(
            op.token.location,
            "invalid drop count",
            [Label::new(count_token.location)
                .with_color(Color::Red)
                .with_message("cannot drop 0 items")],
            None,
            source_store,
        );
        *had_error = true;
        return;
    }

    ensure_stack_depth(analyzer, stack, source_store, had_error, op, count);

    let split_point = stack.len() - count;
    let inputs = stack.split_off(split_point);

    for &input in &inputs {
        analyzer.consume_value(input, op.id);
    }
    analyzer.set_op_io(op, &inputs, &[]);
}

pub(super) fn dup(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    count: usize,
    count_token: Token,
) {
    if count == 0 {
        diagnostics::emit_error(
            op.token.location,
            "invalid duplicate count",
            [Label::new(count_token.location)
                .with_color(Color::Red)
                .with_message("cannot duplicate 0 items")],
            None,
            source_store,
        );
        *had_error = true;
        return;
    }

    ensure_stack_depth(analyzer, stack, source_store, had_error, op, count);

    let input_range = (stack.len() - count)..stack.len();
    let output_range_start = stack.len();
    for _ in 0..count {
        let new_id = analyzer.new_value(op);
        stack.push(new_id);
    }
    analyzer.set_op_io(op, &stack[input_range], &stack[output_range_start..]);
}

pub(super) fn over(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    depth: usize,
) {
    if depth == 0 {
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

    ensure_stack_depth(analyzer, stack, source_store, had_error, op, depth + 1);

    let src_id = stack[stack.len() - 1 - depth];
    let new_id = analyzer.new_value(op);
    stack.push(new_id);

    dbg!(src_id);

    analyzer.set_op_io(op, &[src_id], &[new_id]);
}

pub(super) fn push_str(analyzer: &mut Analyzer, stack: &mut Vec<ValueId>, op: &Op, is_c_str: bool) {
    let ptr_id = analyzer.new_value(op);

    if is_c_str {
        stack.push(ptr_id);
        analyzer.set_op_io(op, &[], &[ptr_id]);
    } else {
        let len_id = analyzer.new_value(op);
        stack.push(len_id);
        stack.push(ptr_id);
        analyzer.set_op_io(op, &[], &[len_id, ptr_id]);
    };
}

pub(super) fn rot(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    item_count: usize,
    direction: Direction,
    mut shift_count: usize,
    item_count_token: Token,
    shift_count_token: Token,
) {
    if item_count == 0 {
        diagnostics::emit_error(
            op.token.location,
            "invalid item count",
            [Label::new(item_count_token.location)
                .with_color(Color::Red)
                .with_message("cannot rotate 0 items")],
            None,
            source_store,
        );
        *had_error = true;
        return;
    }
    if shift_count > item_count {
        shift_count %= item_count;
        diagnostics::emit_warning(
            op.token.location,
            "truncated shift count",
            [Label::new(shift_count_token.location)
                .with_color(Color::Red)
                .with_message(format!("shift count has been truncated to {shift_count}"))],
            None,
            source_store,
        );
        shift_count %= item_count;
    }

    if shift_count == item_count {
        diagnostics::emit_warning(
            op.token.location,
            "rotate is a no-op",
            [Label::new(shift_count_token.location)
                .with_color(Color::Yellow)
                .with_message(format!("shift count equals item count ({item_count})"))],
            None,
            source_store,
        );
        return;
    }

    ensure_stack_depth(analyzer, stack, source_store, had_error, op, item_count);

    let start = stack.len() - 3;
    match direction {
        Direction::Left => stack[start..].rotate_left(shift_count),
        Direction::Right => stack[start..].rotate_right(shift_count),
    }
}

pub(super) fn swap(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    count: usize,
    count_token: Token,
) {
    if count == 0 {
        diagnostics::emit_warning(
            op.token.location,
            "invalid swap count",
            [Label::new(count_token.location)
                .with_color(Color::Yellow)
                .with_message("cannot swap 0 items")],
            None,
            source_store,
        );
    }
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, count * 2);

    let slice_start = stack.len() - count;
    let (rest, a_slice) = stack.split_at_mut(slice_start);
    let (_, b_slice) = rest.split_at_mut(rest.len() - count);

    a_slice.swap_with_slice(b_slice);
}
