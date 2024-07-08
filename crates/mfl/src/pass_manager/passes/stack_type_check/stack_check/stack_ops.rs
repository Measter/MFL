use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;

use crate::{
    diagnostics,
    ir::{Op, TypeResolvedOp},
    pass_manager::static_analysis::{Analyzer, ValueId},
    source_file::Spanned,
    Stores,
};

use super::ensure_stack_depth;

pub(crate) fn dup(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
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
        *had_error = true;
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
    had_error: &mut bool,
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
        *had_error = true;
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
