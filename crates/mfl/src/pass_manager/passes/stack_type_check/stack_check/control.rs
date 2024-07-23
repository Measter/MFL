use std::cmp::Ordering;

use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;
use tracing::trace;

use crate::{
    context::{Context, ItemId},
    diagnostics::{self, build_creator_label_chain},
    error_signal::ErrorSignal,
    ir::{If, TypeResolvedOp, While},
    n_ops::SliceNOps,
    pass_manager::{
        static_analysis::{
            generate_stack_length_mismatch_diag, Analyzer, IfMerge, ValueId, WhileMerge,
            WhileMerges,
        },
        PassContext,
    },
    stores::{ops::Op, source::Spanned},
    Stores,
};

use super::ensure_stack_depth;

pub(crate) fn epilogue_return(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    item_id: ItemId,
) {
    let item_header = ctx.get_item_header(item_id);
    let item_sig = ctx.urir().get_item_signature(item_id);

    let exit_sig = &item_sig.exit.inner;
    if stack.len() != exit_sig.len() {
        let mut labels = vec![
            Label::new(op.token.location)
                .with_color(Color::Red)
                .with_message("returning here"),
            Label::new(item_sig.exit.location)
                .with_color(Color::Cyan)
                .with_message("return type defined here"),
        ];

        match stack.len().cmp(&exit_sig.len()) {
            Ordering::Less => {
                let num_missing = usize::saturating_sub(exit_sig.len(), stack.len());
                for _ in 0..num_missing {
                    let pad_value = analyzer.new_value(op.token.location, None);
                    stack.push(pad_value);
                }
            }
            Ordering::Greater => {
                let unused_values = stack[..stack.len() - exit_sig.len()]
                    .iter()
                    .zip(0..)
                    .map(|(&id, idx)| (id, idx, "unused value"));
                let unused_value_labels =
                    build_creator_label_chain(analyzer, unused_values, Color::Green, Color::Cyan);
                labels.extend(unused_value_labels);
            }
            Ordering::Equal => unreachable!(),
        }

        diagnostics::emit_error(
            stores,
            op.token.location,
            format!(
                "function '{}' return {}, found {}",
                stores.strings.resolve(item_header.name.inner),
                exit_sig.len(),
                stack.len()
            ),
            labels,
            None,
        );

        had_error.set();
    }

    let inputs = stack.lastn(exit_sig.len()).unwrap();

    for &value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }
    analyzer.set_op_io(op, inputs, &[]);
    let len = inputs.len();
    stack.truncate(stack.len() - len);
}

pub(crate) fn prologue(
    ctx: &mut Context,
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    item_id: ItemId,
) {
    let mut outputs = SmallVec::<[_; 8]>::new();
    let sig = ctx.urir().get_item_signature(item_id);

    for arg in &sig.entry.inner {
        let new_id = analyzer.new_value(arg.location, None);
        outputs.push(new_id);
        stack.push(new_id);
    }

    analyzer.set_op_io(op, &[], &outputs);
}

pub(crate) fn syscall(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    num_args: Spanned<u8>,
) {
    if !matches!(num_args.inner, 1..=7) {
        diagnostics::emit_error(
            stores,
            op.token.location,
            "invalid syscall size",
            [Label::new(num_args.location)
                .with_color(Color::Red)
                .with_message("valid syscall sizes are 1..=7")],
            None,
        );
        had_error.set();
        return;
    }

    let num_args = num_args.inner.to_usize();
    ensure_stack_depth(stores, analyzer, had_error, stack, op, num_args);

    let inputs = stack.split_off(stack.len() - num_args);
    for &value_id in &inputs {
        analyzer.consume_value(value_id, op.id);
    }

    let new_id = analyzer.new_value(op.token.location, None);
    analyzer.set_op_io(op, &inputs, &[new_id]);
    stack.push(new_id);
}

pub(crate) fn call_function_const(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op: &Op<TypeResolvedOp>,
    callee_id: ItemId,
) {
    let callee_sig = ctx.urir().get_item_signature(callee_id);
    let entry_arg_count = callee_sig.entry.inner.len();

    if stack.len() < entry_arg_count {
        diagnostics::emit_error(
            stores,
            op.token.location,
            format!(
                "procedure takes {entry_arg_count} arguments, found {}",
                stack.len()
            ),
            [
                Label::new(op.token.location).with_color(Color::Red),
                Label::new(callee_sig.entry.location)
                    .with_color(Color::Cyan)
                    .with_message("signature defined here"),
            ],
            None,
        );
        had_error.set();

        let num_missing = usize::saturating_sub(entry_arg_count, stack.len());
        for _ in 0..num_missing {
            let pad_value = analyzer.new_value(op.token.location, None);
            stack.push(pad_value);
        }
    }

    let inputs: SmallVec<[_; 8]> = stack.drain(stack.len() - entry_arg_count..).collect();
    for &value_id in &inputs {
        analyzer.consume_value(value_id, op.id);
    }

    let mut outputs = SmallVec::<[_; 8]>::new();
    for _ in &callee_sig.exit.inner {
        let new_id = analyzer.new_value(op.token.location, None);
        outputs.push(new_id);
        stack.push(new_id);
    }

    analyzer.set_op_io(op, &inputs, &outputs);
}

pub(crate) fn analyze_if(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
    op: &Op<TypeResolvedOp>,
    if_op: &If<TypeResolvedOp>,
) {
    let mut condition_values = SmallVec::<[_; 1]>::new();

    // Evaluate condition.
    super::super::analyze_block(
        ctx,
        stores,
        analyzer,
        pass_ctx,
        had_error,
        item_id,
        &if_op.condition.block,
        stack,
        max_stack_depth,
    );

    // We expect there to be a boolean value on teh top of the stack afterwards.
    if stack.is_empty() {
        generate_stack_length_mismatch_diag(
            stores,
            if_op.tokens.do_token,
            if_op.tokens.do_token,
            stack.len(),
            1,
            None,
        );

        had_error.set();

        // Pad the stack out to the expected length so the rest of the logic makes sense.
        stack.push(analyzer.new_value(op.token.location, None));
    }
    condition_values.push(stack.pop().unwrap());
    let initial_stack: SmallVec<[_; 20]> = stack.iter().copied().collect();

    // Now we can do the then-block
    super::super::analyze_block(
        ctx,
        stores,
        analyzer,
        pass_ctx,
        had_error,
        item_id,
        &if_op.then_block.block,
        stack,
        max_stack_depth,
    );

    // We always have an else block, so save our current stack state for comparison.
    let then_block_stack: SmallVec<[_; 20]> = stack.iter().copied().collect();
    let then_block_sample_location = if_op.tokens.else_token;

    // Restore our stack back to after the condition.
    stack.clear();
    stack.extend_from_slice(&initial_stack);

    // Now analyze the else block.
    super::super::analyze_block(
        ctx,
        stores,
        analyzer,
        pass_ctx,
        had_error,
        item_id,
        &if_op.else_block.block,
        stack,
        max_stack_depth,
    );

    let mut body_merges = Vec::new();

    if if_op.then_block.is_terminal && if_op.else_block.is_terminal {
        // Both are terminal, so we don't need to do any checking.
        trace!("both branches terminate");
    } else if if_op.then_block.is_terminal {
        // We only need to "merge" for the else block, so we can just take the result of the else block as
        // the stack state.
        trace!("then-branch terminates, leaving stack as else-branch resulted");
    } else if if_op.else_block.is_terminal {
        // Same logic as the previous branch, except for the then-block.
        stack.clear();
        stack.extend_from_slice(&then_block_stack);
        trace!("else-branch terminates, leaving stack as then-branch resulted");
    } else {
        // Neither diverge, so we need to check that they both left the stack the same length,
        // and create merge values for values that differ.
        if stack.len() != then_block_stack.len() {
            generate_stack_length_mismatch_diag(
                stores,
                then_block_sample_location,
                if_op.tokens.end_token,
                stack.len(),
                then_block_stack.len(),
                None,
            );
            had_error.set();
        }

        for (then_value_id, else_value_id) in then_block_stack
            .into_iter()
            .zip(stack)
            .filter(|(a, b)| &a != b)
        {
            let output_value_id = analyzer.new_value(op.token.location, None);
            trace!(
                ?then_value_id,
                ?else_value_id,
                ?output_value_id,
                "defining merge for IF"
            );

            body_merges.push(IfMerge {
                then_value: then_value_id,
                else_value: *else_value_id,
                output_value: output_value_id,
            });
            *else_value_id = output_value_id;
        }
    }

    analyzer.set_op_io(op, &condition_values, &[]);
    analyzer.set_if_merges(op, body_merges);
}

pub(crate) fn analyze_while(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
    op: &Op<TypeResolvedOp>,
    while_op: &While<TypeResolvedOp>,
) {
    let pre_condition_stack: SmallVec<[_; 20]> = stack.iter().copied().collect();

    // Evaluate the condition.
    super::super::analyze_block(
        ctx,
        stores,
        analyzer,
        pass_ctx,
        had_error,
        item_id,
        &while_op.condition.block,
        stack,
        max_stack_depth,
    );

    // We expect there to be a boolean value on teh top of the stack afterwards.
    if stack.is_empty() {
        generate_stack_length_mismatch_diag(
            stores,
            while_op.tokens.do_token,
            while_op.tokens.do_token,
            stack.len(),
            1,
            None,
        );

        had_error.set();

        // Pad the stack out to the expected length so the rest of the logic makes sense.
        stack.push(analyzer.new_value(op.token.location, None));
    }
    let condition_value = stack.pop().unwrap();

    // The condition cannot be allowed to otherwise change the depth of the stack, as it could be
    // executed an arbitrary number of times.
    // TODO: Allow the condition to alter the stack, as long as the body restores it.
    if stack.len() != pre_condition_stack.len() {
        generate_stack_length_mismatch_diag(
            stores,
            op.token.location,
            while_op.tokens.do_token,
            stack.len(),
            pre_condition_stack.len(),
            None,
        );

        had_error.set();

        // Pad the stack out to the expected length so the rest of the logict makes sense.
        for _ in 0..(pre_condition_stack.len()).saturating_sub(stack.len()) {
            stack.push(analyzer.new_value(op.token.location, None));
        }
    }

    let mut condition_merges = SmallVec::new();

    // Now we need to see which value IDs have been changed.
    for (&pre_value_id, &condition_value_id) in pre_condition_stack
        .iter()
        .zip(&*stack)
        .filter(|(a, b)| a != b)
    {
        {
            trace!(
                ?condition_value_id,
                ?pre_value_id,
                "defining merges for While condition"
            );

            condition_merges.push(WhileMerge {
                pre_value: pre_value_id,
                condition_value: condition_value_id,
            });
        }
    }

    // Because the condition cannot change the stack state, we'll just restore to the pre-condition stack for the body.
    stack.clear();
    stack.extend_from_slice(&pre_condition_stack);

    // Now do the same, but with the body.
    super::super::analyze_block(
        ctx,
        stores,
        analyzer,
        pass_ctx,
        had_error,
        item_id,
        &while_op.body_block.block,
        stack,
        max_stack_depth,
    );

    // Again, the body cannot change the depth of the stack.
    if stack.len() != pre_condition_stack.len() {
        generate_stack_length_mismatch_diag(
            stores,
            op.token.location,
            while_op.tokens.end_token,
            stack.len(),
            pre_condition_stack.len(),
            Some("Loop body cannot change the depth or types on the stack".to_owned()),
        );

        had_error.set();

        // Pad the stack out to the expected length so the rest of the logict makes sense.
        for _ in 0..(pre_condition_stack.len()).saturating_sub(stack.len()) {
            stack.push(analyzer.new_value(op.token.location, None));
        }
    }

    let mut body_merges = SmallVec::new();
    for (&pre_value_id, &condition_value_id) in pre_condition_stack
        .iter()
        .zip(&*stack)
        .filter(|(a, b)| a != b)
    {
        trace!(
            ?condition_value_id,
            ?pre_value_id,
            "defining merge for While body"
        );

        body_merges.push(WhileMerge {
            pre_value: pre_value_id,
            condition_value: condition_value_id,
        });
    }

    // Need to revert the stack to before the loop executed.
    stack.clear();
    stack.extend_from_slice(&pre_condition_stack);

    analyzer.set_while_merges(
        op,
        WhileMerges {
            condition: condition_merges,
            body: body_merges,
        },
    );
    analyzer.set_op_io(op, &[condition_value], &[]);
    analyzer.consume_value(condition_value, op.id);
}
