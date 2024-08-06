use std::cmp::Ordering;

use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;
use tracing::trace;

use crate::{
    diagnostics::{self, build_creator_label_chain},
    error_signal::ErrorSignal,
    ir::{If, While},
    n_ops::SliceNOps,
    pass_manager::{static_analysis::generate_stack_length_mismatch_diag, PassManager},
    stores::{
        item::ItemId,
        ops::OpId,
        signatures::StackDefItemUnresolved,
        source::Spanned,
        values::{IfMerge, ValueId, WhileMerge, WhileMerges},
    },
    Stores,
};

use super::ensure_stack_depth;

pub(crate) fn epilogue_return(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op_id: OpId,
    item_id: ItemId,
) {
    let item_header = stores.items.get_item_header(item_id);
    let item_sig = stores.sigs.urir.get_item_signature(item_id);

    let exit_sig = &item_sig.exit.inner;
    if stack.len() != exit_sig.len() {
        let op_loc = stores.ops.get_token(op_id).location;

        let mut labels = vec![
            Label::new(op_loc)
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
                    let pad_value = stores.values.new_value(op_loc, None);
                    stack.push(pad_value);
                }
            }
            Ordering::Greater => {
                let unused_values = stack[..stack.len() - exit_sig.len()]
                    .iter()
                    .zip(0..)
                    .map(|(&id, idx)| (id, idx, "unused value"));
                let unused_value_labels =
                    build_creator_label_chain(stores, unused_values, Color::Green, Color::Cyan);
                labels.extend(unused_value_labels);
            }
            Ordering::Equal => unreachable!(),
        }

        diagnostics::emit_error(
            stores,
            op_loc,
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
        stores.values.consume_value(value_id, op_id);
    }
    stores.ops.set_op_io(op_id, inputs, &[]);
    let len = inputs.len();
    stack.truncate(stack.len() - len);
}

pub(crate) fn prologue(
    stores: &mut Stores,
    stack: &mut Vec<ValueId>,
    op_id: OpId,
    item_id: ItemId,
) {
    let mut outputs = SmallVec::<[_; 8]>::new();
    let sig = stores.sigs.urir.get_item_signature(item_id);

    for arg in &sig.entry.inner {
        let (StackDefItemUnresolved::Stack(kind) | StackDefItemUnresolved::Var { kind, .. }) = arg;

        let new_id = stores.values.new_value(kind.location, None);
        outputs.push(new_id);

        // We only push stack args to the stack. Vars get put into implicitly declared variables during codegen.
        if let StackDefItemUnresolved::Stack(_) = arg {
            stack.push(new_id);
        }
    }

    stores.ops.set_op_io(op_id, &[], &outputs);
}

pub(crate) fn syscall(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op_id: OpId,
    num_args: Spanned<u8>,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    if !matches!(num_args.inner, 1..=7) {
        diagnostics::emit_error(
            stores,
            op_loc,
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
    ensure_stack_depth(stores, had_error, stack, op_id, num_args);

    let inputs = stack.split_off(stack.len() - num_args);
    for &value_id in &inputs {
        stores.values.consume_value(value_id, op_id);
    }

    let new_id = stores.values.new_value(op_loc, None);
    stores.ops.set_op_io(op_id, &inputs, &[new_id]);
    stack.push(new_id);
}

pub(crate) fn call_function_const(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    stack: &mut Vec<ValueId>,
    op_id: OpId,
    callee_id: ItemId,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    let callee_sig = stores.sigs.urir.get_item_signature(callee_id);
    let entry_arg_count = callee_sig.entry.inner.len();

    if stack.len() < entry_arg_count {
        diagnostics::emit_error(
            stores,
            op_loc,
            format!(
                "procedure takes {entry_arg_count} arguments, found {}",
                stack.len()
            ),
            [
                Label::new(op_loc).with_color(Color::Red),
                Label::new(callee_sig.entry.location)
                    .with_color(Color::Cyan)
                    .with_message("signature defined here"),
            ],
            None,
        );
        had_error.set();

        let num_missing = usize::saturating_sub(entry_arg_count, stack.len());
        for _ in 0..num_missing {
            let pad_value = stores.values.new_value(op_loc, None);
            stack.push(pad_value);
        }
    }

    let inputs: SmallVec<[_; 8]> = stack.drain(stack.len() - entry_arg_count..).collect();
    for &value_id in &inputs {
        stores.values.consume_value(value_id, op_id);
    }

    let mut outputs = SmallVec::<[_; 8]>::new();
    for _ in &callee_sig.exit.inner {
        let new_id = stores.values.new_value(op_loc, None);
        outputs.push(new_id);
        stack.push(new_id);
    }

    stores.ops.set_op_io(op_id, &inputs, &outputs);
}

pub(crate) fn analyze_if(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
    op_id: OpId,
    if_op: &If,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    let mut condition_values = SmallVec::<[_; 1]>::new();

    // Evaluate condition.
    super::super::analyze_block(
        stores,
        pass_manager,
        had_error,
        item_id,
        if_op.condition,
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
        stack.push(stores.values.new_value(op_loc, None));
    }
    condition_values.push(stack.pop().unwrap());
    let initial_stack: SmallVec<[_; 20]> = stack.iter().copied().collect();

    // Now we can do the then-block
    super::super::analyze_block(
        stores,
        pass_manager,
        had_error,
        item_id,
        if_op.then_block,
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
        stores,
        pass_manager,
        had_error,
        item_id,
        if_op.else_block,
        stack,
        max_stack_depth,
    );

    let mut body_merges = Vec::new();

    let else_terminal = stores.blocks.is_terminal(if_op.else_block);
    let then_terminal = stores.blocks.is_terminal(if_op.then_block);
    if else_terminal && then_terminal {
        // Both are terminal, so we don't need to do any checking.
        trace!("both branches terminate");
    } else if then_terminal {
        // We only need to "merge" for the else block, so we can just take the result of the else block as
        // the stack state.
        trace!("then-branch terminates, leaving stack as else-branch resulted");
    } else if else_terminal {
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
            let output_value_id = stores.values.new_value(op_loc, None);
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

    stores.ops.set_op_io(op_id, &condition_values, &[]);
    stores.values.set_if_merges(op_id, body_merges);
}

pub(crate) fn analyze_while(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
    op_id: OpId,
    while_op: &While,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    let pre_condition_stack: SmallVec<[_; 20]> = stack.iter().copied().collect();

    // Evaluate the condition.
    super::super::analyze_block(
        stores,
        pass_manager,
        had_error,
        item_id,
        while_op.condition,
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
        stack.push(stores.values.new_value(op_loc, None));
    }
    let condition_value = stack.pop().unwrap();

    // The condition cannot be allowed to otherwise change the depth of the stack, as it could be
    // executed an arbitrary number of times.
    // TODO: Allow the condition to alter the stack, as long as the body restores it.
    if stack.len() != pre_condition_stack.len() {
        generate_stack_length_mismatch_diag(
            stores,
            op_loc,
            while_op.tokens.do_token,
            stack.len(),
            pre_condition_stack.len(),
            None,
        );

        had_error.set();

        // Pad the stack out to the expected length so the rest of the logict makes sense.
        for _ in 0..(pre_condition_stack.len()).saturating_sub(stack.len()) {
            stack.push(stores.values.new_value(op_loc, None));
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
        stores,
        pass_manager,
        had_error,
        item_id,
        while_op.body_block,
        stack,
        max_stack_depth,
    );

    // Again, the body cannot change the depth of the stack.
    if stack.len() != pre_condition_stack.len() {
        generate_stack_length_mismatch_diag(
            stores,
            op_loc,
            while_op.tokens.end_token,
            stack.len(),
            pre_condition_stack.len(),
            Some("Loop body cannot change the depth or types on the stack".to_owned()),
        );

        had_error.set();

        // Pad the stack out to the expected length so the rest of the logict makes sense.
        for _ in 0..(pre_condition_stack.len()).saturating_sub(stack.len()) {
            stack.push(stores.values.new_value(op_loc, None));
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

    stores.values.set_while_merges(
        op_id,
        WhileMerges {
            condition: condition_merges,
            body: body_merges,
        },
    );
    stores.ops.set_op_io(op_id, &[condition_value], &[]);
    stores.values.consume_value(condition_value, op_id);
}
