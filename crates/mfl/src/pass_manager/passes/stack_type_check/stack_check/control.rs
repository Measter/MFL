use std::cmp::Ordering;

use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;
use stores::{items::ItemId, source::Spanned};
use tracing::trace;

use crate::{
    diagnostics::{self, build_creator_label_chain},
    error_signal::ErrorSignal,
    ir::{Basic, Cond, Control, OpCode, While},
    n_ops::SliceNOps,
    pass_manager::{static_analysis::generate_stack_length_mismatch_diag, PassManager},
    stores::{
        block::BlockId,
        ops::OpId,
        signatures::StackDefItemUnresolved,
        values::{MergeValue, ValueId},
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

pub(crate) fn analyze_cond(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
    op_id: OpId,
    cond_op: &Cond,
) {
    let op_loc = stores.ops.get_token(op_id).location;
    let pre_cond_stack: SmallVec<[_; 20]> = stack.iter().copied().collect();
    let mut condition_values = SmallVec::<[_; 8]>::new();

    let mut arm_stacks = Vec::new();
    for arm in &cond_op.arms {
        // Evaluate condition.
        super::super::analyze_block(
            stores,
            pass_manager,
            had_error,
            item_id,
            arm.condition,
            stack,
            max_stack_depth,
        );

        // We expect there to be a boolean value on teh top of the stack afterwards.
        if stack.is_empty() {
            generate_stack_length_mismatch_diag(stores, arm.open, arm.open, stack.len(), 1, None);

            had_error.set();

            // Pad the stack out to the expected length so the rest of the logic makes sense.
            stack.push(stores.values.new_value(op_loc, None));
        }
        condition_values.push(stack.pop().unwrap());

        // Now we can do the then-block
        super::super::analyze_block(
            stores,
            pass_manager,
            had_error,
            item_id,
            arm.block,
            stack,
            max_stack_depth,
        );

        let condition_terminal = stores.blocks.is_terminal(arm.condition);
        let block_terminal = stores.blocks.is_terminal(arm.block);
        if !(condition_terminal | block_terminal) {
            trace!(?arm.condition, ?arm.block, "cond arm doesn't terminate");
            arm_stacks.push((arm.close, arm.block, stack.clone()));
        } else {
            trace!(?arm.condition, ?arm.block, "cond arm terminates");
        }

        // Restore our stack back to before the cond
        stack.clear();
        stack.extend_from_slice(&pre_cond_stack);
    }

    // Now we can do the else-block
    super::super::analyze_block(
        stores,
        pass_manager,
        had_error,
        item_id,
        cond_op.else_block,
        stack,
        max_stack_depth,
    );

    if !stores.blocks.is_terminal(cond_op.else_block) {
        trace!(?cond_op.else_block, "cond else doesn't terminate");
        arm_stacks.push((cond_op.else_close, cond_op.else_block, stack.clone()));
    } else {
        trace!(?cond_op.else_block, "cond else terminates");
    }

    let mut merge_values = Vec::new();
    match &*arm_stacks {
        [] => {} // All arms terminated.
        [(_, _, stk)] => {
            // Only one arm didn't terminate, so that's our stack.
            stack.clear();
            stack.extend_from_slice(stk);
        }
        [(first_arm_loc, first_arm_block_id, first_arm_stack), rest @ ..] => {
            let (expected_stack_loc, expected_block, expected_stack, stacks_to_check) =
                if cond_op.implicit_else {
                    let [rest @ .., else_stack] = &*arm_stacks else {
                        unreachable!()
                    };

                    (cond_op.token, else_stack.1, &*else_stack.2, rest)
                } else {
                    (
                        *first_arm_loc,
                        *first_arm_block_id,
                        &**first_arm_stack,
                        rest,
                    )
                };

            let mut same_length = true;
            // Length check
            for (arm_loc, _, arm_stack) in stacks_to_check {
                if arm_stack.len() != expected_stack.len() {
                    generate_stack_length_mismatch_diag(
                        stores,
                        expected_stack_loc,
                        *arm_loc,
                        arm_stack.len(),
                        expected_stack.len(),
                        None,
                    );
                    had_error.set();
                    same_length = false;
                }
            }

            if same_length {
                stack.clear();
                let expected_stack_iter = expected_stack.iter().copied();
                let mut to_check_iters = stacks_to_check
                    .iter()
                    .map(|(_, id, s)| (id, s.iter().copied()))
                    .collect::<Vec<_>>();

                for orig_value_id in expected_stack_iter {
                    let mut needs_merge = false;
                    let mut merge_value = MergeValue {
                        inputs: Vec::new(),
                        output: orig_value_id,
                    };

                    for (block_id, arm_values) in &mut to_check_iters {
                        let to_check_value = arm_values.next().unwrap(); // We know they're the same length.
                        if orig_value_id != to_check_value {
                            // If we found our first merge, create a new merge value and insert the expected input
                            // as an input.
                            if !needs_merge {
                                needs_merge = true;
                                merge_value.output = stores.values.new_value(cond_op.token, None);
                                merge_value.inputs.push((expected_block, orig_value_id));
                            }

                            merge_value.inputs.push((**block_id, to_check_value));
                        }
                    }

                    if needs_merge {
                        stack.push(merge_value.output);

                        // Sort the merge value inputs by block ID, so we know where the else block is
                        // for type checking.
                        merge_value.inputs.sort_by_key(|i| i.0);

                        merge_values.push(merge_value);
                    } else {
                        stack.push(orig_value_id);
                    }
                }
            }
        }
    }

    stores.ops.set_op_io(op_id, &condition_values, &[]);
    stores.values.set_merge_values(op_id, merge_values);
}

pub(crate) fn analyze_while(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    block_id: BlockId,
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
    let post_condition_stack: SmallVec<[_; 20]> = stack.iter().copied().collect();

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

    // The body must restore the stack to the length prior to the condition's execution.
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

    // Now we look for how the values on the stack have changed relative to the condition's execution,
    // and define merge values for the changes.
    let mut while_merges = Vec::new();
    for (&pre_condition_value_id, &post_body_value_id) in pre_condition_stack
        .iter()
        .zip(&*stack)
        .filter(|(a, b)| a != b)
    {
        let merged_value_id = stores.values.new_value(op_loc, None);
        trace!(
            ?pre_condition_value_id,
            ?post_body_value_id,
            ?merged_value_id,
            "defining merge for While"
        );

        while_merges.push(MergeValue {
            inputs: vec![
                (block_id, pre_condition_value_id),
                (while_op.body_block, post_body_value_id),
            ],
            output: merged_value_id,
        });
    }

    // Now we need to fix up ops in both the condition and the body to refer to merge values instead of pre-condition
    // values.
    fixup_op_input_values(stores, block_id, while_op.condition, &while_merges);
    fixup_op_input_values(stores, block_id, while_op.body_block, &while_merges);

    // Need to revert the stack to after the condition executed, but fixup merge values.
    stack.clear();
    for value_id in post_condition_stack {
        // Technically N^2, but the list should be small.
        if let Some(output_id) = while_merges
            .iter()
            .find(|m| m.block_input(block_id) == Some(value_id))
        {
            stack.push(output_id.output);
        } else {
            stack.push(value_id);
        }
    }

    // Also need to see if we need to fixup the condition value.
    let mut condition_value = condition_value;
    for merge in &while_merges {
        if merge.block_input(block_id) == Some(condition_value) {
            condition_value = merge.output;
            break;
        }
    }

    stores.values.set_merge_values(op_id, while_merges);
    stores.ops.set_op_io(op_id, &[condition_value], &[]);
    stores.values.consume_value(condition_value, op_id);
}

fn fixup_op_input_values(
    stores: &mut Stores,
    pre_cond_block_id: BlockId,
    fixup_block_id: BlockId,
    merges: &[MergeValue],
) {
    let block = stores.blocks.get_block(fixup_block_id).clone();
    for &op_id in &block.ops {
        let op_io = stores.ops.get_op_io(op_id);
        let mut new_op_inputs = SmallVec::<[ValueId; 8]>::new();
        let mut changed = false;

        for &input_value_id in &op_io.inputs {
            // Technically N^2, but the list should be small.
            if let Some(output_id) = merges
                .iter()
                .find(|m| m.block_input(pre_cond_block_id) == Some(input_value_id))
            {
                new_op_inputs.push(output_id.output);
                changed = true;
            } else {
                new_op_inputs.push(input_value_id);
            }
        }

        if changed {
            stores.ops.update_op_inputs(op_id, &new_op_inputs);
        }

        match stores.ops.get_type_resolved(op_id).clone() {
            OpCode::Basic(Basic::Control(Control::While(while_op))) => {
                fixup_merge_variables(stores, pre_cond_block_id, op_id, merges);

                fixup_op_input_values(stores, pre_cond_block_id, while_op.condition, merges);
                fixup_op_input_values(stores, pre_cond_block_id, while_op.body_block, merges);
            }
            OpCode::Basic(Basic::Control(Control::Cond(cond_op))) => {
                fixup_merge_variables(stores, pre_cond_block_id, op_id, merges);
                for arm in &cond_op.arms {
                    fixup_op_input_values(stores, pre_cond_block_id, arm.condition, merges);
                    fixup_op_input_values(stores, pre_cond_block_id, arm.block, merges);
                }
                fixup_op_input_values(stores, pre_cond_block_id, cond_op.else_block, merges);
            }
            _ => {}
        }
    }
}

fn fixup_merge_variables(
    stores: &mut Stores,
    pre_cond_block_id: BlockId,
    op_id: OpId,
    merges: &[MergeValue],
) {
    let old_merges = stores
        .values
        .get_merge_values(op_id)
        .expect("ICE: Tried to fixup merge values on a non-branching op");

    let mut new_merges = Vec::new();
    let mut changed = false;

    for mut old_merge in old_merges.iter().cloned() {
        // Technically N^2, but the list should be small.
        let mut this_changed = false;
        for outer_merge in merges {
            let Some(outer_id) = outer_merge.block_input(pre_cond_block_id) else {
                continue;
            };
            for (_, old_merge_id) in &mut old_merge.inputs {
                if outer_id == *old_merge_id {
                    this_changed = true;
                    *old_merge_id = outer_merge.output;
                }
            }
        }

        if this_changed {
            changed = true;
        }
        new_merges.push(old_merge);
    }

    if changed {
        stores.values.update_marge_values(op_id, new_merges);
    }
}
