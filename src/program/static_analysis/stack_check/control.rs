use std::cmp::Ordering;

use ariadne::{Color, Label};
use intcast::IntCast;
use smallvec::SmallVec;
use tracing::trace;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::Token,
    n_ops::SliceNOps,
    opcode::{If, Op, While},
    program::{
        static_analysis::{IfMerge, WhileMerge, WhileMerges},
        ItemId, ItemKind, ItemSignatureUnresolved, Program,
    },
    source_file::SourceStorage,
    type_store::TypeStore,
};

use super::{
    super::{generate_stack_length_mismatch_diag, Analyzer, ValueId},
    ensure_stack_depth,
};

pub fn epilogue_return(
    program: &Program,
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    item_id: ItemId,
) {
    let item = program.get_item_header(item_id);
    let item_sig = program.get_item_signature_resolved(item_id);
    let item_sig_tokens = program.get_item_signature_unresolved(item_id);

    if stack.len() != item_sig.exit_stack().len() {
        *had_error = true;

        let mut labels = vec![
            Label::new(op.token.location)
                .with_color(Color::Red)
                .with_message("returning here"),
            Label::new(item_sig_tokens.exit_stack_location())
                .with_color(Color::Cyan)
                .with_message("return type defined here"),
        ];

        match stack.len().cmp(&item_sig.exit_stack().len()) {
            Ordering::Less => {
                let num_missing = usize::saturating_sub(item_sig.exit_stack().len(), stack.len());
                for _ in 0..num_missing {
                    let pad_value = analyzer.new_value(op.token.location, None);
                    stack.push(pad_value);
                }
            }
            Ordering::Greater => {
                for &value_id in &stack[..stack.len() - item_sig.exit_stack().len()] {
                    let [value] = analyzer.values([value_id]);
                    labels.push(
                        Label::new(value.source_location)
                            .with_color(Color::Green)
                            .with_message("unused value created here"),
                    );
                }
            }
            Ordering::Equal => unreachable!(),
        }

        diagnostics::emit_error(
            op.token.location,
            format!(
                "function `{}` returns {} values, found {}",
                interner.resolve_lexeme(item.name().lexeme),
                item_sig.exit_stack().len(),
                stack.len()
            ),
            labels,
            None,
            source_store,
        );
    }

    let inputs = stack.lastn(item_sig.exit_stack().len()).unwrap();

    for &value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }

    analyzer.set_op_io(op, inputs, &[]);

    let len = inputs.len();
    stack.truncate(stack.len() - len);
}

pub fn prologue(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    op: &Op,
    item_sig: &ItemSignatureUnresolved,
) {
    let mut outputs = Vec::new();
    for (_, loc) in item_sig.entry_stack() {
        let new_id = analyzer.new_value(*loc, None);
        outputs.push(new_id);
        stack.push(new_id);
    }

    analyzer.set_op_io(op, &[], &outputs);
}

pub fn resolved_ident(
    program: &Program,
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    item: ItemId,
) {
    let referenced_item = program.get_item_header(item);
    let referenced_item_sig = program.get_item_signature_resolved(item);

    match referenced_item.kind() {
        ItemKind::Memory => {
            let new_id = analyzer.new_value(op.token.location, None);
            stack.push(new_id);
            analyzer.set_op_io(op, &[], &[new_id]);
        }
        _ => {
            // TODO: Maybe do a custom error here so we can point to the expected signature.
            ensure_stack_depth(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                referenced_item_sig.entry_stack().len(),
            );

            let inputs = stack.split_off(stack.len() - referenced_item_sig.entry_stack().len());
            for &value_id in &inputs {
                analyzer.consume_value(value_id, op.id);
            }
            let mut outputs = Vec::new();

            for _ in referenced_item_sig.exit_stack() {
                let new_id = analyzer.new_value(op.token.location, None);
                outputs.push(new_id);
                stack.push(new_id);
            }

            analyzer.set_op_io(op, &inputs, &outputs);
        }
    }
}

pub fn syscall(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    num_args: u8,
    arg_count_token: Token,
) {
    let num_args = num_args.to_usize();

    if !matches!(num_args, 1..=7) {
        diagnostics::emit_error(
            op.token.location,
            "invalid syscall size",
            [Label::new(arg_count_token.location)
                .with_color(Color::Red)
                .with_message("valid syscall sizes are 1..=7")],
            None,
            source_store,
        );
        *had_error = true;
        return;
    }

    ensure_stack_depth(analyzer, stack, source_store, had_error, op, num_args);

    let inputs = stack.split_off(stack.len() - num_args);
    for &value_id in &inputs {
        analyzer.consume_value(value_id, op.id);
    }

    let new_id = analyzer.new_value(op.token.location, None);
    analyzer.set_op_io(op, &inputs, &[new_id]);
    stack.push(new_id);
}

pub fn analyze_while(
    program: &Program,
    item_id: ItemId,
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
    had_error: &mut bool,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    op: &Op,
    while_op: &While,
    emit_traces: bool,
) {
    let initial_stack = stack.clone();

    // Evaluate the condition.
    super::super::analyze_block(
        program,
        item_id,
        &while_op.condition,
        stack,
        max_stack_depth,
        had_error,
        analyzer,
        interner,
        source_store,
        type_store,
        emit_traces,
    );

    // We expect there to be a boolean value on the top of the stack afterwards.
    // The condition cannot be allowed to otherwise change the depth of the stack as it could be
    // executed an arbitrary number of times.
    if stack.len() != initial_stack.len() + 1 {
        generate_stack_length_mismatch_diag(
            source_store,
            op.token.location,
            while_op.do_token.location,
            stack.len(),
            initial_stack.len(),
        );
        *had_error = true;

        // Pad the stack out to the expected length so the rest of the logic makes sense.
        for _ in 0..(initial_stack.len() + 1).saturating_sub(stack.len()) {
            stack.push(analyzer.new_value(op.token.location, None));
        }
    }
    let condition_value = stack.pop().unwrap();

    // Might need something smarter than this for the codegen.
    let mut condition_merges = SmallVec::new();

    // Now we need to see which value IDs have been changed, so the codegen phase will know
    // where to merge the new data.
    for (&pre_value, &condition_value) in initial_stack.iter().zip(&*stack).filter(|(a, b)| a != b)
    {
        trace!(
            ?condition_value,
            ?pre_value,
            "defining merge for WHILE-condition"
        );

        condition_merges.push(WhileMerge {
            pre_value,
            condition_value,
        });
    }

    // Because the condition cannot change the stack state, we'll just restore to the initial stap for the body.
    stack.clear();
    stack.extend_from_slice(&initial_stack);

    // Now we do the same thing as above, but with the body.
    super::super::analyze_block(
        program,
        item_id,
        &while_op.body_block,
        stack,
        max_stack_depth,
        had_error,
        analyzer,
        interner,
        source_store,
        type_store,
        emit_traces,
    );

    // Again, the body cannot change the depth of the stack.
    if stack.len() != initial_stack.len() {
        generate_stack_length_mismatch_diag(
            source_store,
            op.token.location,
            while_op.end_token.location,
            stack.len(),
            initial_stack.len(),
        );
        *had_error = true;
        // Pad the stack out to the expected length so the rest of the logic makes sense.
        for _ in 0..initial_stack.len().saturating_sub(stack.len()) {
            stack.push(analyzer.new_value(op.token.location, None));
        }
    }

    let mut body_merges = SmallVec::new();

    // Again, we need to see which value IDs have been changed, so the codegen phase will know
    // where to merge the new data.
    for (&pre_value, &condition_value) in initial_stack.iter().zip(&*stack).filter(|(a, b)| a != b)
    {
        trace!(
            ?condition_value,
            ?pre_value,
            "defining merge for WHILE-body"
        );

        body_merges.push(WhileMerge {
            pre_value,
            condition_value,
        });
    }

    // Need to revert the stack to before the loop executed.
    stack.clear();
    stack.extend_from_slice(&initial_stack);

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

pub fn analyze_if(
    program: &Program,
    item_id: ItemId,
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
    had_error: &mut bool,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    op: &Op,
    if_op: &If,
    emit_traces: bool,
) {
    let mut condition_values = Vec::new();

    // Evaluate condition.
    super::super::analyze_block(
        program,
        item_id,
        &if_op.condition,
        stack,
        max_stack_depth,
        had_error,
        analyzer,
        interner,
        source_store,
        type_store,
        emit_traces,
    );

    // We expect there to be a boolean value on the top of the stack afterwards.
    if stack.is_empty() {
        generate_stack_length_mismatch_diag(
            source_store,
            if_op.do_token.location,
            if_op.do_token.location,
            stack.len(),
            1,
        );
        *had_error = true;

        // Pad the stack out to the expected length so the rest of the logic makes sense.
        stack.push(analyzer.new_value(op.token.location, None));
    }
    condition_values.push(stack.pop().unwrap());

    let initial_stack = stack.clone();

    // Now we can do the then-block.
    super::super::analyze_block(
        program,
        item_id,
        &if_op.then_block,
        stack,
        max_stack_depth,
        had_error,
        analyzer,
        interner,
        source_store,
        type_store,
        emit_traces,
    );

    // We always have an else block, so save our current stack state for comparison.
    let then_block_stack = stack.clone();
    let then_block_sample_location = if_op.else_token.location;

    // And restore our stack back to the initial stack.
    stack.clear();
    stack.extend_from_slice(&initial_stack);

    // Now analyze the else block.
    super::super::analyze_block(
        program,
        item_id,
        &if_op.else_block,
        stack,
        max_stack_depth,
        had_error,
        analyzer,
        interner,
        source_store,
        type_store,
        emit_traces,
    );

    let mut body_merges = Vec::new();

    if if_op.is_then_terminal && if_op.is_else_terminal {
        // Both are terminal, nothing to do here.
        trace!("both branches terminate");
    } else if if_op.is_then_terminal {
        // We only need to "merge" for the else block. Which I think means we don't need to define
        // any merges at all. I think we can just leave our stack as whatever the else-block left it at.
        trace!("then-branch terminates, leaving stack as else-branch resulted");
    } else if if_op.is_else_terminal {
        // And in this case, we restore the stack to what the then-branch left it as.
        stack.clear();
        stack.extend_from_slice(&then_block_stack);
    } else {
        // Neither diverge, so we need to do some checking.
        if stack.len() != then_block_stack.len() {
            generate_stack_length_mismatch_diag(
                source_store,
                then_block_sample_location,
                if_op.end_token.location,
                stack.len(),
                then_block_stack.len(),
            );
            *had_error = true;
        }

        for (&then_value, else_value) in then_block_stack.iter().zip(stack).filter(|(a, b)| a != b)
        {
            let output_value = analyzer.new_value(op.token.location, None);
            trace!(
                ?then_value,
                ?else_value,
                ?output_value,
                "defining merge for IF"
            );

            body_merges.push(IfMerge {
                then_value,
                else_value: *else_value,
                output_value,
            });
            *else_value = output_value;
        }
    }

    analyzer.set_op_io(op, &condition_values, &[]);
    analyzer.set_if_merges(op, body_merges);
}
