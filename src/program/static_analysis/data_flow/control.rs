use std::cmp::Ordering;

use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    lexer::Token,
    n_ops::SliceNOps,
    opcode::{ConditionalBlock, Op},
    program::{
        static_analysis::{IfMerges, MergeBlock, MergeInfo, MergePair},
        Procedure, ProcedureId, ProcedureKind, Program,
    },
    source_file::SourceStorage,
};

use super::{
    super::{generate_stack_length_mismatch_diag, Analyzer, ValueId},
    ensure_stack_depth,
};

pub(super) fn epilogue_return(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    proc: &Procedure,
) {
    if stack.len() != proc.exit_stack().len() {
        *had_error = true;

        let mut labels = vec![
            Label::new(op.token.location)
                .with_color(Color::Red)
                .with_message("returning here"),
            Label::new(proc.exit_stack_location())
                .with_color(Color::Cyan)
                .with_message("return type defined here"),
        ];

        match stack.len().cmp(&proc.exit_stack().len()) {
            Ordering::Less => {
                let num_missing = usize::saturating_sub(proc.exit_stack().len(), stack.len());
                for _ in 0..num_missing {
                    let pad_value = analyzer.new_value(op);
                    stack.push(pad_value);
                }
            }
            Ordering::Greater => {
                for &value_id in &stack[..stack.len() - proc.exit_stack().len()] {
                    let [value] = analyzer.values([value_id]);
                    labels.push(
                        Label::new(value.creator_token.location)
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
                interner.resolve_lexeme(proc.name().lexeme),
                proc.exit_stack().len(),
                stack.len()
            ),
            labels,
            None,
            source_store,
        );
    }

    let inputs = stack.lastn(proc.exit_stack().len()).unwrap();

    for &value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }

    analyzer.set_op_io(op, inputs, &[]);
}

pub(super) fn prologue(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    op: &Op,
    proc: &Procedure,
) {
    let mut outputs = Vec::new();
    for _ in proc.entry_stack() {
        let new_id = analyzer.new_value(op);
        outputs.push(new_id);
        stack.push(new_id);
    }

    analyzer.set_op_io(op, &[], &outputs);
}

pub(super) fn resolved_ident(
    program: &Program,
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    proc_id: ProcedureId,
) {
    let referenced_proc = program.get_proc(proc_id);

    match referenced_proc.kind() {
        ProcedureKind::Memory => {
            let new_id = analyzer.new_value(op);
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
                referenced_proc.entry_stack().len(),
            );

            let inputs = stack.split_off(stack.len() - referenced_proc.entry_stack().len());
            for &value_id in &inputs {
                analyzer.consume_value(value_id, op.id);
            }
            let mut outputs = Vec::new();

            for _ in referenced_proc.exit_stack() {
                let new_id = analyzer.new_value(op);
                outputs.push(new_id);
                stack.push(new_id);
            }

            analyzer.set_op_io(op, &inputs, &outputs);
        }
    }
}

pub(super) fn syscall(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    mut num_args: usize,
) {
    // Also need the syscall ID.
    // TODO: This is dumb. Make this not be dumb.
    num_args += 1;

    ensure_stack_depth(analyzer, stack, source_store, had_error, op, num_args);

    let inputs = stack.split_off(stack.len() - num_args);
    for &value_id in &inputs {
        analyzer.consume_value(value_id, op.id);
    }

    let new_id = analyzer.new_value(op);
    analyzer.set_op_io(op, &inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn analyze_while(
    program: &Program,
    proc: &Procedure,
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    op: &Op,
    body: &ConditionalBlock,
) {
    let initial_stack = stack.clone();

    // Evaluate the condition.
    super::analyze_block(
        program,
        proc,
        &body.condition,
        analyzer,
        stack,
        had_error,
        interner,
        source_store,
    );

    // We expect there to be a boolean value on the top of the stack afterwards.
    // The condition cannot be allowed to otherwise change the depth of the stack as it could be
    // executed an arbitrary number of times.
    if stack.len() != initial_stack.len() + 1 {
        generate_stack_length_mismatch_diag(
            source_store,
            op.token.location,
            body.do_token.location,
            stack.len(),
            initial_stack.len(),
        );
        *had_error = true;

        // Pad the stack out to the expected length so the rest of the logic makes sense.
        for _ in 0..(initial_stack.len() + 1).saturating_sub(stack.len()) {
            stack.push(analyzer.new_value(op));
        }
    }
    let condition_value = stack.pop().unwrap();

    // Might need something smarter than this for the codegen.
    let mut condition_merges = Vec::new();

    // Now we need to see which value IDs have been changed, so the codegen phase will know
    // where to merge the new data.
    for (&old_value_id, new_value_id) in initial_stack.iter().zip(&*stack).filter(|(a, b)| a != b) {
        condition_merges.push(MergePair {
            src: *new_value_id,
            dst: old_value_id,
        });
        let [new_value] = analyzer.values_mut([new_value_id]);
    }

    // Restore the stack to the initial stack, so we can evaluate the body with a clean slate.
    // This allows us to know which values should be merged with.
    stack.clear();
    stack.extend_from_slice(&initial_stack);

    // Now we do the same thing as above, but with the body.
    super::analyze_block(
        program,
        proc,
        &body.block,
        analyzer,
        stack,
        had_error,
        interner,
        source_store,
    );

    // In this case, we do not expect any new values, only that the stack has the same depth.
    // Might be worth having a custom error here.
    if stack.len() != initial_stack.len() {
        generate_stack_length_mismatch_diag(
            source_store,
            op.token.location,
            body.close_token.location,
            stack.len(),
            initial_stack.len(),
        );
        *had_error = true;
        // Pad the stack out to the expected length so the rest of the logic makes sense.
        for _ in 0..initial_stack.len().saturating_sub(stack.len()) {
            stack.push(analyzer.new_value(op));
        }
    }

    let mut body_merges = Vec::new();

    // Again, we need to see which value IDs have been changed, so the codegen phase will know
    // where to merge the new data.
    for (&old_value_id, new_value_id) in initial_stack.iter().zip(&*stack).filter(|(a, b)| a != b) {
        body_merges.push(MergePair {
            src: *new_value_id,
            dst: old_value_id,
        });
        let [new_value] = analyzer.values_mut([new_value_id]);
    }

    analyzer.set_op_merges(
        op,
        MergeInfo::While(MergeBlock {
            condition_merges,
            body_merges,
        }),
    );
    analyzer.set_op_io(op, &[condition_value], &[]);
    analyzer.consume_value(condition_value, op.id);

    // Now restore the stack a second time so the rest of the proc can pretend the while block
    // changed anything.
    *stack = initial_stack;
}

pub(super) fn analyze_if(
    program: &Program,
    proc: &Procedure,
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    op: &Op,
    main: &ConditionalBlock,
    elif_blocks: &[ConditionalBlock],
    else_block: Option<&[Op]>,
    open_token: Token,
    close_token: Token,
) {
    // We'll go with a simpler validity check:
    // * If there's a single condition (no elifs) then the condition may change the stack.
    // * If there's an else block, then the bodies may change the stack.

    let mut initial_stack = stack.clone();
    let mut initial_stack_sample_location = open_token.location;
    let mut output_stack = stack.clone();
    let mut output_stack_sample_location = open_token.location;

    let mut condition_values = Vec::new();

    // Evaluate main condition.
    super::analyze_block(
        program,
        proc,
        &main.condition,
        analyzer,
        stack,
        had_error,
        interner,
        source_store,
    );

    // We expect there to be a boolean value on the top of the stack afterwards.
    // The length we expected depends on whether we have elifs or not, as a block with
    // no elifs can have it's main condition change the stack.
    let expected_len = if elif_blocks.is_empty() {
        1
    } else {
        initial_stack.len() + 1
    };
    if (elif_blocks.is_empty() && stack.is_empty())
        || (!elif_blocks.is_empty() && stack.len() != expected_len)
    {
        generate_stack_length_mismatch_diag(
            source_store,
            main.do_token.location,
            main.do_token.location,
            stack.len(),
            expected_len,
        );
        *had_error = true;

        // Pad the stack out to the expected length so the rest of the logic makes sense.
        for _ in 0..expected_len.saturating_sub(stack.len()) {
            stack.push(analyzer.new_value(op));
        }
    }
    condition_values.push(stack.pop().unwrap());

    let mut main_condition_merges = Vec::new();

    // If there are no elifs, then we can allow the stack to be changed.
    if elif_blocks.is_empty() {
        initial_stack.clear();
        initial_stack.extend_from_slice(stack);
        initial_stack_sample_location = main.do_token.location;
        output_stack.clear();
        output_stack.extend_from_slice(stack);
        output_stack_sample_location = main.do_token.location;
    } else {
        // We need to see which IDs have been changed, so we know which are non-const and which
        // values need to be merged.
        for (&old_value_id, &new_value_id) in
            initial_stack.iter().zip(&*stack).filter(|(a, b)| a != b)
        {
            main_condition_merges.push(MergePair {
                src: new_value_id,
                dst: old_value_id,
            })
        }

        // Restore the stack to the initial stack so the bady can be evaluated with a clean slate.
        stack.clear();
        stack.extend_from_slice(&initial_stack);
    }

    // Now we can do the main body.
    super::analyze_block(
        program,
        proc,
        &main.block,
        analyzer,
        stack,
        had_error,
        interner,
        source_store,
    );

    let mut main_body_merges = Vec::new();
    // If we have an else block, then we're allowed to changed the expected output stack, otherwise
    // we must assert that the depth is unchanged.
    // Additionally, we only need to set the merges if we cannot change it.
    if else_block.is_some() {
        output_stack = stack.clone();
        output_stack_sample_location = main.close_token.location;
    } else {
        if stack.len() != output_stack.len() {
            generate_stack_length_mismatch_diag(
                source_store,
                output_stack_sample_location,
                main.close_token.location,
                stack.len(),
                output_stack.len(),
            );
            *had_error = true;
        }

        // Now we need to see which value IDs have been changed, so the codegen phase will know
        // where to merge the new data.
        for (&old_value_id, &new_value_id) in
            initial_stack.iter().zip(&*stack).filter(|(a, b)| a != b)
        {
            main_body_merges.push(MergePair {
                src: new_value_id,
                dst: old_value_id,
            });
        }
    }

    let main_merges = MergeBlock {
        condition_merges: main_condition_merges,
        body_merges: main_body_merges,
    };

    // And restore our stack back to the initial stack.
    stack.clear();
    stack.extend_from_slice(&initial_stack);

    let mut elif_merges = Vec::new();

    for elif_block in elif_blocks {
        super::analyze_block(
            program,
            proc,
            &elif_block.condition,
            analyzer,
            stack,
            had_error,
            interner,
            source_store,
        );

        if stack.len() != initial_stack.len() + 1 {
            generate_stack_length_mismatch_diag(
                source_store,
                initial_stack_sample_location,
                elif_block.do_token.location,
                stack.len(),
                initial_stack.len() + 1,
            );
            *had_error = true;
            // Create a value for the condition boolean.
            analyzer.new_value(op);
        }

        condition_values.push(stack.pop().unwrap());

        let mut elif_condition_merges = Vec::new();
        for (&old_value_id, &new_value_id) in
            initial_stack.iter().zip(&*stack).filter(|(a, b)| a != b)
        {
            elif_condition_merges.push(MergePair {
                src: new_value_id,
                dst: old_value_id,
            });
        }

        // Restore the stack.
        stack.clear();
        stack.extend_from_slice(&initial_stack);

        super::analyze_block(
            program,
            proc,
            &elif_block.block,
            analyzer,
            stack,
            had_error,
            interner,
            source_store,
        );

        if stack.len() != output_stack.len() {
            generate_stack_length_mismatch_diag(
                source_store,
                output_stack_sample_location,
                elif_block.close_token.location,
                stack.len(),
                output_stack.len(),
            );
            *had_error = true;
        }

        let mut elif_body_merges = Vec::new();
        for (&old_value_id, &new_value_id) in
            output_stack.iter().zip(&*stack).filter(|(a, b)| a != b)
        {
            elif_body_merges.push(MergePair {
                src: new_value_id,
                dst: old_value_id,
            });
        }

        // Restore to the initial stack for the next elif.
        stack.clear();
        stack.extend_from_slice(&initial_stack);

        elif_merges.push(MergeBlock {
            condition_merges: elif_condition_merges,
            body_merges: elif_body_merges,
        });
    }

    let mut else_merges = Vec::new();
    if let Some(else_block) = else_block {
        super::analyze_block(
            program,
            proc,
            else_block,
            analyzer,
            stack,
            had_error,
            interner,
            source_store,
        );

        if stack.len() != output_stack.len() {
            generate_stack_length_mismatch_diag(
                source_store,
                output_stack_sample_location,
                close_token.location,
                stack.len(),
                output_stack.len(),
            );
            *had_error = true;
        }

        for (&old_value_id, &new_value_id) in
            output_stack.iter().zip(&*stack).filter(|(a, b)| a != b)
        {
            else_merges.push(MergePair {
                src: new_value_id,
                dst: old_value_id,
            });
        }
    }

    analyzer.set_op_io(op, &condition_values, &[]);
    analyzer.set_op_merges(
        op,
        MergeInfo::If(IfMerges {
            main: main_merges,
            elifs: elif_merges,
            else_block: MergeBlock {
                condition_merges: Vec::new(),
                body_merges: else_merges,
            },
        }),
    );
}
