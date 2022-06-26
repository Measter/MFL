use std::cmp::Ordering;

use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{ConditionalBlock, Op},
    program::{
        static_analysis::{MergeBlock, MergeInfo, MergePair},
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
) {
    todo!()
}
