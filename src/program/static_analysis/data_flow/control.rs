use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::NOps,
    opcode::{ConditionalBlock, Op},
    program::{static_analysis::Value, Procedure, ProcedureId, ProcedureKind, Program},
    source_file::{SourceLocation, SourceStorage},
    type_check::PorthTypeKind,
};

use super::super::{
    failed_compare_stack_types, generate_stack_length_mismatch_diag, generate_type_mismatch_diag,
    Analyzer, ConstVal, PtrId, ValueId,
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
    let expand_labels = |label_op: &Op, msg: &str| {
        let mut labels = vec![Label::new(label_op.token.location)
            .with_color(Color::Red)
            .with_message(msg)];

        for source in label_op.expansions.iter() {
            labels.push(
                Label::new(*source)
                    .with_color(Color::Blue)
                    .with_message("expanded from..."),
            );
        }

        labels
    };

    for &value_id in stack.lastn(proc.exit_stack().len()).unwrap_or(&*stack) {
        analyzer.consume(value_id, op.id);
    }

    if stack.len() != proc.exit_stack().len() {
        let mut labels = vec![
            Label::new(op.token.location)
                .with_color(Color::Red)
                .with_message("returning here"),
            Label::new(proc.exit_stack_location())
                .with_color(Color::Cyan)
                .with_message("return type defined here"),
        ];

        let stack_len = stack.len();
        stack.truncate(stack.len().saturating_sub(proc.exit_stack().len()));

        for &value_id in &**stack {
            let [value] = analyzer.get_values([value_id]);
            labels.push(
                Label::new(value.creator_token.location)
                    .with_color(Color::Green)
                    .with_message("value created here"),
            );
        }

        diagnostics::emit_error(
            op.token.location,
            format!(
                "function `{}` returns {} values, found {}",
                interner.resolve_lexeme(proc.name().lexeme),
                proc.exit_stack().len(),
                stack_len
            ),
            labels,
            None,
            source_store,
        );
        *had_error = true;

        return;
    }

    for (expected, actual_id) in proc.exit_stack().iter().zip(stack.iter()) {
        let [actual_value] = analyzer.get_values([*actual_id]);

        if expected.kind != actual_value.porth_type {
            let expected_kinds: Vec<_> = proc.exit_stack().iter().map(|t| t.kind).collect();

            failed_compare_stack_types(
                analyzer,
                source_store,
                stack,
                &expected_kinds,
                proc.exit_stack_location(),
                op.token.location,
                "procedure return stack mismatch",
            );
            *had_error = true;
            break;
        }
    }
    stack.truncate(stack.len().saturating_sub(proc.exit_stack().len()));
}

pub(super) fn prologue(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    op: &Op,
    proc: &Procedure,
) {
    let mut outputs = Vec::new();
    for input_type in proc.entry_stack() {
        let (new_id, _) = analyzer.new_value(input_type.kind, op.id, op.token);
        outputs.push(new_id);
        stack.push(new_id);
    }

    analyzer.set_io(op.id, op.token, &[], &outputs);
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
            let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Ptr, op.id, op.token);
            new_value.const_val = Some(ConstVal::Ptr {
                id: PtrId::Mem(proc_id),
                src_op_loc: op.token.location,
                offset: Some(0),
            });
            analyzer.set_io(op.id, op.token, &[], &[new_id]);

            stack.push(new_id);
        }
        _ => {
            let num_args = referenced_proc.entry_stack().len();
            let inputs = if stack.len() < num_args {
                generate_stack_length_mismatch_diag(
                    source_store,
                    op,
                    op.token.location,
                    stack.len(),
                    num_args,
                );
                *had_error = true;
                stack.clear();
                Vec::new()
            } else {
                let inputs = stack.split_off(stack.len() - num_args);

                let stacks = referenced_proc.entry_stack().iter().zip(&inputs);
                for (expected, actual_id) in stacks {
                    let [actual_value] = analyzer.get_values([*actual_id]);
                    if expected.kind != actual_value.porth_type {
                        let expected_kinds: Vec<_> = referenced_proc
                            .entry_stack()
                            .iter()
                            .map(|t| t.kind)
                            .collect();

                        failed_compare_stack_types(
                            analyzer,
                            source_store,
                            stack,
                            &expected_kinds,
                            referenced_proc.entry_stack_location(),
                            op.token.location,
                            "incorrect arguments for function",
                        );
                        *had_error = true;
                        break;
                    }
                }

                inputs
            };

            let mut outputs = Vec::new();

            for output in referenced_proc.exit_stack() {
                let (new_id, _) = analyzer.new_value(output.kind, op.id, op.token);
                outputs.push(new_id);
                stack.push(new_id);
            }

            analyzer.set_io(op.id, op.token, &inputs, &outputs);
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

    for &value_id in stack.lastn(num_args).unwrap_or(&*stack) {
        analyzer.consume(value_id, op.id);
    }

    // Only 7 arguments are support. Anything else will ICE.
    let mut args = [ValueId(usize::MAX); 7];

    let (inputs, new_type) = if stack.len() < num_args {
        generate_stack_length_mismatch_diag(
            source_store,
            op,
            op.token.location,
            stack.len(),
            num_args,
        );
        *had_error = true;
        stack.clear();
        (None, PorthTypeKind::Unknown)
    } else {
        let args = &mut args[..num_args];
        args.copy_from_slice(&stack[stack.len() - num_args..]);
        stack.truncate(stack.len() - num_args);
        (Some(args), PorthTypeKind::Int)
    };

    let (new_id, _) = analyzer.new_value(new_type, op.id, op.token);
    let inputs = inputs.map(|i| &*i).unwrap_or(&[]);
    analyzer.set_io(op.id, op.token, inputs, &[new_id]);
    stack.push(new_id);
}

fn check_stack_length_and_types(
    initial_stack: &[ValueId],
    stack: &[ValueId],
    op: &Op,
    sample_location: SourceLocation,
    msg: &str,
    had_error: &mut bool,
    source_store: &SourceStorage,
    analyzer: &mut Analyzer,
) {
    if stack.len() != initial_stack.len() {
        generate_stack_length_mismatch_diag(
            source_store,
            op,
            sample_location,
            stack.len(),
            initial_stack.len(),
        );
        *had_error = true;
    } else if !initial_stack.iter().zip(stack).all(|(expected, actual)| {
        let [expected_val, actual_val] = analyzer.get_values([*expected, *actual]);
        expected_val.porth_type == actual_val.porth_type
    }) {
        let expected_kinds: Vec<_> = initial_stack
            .iter()
            .map(|v| {
                let [v] = analyzer.get_values([*v]);
                v.porth_type
            })
            .collect();

        failed_compare_stack_types(
            analyzer,
            source_store,
            stack,
            &expected_kinds,
            op.token.location,
            sample_location,
            msg,
        );

        *had_error = true;
    }
}

fn make_non_const(analyzer: &mut Analyzer, initial_stack: &[ValueId], cur_stack: &[ValueId]) {
    for (&initial, &cur) in initial_stack.iter().zip(cur_stack).filter(|(a, b)| a != b) {
        let val = analyzer.value_mut(initial);
        val.const_val = None;
    }
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

    let last_value = analyzer.last_value_id();

    super::analyze_block(
        program,
        proc,
        &body.condition,
        analyzer,
        stack,
        last_value,
        had_error,
        interner,
        source_store,
    );

    if let Some(&value_id) = stack.last() {
        analyzer.consume(value_id, op.id);
    }

    let (do_input, const_val) = match stack.pop() {
        None => {
            generate_stack_length_mismatch_diag(source_store, op, body.do_token.location, 0, 1);
            *had_error = true;
            stack.clear();

            (None, None)
        }
        Some(val) => {
            let const_val = match analyzer.get_values([val]) {
                type_pattern!(a @ PorthTypeKind::Bool) => *a,
                [val] => {
                    // Type mismatch
                    *had_error = true;
                    if val.porth_type != PorthTypeKind::Unknown {
                        let lexeme = interner.resolve_lexeme(body.do_token.lexeme);
                        generate_type_mismatch_diag(source_store, lexeme, op, &[val]);
                    }
                    None
                }
            };

            (Some(val), const_val)
        }
    };

    check_stack_length_and_types(
        &initial_stack,
        stack,
        op,
        body.do_token.location,
        "while condition cannot change the length and types on the stack",
        had_error,
        source_store,
        analyzer,
    );

    // TODO: Mark all stack slots changed by the condition as non-const.
    // Ensure the stack is in the same state as before the condition.
    make_non_const(analyzer, &initial_stack, stack);
    stack.clear();
    stack.extend_from_slice(&initial_stack);

    super::analyze_block(
        program,
        proc,
        &body.block,
        analyzer,
        stack,
        last_value,
        had_error,
        interner,
        source_store,
    );

    check_stack_length_and_types(
        &initial_stack,
        stack,
        op,
        body.close_token.location,
        "while body cannot change the length and types on the stack",
        had_error,
        source_store,
        analyzer,
    );

    make_non_const(analyzer, &initial_stack, stack);
    stack.clear();
    stack.extend_from_slice(&initial_stack);
}
