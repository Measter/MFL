use ariadne::{Color, Label};

use crate::{
    diagnostics,
    n_ops::NOps,
    opcode::{Op, OpCode},
    program::{Procedure, ProcedureId, ProcedureKind, Program},
    source_file::SourceStorage,
    type_check::PorthTypeKind,
};

use super::{
    failed_compare_stack_types, generate_stack_exhaustion_diag, Analyzer, ConstVal, PtrId, ValueId,
};

pub(super) fn epilogue_return(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op_idx: usize,
    op: &Op,
    proc: &Procedure,
) {
    // The epilogue points to the procedure name, but we want the diagnostic
    // to point at the last token.
    let cur_op = if op.code == OpCode::Epilogue {
        &proc.body()[proc.body().len() - 2]
    } else {
        op
    };

    let make_labels = || {
        let mut labels = vec![Label::new(cur_op.token.location)
            .with_color(Color::Red)
            .with_message("here")];

        for source in cur_op.expansions.iter() {
            labels.push(
                Label::new(*source)
                    .with_color(Color::Blue)
                    .with_message("expanded from..."),
            );
        }

        labels
    };

    for &value_id in stack.lastn(proc.exit_stack().len()).unwrap_or(&*stack) {
        analyzer.consume(value_id, op_idx);
    }

    if stack.len() != proc.exit_stack().len() {
        diagnostics::emit_error(
            cur_op.token.location,
            format!(
                "expected {} values on stack, found {}",
                proc.exit_stack().len(),
                stack.len()
            ),
            make_labels(),
            None,
            source_store,
        );
        *had_error = true;

        stack.truncate(stack.len().saturating_sub(proc.exit_stack().len()));
        return;
    }

    for (expected, actual_id) in proc.exit_stack().iter().zip(stack.iter()) {
        let [actual_value] = analyzer.get_values([*actual_id]);

        if expected.kind != actual_value.porth_type {
            failed_compare_stack_types(
                analyzer,
                source_store,
                stack,
                proc.exit_stack(),
                cur_op,
                proc.name,
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
    op_idx: usize,
    op: &Op,
    proc: &Procedure,
) {
    let mut outputs = Vec::new();
    for input_type in proc.entry_stack() {
        let (new_id, _) = analyzer.new_value(input_type.kind, op_idx, op.token);
        outputs.push(new_id);
        stack.push(new_id);
    }

    analyzer.set_io(op_idx, op.token, &[], &outputs);
}

pub(super) fn resolved_ident(
    program: &Program,
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op_idx: usize,
    op: &Op,
    proc_id: ProcedureId,
) {
    let referenced_proc = program.get_proc(proc_id);

    match referenced_proc.kind() {
        ProcedureKind::Memory => {
            let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Ptr, op_idx, op.token);
            new_value.const_val = Some(ConstVal::Ptr {
                id: PtrId::Mem(proc_id),
                src_op_loc: op.token.location,
                offset: Some(0),
            });
            analyzer.set_io(op_idx, op.token, &[], &[new_id]);

            stack.push(new_id);
        }
        _ => {
            let num_args = referenced_proc.entry_stack().len();
            let inputs = if stack.len() < num_args {
                generate_stack_exhaustion_diag(source_store, op, stack.len(), num_args);
                *had_error = true;
                stack.clear();
                Vec::new()
            } else {
                let inputs = stack.split_off(stack.len() - num_args);

                let stacks = referenced_proc.entry_stack().iter().zip(&inputs);
                for (expected, actual_id) in stacks {
                    let [actual_value] = analyzer.get_values([*actual_id]);
                    if expected.kind != actual_value.porth_type {
                        failed_compare_stack_types(
                            analyzer,
                            source_store,
                            stack,
                            referenced_proc.entry_stack(),
                            op,
                            op.token,
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
                let (new_id, _) = analyzer.new_value(output.kind, op_idx, op.token);
                outputs.push(new_id);
                stack.push(new_id);
            }

            analyzer.set_io(op_idx, op.token, &inputs, &outputs);
        }
    }
}

pub(super) fn syscall(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op_idx: usize,
    op: &Op,
    mut num_args: usize,
) {
    // Also need the syscall ID.
    // TODO: This is dumb. Make this not be dumb.
    num_args += 1;

    for &value_id in stack.lastn(num_args).unwrap_or(&*stack) {
        analyzer.consume(value_id, op_idx);
    }

    // Only 7 arguments are support. Anything else will ICE.
    let mut args = [ValueId(usize::MAX); 7];

    let (inputs, new_type) = if stack.len() < num_args {
        generate_stack_exhaustion_diag(source_store, op, stack.len(), num_args);
        *had_error = true;
        stack.clear();
        (None, PorthTypeKind::Unknown)
    } else {
        let args = &mut args[..num_args];
        args.copy_from_slice(&stack[stack.len() - num_args..]);
        stack.truncate(stack.len() - num_args);
        (Some(args), PorthTypeKind::Int)
    };

    let (new_id, _) = analyzer.new_value(new_type, op_idx, op.token);
    let inputs = inputs.map(|i| &*i).unwrap_or(&[]);
    analyzer.set_io(op_idx, op.token, inputs, &[new_id]);
    stack.push(new_id);
}
