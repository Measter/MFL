use ariadne::{Color, Label};

use crate::{
    diagnostics,
    n_ops::NOps,
    opcode::{Op, OpCode},
    program::Procedure,
    source_file::SourceStorage,
};

use super::{failed_compare_stack_types, Analyzer, ValueId};

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
                    .with_message("expended from..."),
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
