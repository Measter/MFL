use crate::{
    interners::Interners,
    opcode::{ConditionalBlock, Op},
    program::{
        static_analysis::{failed_compare_stack_types, Analyzer, PorthTypeKind},
        Procedure, ProcedureId, ProcedureKind, Program,
    },
    source_file::SourceStorage,
};

pub(super) fn epilogue_return(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    proc: &Procedure,
) {
    let op_data = analyzer.get_op_io(op.id);

    for (expected, actual_id) in proc.exit_stack().iter().zip(&op_data.inputs) {
        let actual_type = analyzer.value_types([*actual_id]);

        if actual_type != Some([expected.kind]) {
            let expected_kinds: Vec<_> = proc.exit_stack().iter().map(|t| t.kind).collect();

            failed_compare_stack_types(
                analyzer,
                source_store,
                &op_data.inputs,
                &expected_kinds,
                proc.exit_stack_location(),
                op.token.location,
                "procedure return stack mismatch",
            );
            *had_error = true;
            break;
        }
    }
}

pub(super) fn prologue(analyzer: &mut Analyzer, op: &Op, proc: &Procedure) {
    let op_data = analyzer.get_op_io(op.id);
    let outputs = op_data.outputs.clone();

    for (output_id, &output_type) in outputs.into_iter().zip(proc.entry_stack()) {
        analyzer.set_value_type(output_id, output_type.kind);
    }
}

pub(super) fn resolved_ident(
    program: &Program,
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    proc_id: ProcedureId,
) {
    let referenced_proc = program.get_proc(proc_id);
    let op_data = analyzer.get_op_io(op.id);

    match referenced_proc.kind() {
        ProcedureKind::Memory => {
            let output_id = op_data.outputs[0];
            analyzer.set_value_type(output_id, PorthTypeKind::Ptr);
        }
        _ => {
            for (expected, actual_id) in referenced_proc.entry_stack().iter().zip(&op_data.inputs) {
                let actual_type = analyzer.value_types([*actual_id]);

                if actual_type != Some([expected.kind]) {
                    let expected_kinds: Vec<_> = referenced_proc
                        .entry_stack()
                        .iter()
                        .map(|t| t.kind)
                        .collect();

                    failed_compare_stack_types(
                        analyzer,
                        source_store,
                        &op_data.inputs,
                        &expected_kinds,
                        referenced_proc.entry_stack_location(),
                        op.token.location,
                        "procedure call signature mismatch",
                    );
                    *had_error = true;
                    break;
                }
            }

            let output_ids = op_data.outputs.clone();

            for (&output_type, output_id) in referenced_proc.exit_stack().iter().zip(output_ids) {
                analyzer.set_value_type(output_id, output_type.kind);
            }
        }
    }
}

pub(super) fn syscall(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    num_args: usize,
) {
    let op_data = analyzer.get_op_io(op.id);

    // All syscall inputs are untyped.
    // The output is always an int.

    analyzer.set_value_type(op_data.outputs[0], PorthTypeKind::Int);
}

pub(super) fn analyze_while(
    program: &Program,
    proc: &Procedure,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    op: &Op,
    body: &ConditionalBlock,
) {
    super::analyze_block(
        program,
        proc,
        &body.condition,
        analyzer,
        had_error,
        interner,
        source_store,
    );
}
