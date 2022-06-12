use crate::{
    interners::Interners,
    opcode::{ConditionalBlock, Op},
    program::{
        static_analysis::{failed_compare_stack_types, Analyzer},
        Procedure, ProcedureId, Program,
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
pub(super) fn syscall(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    num_args: usize,
) {
    todo!()
}

pub(super) fn resolved_ident(
    program: &Program,
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    proc_id: ProcedureId,
) {
    todo!()
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
    todo!()
}
