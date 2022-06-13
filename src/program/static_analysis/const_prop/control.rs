use crate::{
    interners::Interners,
    opcode::{ConditionalBlock, Op},
    program::{
        static_analysis::{Analyzer, ConstVal, PtrId},
        Procedure, ProcedureId, ProcedureKind, Program,
    },
    source_file::SourceStorage,
};

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

    if let ProcedureKind::Memory = referenced_proc.kind() {
        let output_id = op_data.outputs[0];
        analyzer.set_value_const(
            output_id,
            ConstVal::Ptr {
                id: PtrId::Mem(proc_id),
                src_op_loc: op.token.location,
                offset: Some(0),
            },
        );
    }
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
