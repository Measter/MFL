use crate::{
    interners::Interners,
    opcode::{ConditionalBlock, Op},
    program::{static_analysis::Analyzer, Procedure, ProcedureId, Program},
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
