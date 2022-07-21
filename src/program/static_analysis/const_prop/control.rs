use log::trace;

use crate::{
    interners::Interners,
    opcode::{ConditionalBlock, Op},
    program::{
        static_analysis::{Analyzer, ConstVal, MergeInfo, PtrId},
        Procedure, ProcedureId, ProcedureKind, Program,
    },
    source_file::SourceStorage,
};

pub(super) fn resolved_ident(
    program: &Program,
    analyzer: &mut Analyzer,
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
    // Because the loop will be executed an arbitrary number of times, we'll need to
    // force all overwritten prior values to non-const.
    let Some(MergeInfo::While(merge_info)) = analyzer.get_op_merges(op.id) else {
        panic!("ICE: While block should have merge info");
    };
    let pairs: Vec<_> = merge_info
        .condition_merges
        .iter()
        .chain(&merge_info.body_merges)
        .copied()
        .collect();
    for merge_pair in pairs {
        trace!(
            "Merge {:?} with {:?}, const: {:?}",
            merge_pair.src,
            merge_pair.dst,
            analyzer.value_consts([merge_pair.dst])
        );
        analyzer.clear_value_const(merge_pair.dst);
    }

    // Now we can evaluate the condition and body.
    super::analyze_block(
        program,
        proc,
        &body.condition,
        analyzer,
        had_error,
        interner,
        source_store,
    );
    super::analyze_block(
        program,
        proc,
        &body.block,
        analyzer,
        had_error,
        interner,
        source_store,
    );
}

pub(super) fn analyze_if(
    program: &Program,
    proc: &Procedure,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    op: &Op,
    condition: &ConditionalBlock,
    else_block: Option<&[Op]>,
) {
    todo!()
}
