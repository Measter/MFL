use crate::{
    interners::Interners,
    opcode::{ConditionalBlock, Op},
    program::{
        static_analysis::{Analyzer, ConstVal, PtrId},
        ProcedureHeader, ProcedureId, ProcedureKind, Program,
    },
    source_file::SourceStorage,
};

pub(super) fn resolved_ident(
    program: &Program,
    analyzer: &mut Analyzer,
    op: &Op,
    proc_id: ProcedureId,
) {
    let referenced_proc = program.get_proc_header(proc_id);
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
    proc: &ProcedureHeader,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    op: &Op,
    body: &ConditionalBlock,
) {
    // Because the loop will be executed an arbitrary number of times, we'll need to
    // force all overwritten pre-loop values to non-const.
    let Some(merge_info) = analyzer.get_while_merges(op.id).map(Clone::clone) else {
        panic!("ICE: While block should have merge info");
    };
    let pairs = merge_info.condition.iter().chain(&merge_info.body);
    for merge_pair in pairs {
        analyzer.clear_value_const(merge_pair.pre_value);
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
    proc: &ProcedureHeader,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    condition: &ConditionalBlock,
    else_block: &[Op],
) {
    // The condition is always executed, so we can const prop that.
    super::analyze_block(
        program,
        proc,
        &condition.condition,
        analyzer,
        had_error,
        interner,
        source_store,
    );

    // Both blocks should be analyzed with const prop allowed.
    super::analyze_block(
        program,
        proc,
        &condition.block,
        analyzer,
        had_error,
        interner,
        source_store,
    );
    super::analyze_block(
        program,
        proc,
        else_block,
        analyzer,
        had_error,
        interner,
        source_store,
    );

    // Don't set the const value of merge outputs.
}
