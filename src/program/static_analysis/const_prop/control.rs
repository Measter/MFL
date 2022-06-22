use log::trace;

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
    let op_data = analyzer.get_op_io(op.id);

    // Because the loop will be executed an arbitrary number of times, we'll need to
    // force all overwritten prior values to non-const.
    let inputs = op_data.outputs.clone();
    for input_id in inputs {
        let [input_value] = analyzer.values([input_id]);
        let Some(merge_id) = input_value.merge_with() else { continue };
        trace!(
            "Merge {input_id:?} with {merge_id:?}, const: {:?}",
            analyzer.value_consts([merge_id])
        );
        analyzer.clear_value_const(merge_id);
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
