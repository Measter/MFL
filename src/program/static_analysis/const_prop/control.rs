use crate::{
    interners::Interners,
    opcode::{If, Op, While},
    program::{
        static_analysis::{Analyzer, ConstVal, PtrId},
        ItemId, ItemKind, Program,
    },
    source_file::SourceStorage,
};

pub(super) fn resolved_ident(program: &Program, analyzer: &mut Analyzer, op: &Op, item_id: ItemId) {
    let referenced_item = program.get_item_header(item_id);
    let op_data = analyzer.get_op_io(op.id);

    if let ItemKind::Memory = referenced_item.kind() {
        let output_id = op_data.outputs[0];
        analyzer.set_value_const(
            output_id,
            ConstVal::Ptr {
                id: PtrId::Mem(item_id),
                src_op_loc: op.token.location,
                offset: Some(0),
            },
        );
    }
}

pub(super) fn analyze_while(
    program: &Program,
    item_id: ItemId,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    op: &Op,
    while_op: &While,
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
        item_id,
        &while_op.condition,
        analyzer,
        had_error,
        interner,
        source_store,
    );
    super::analyze_block(
        program,
        item_id,
        &while_op.body_block,
        analyzer,
        had_error,
        interner,
        source_store,
    );
}

pub(super) fn analyze_if(
    program: &Program,
    item_id: ItemId,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
    if_op: &If,
) {
    // The condition is always executed, so we can const prop that.
    super::analyze_block(
        program,
        item_id,
        &if_op.condition,
        analyzer,
        had_error,
        interner,
        source_store,
    );

    // Both blocks should be analyzed with const prop allowed.
    super::analyze_block(
        program,
        item_id,
        &if_op.then_block,
        analyzer,
        had_error,
        interner,
        source_store,
    );
    super::analyze_block(
        program,
        item_id,
        &if_op.else_block,
        analyzer,
        had_error,
        interner,
        source_store,
    );

    // Don't set the const value of merge outputs.
}
