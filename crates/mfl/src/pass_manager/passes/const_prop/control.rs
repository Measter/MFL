use ariadne::Color;

use crate::{
    context::Context,
    diagnostics,
    error_signal::ErrorSignal,
    ir::{Op, TypeResolvedOp},
    pass_manager::static_analysis::{Analyzer, ConstVal, PtrId},
    Stores,
};

pub(crate) fn epilogue_return(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);

    for &input_value_id in &op_data.inputs {
        let Some(
            [ConstVal::Ptr {
                id: PtrId::Mem(memory_item_id),
                ..
            }],
        ) = analyzer.value_consts([input_value_id])
        else {
            continue;
        };

        let memory_header = ctx.get_item_header(memory_item_id);
        // We only care about local memories, not globals.
        if memory_header.parent.is_none() {
            continue;
        }

        let labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(input_value_id, 0, "")],
            Color::Yellow,
            Color::Cyan,
        );

        diagnostics::emit_error(
            stores,
            op.token.location,
            "returning pointer to local memory",
            labels,
            None,
        );

        had_error.set();
    }
}
