use ariadne::Color;

use crate::{
    context::{Context, ItemId, ItemKind},
    diagnostics,
    error_signal::ErrorSignal,
    pass_manager::PassContext,
    simulate::SimulatorValue,
    stores::{
        analyzer::{ConstVal, PtrId},
        ops::OpId,
    },
    Stores,
};

pub(crate) fn epilogue_return(
    ctx: &mut Context,
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);

    for &input_value_id in &op_data.inputs {
        let Some(
            [ConstVal::Ptr {
                id: PtrId::Mem(memory_item_id),
                ..
            }],
        ) = stores.values.value_consts([input_value_id])
        else {
            continue;
        };

        let memory_header = ctx.get_item_header(memory_item_id);
        // We only care about local memories, not globals.
        let parent_id = memory_header.parent.unwrap(); // Only top-level-modules don't have a parent.
        if ctx.get_item_header(parent_id).kind == ItemKind::Module {
            continue;
        }

        let labels = diagnostics::build_creator_label_chain(
            stores,
            [(input_value_id, 0, "")],
            Color::Yellow,
            Color::Cyan,
        );

        let op_loc = stores.ops.get_token(op_id).location;
        diagnostics::emit_error(
            stores,
            op_loc,
            "returning pointer to local memory",
            labels,
            None,
        );

        had_error.set();
    }
}

pub(crate) fn cp_const(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    op_id: OpId,
    const_item_id: ItemId,
) {
    if pass_ctx
        .ensure_evaluated_consts_asserts(ctx, stores, const_item_id)
        .is_err()
    {
        return;
    }

    let op_data = stores.ops.get_op_io(op_id);
    let Some(output_const_vals) = ctx.get_consts(const_item_id) else {
        return;
    };

    let output_value_ids = &op_data.outputs.clone();
    for (&value_id, const_value) in output_value_ids.into_iter().zip(output_const_vals) {
        let output_const_value = match const_value {
            SimulatorValue::Int { kind, .. } => ConstVal::Int(*kind),
            SimulatorValue::Bool(b) => ConstVal::Bool(*b),
        };

        stores.values.set_value_const(value_id, output_const_value);
    }
}

pub(crate) fn memory(stores: &mut Stores, op_id: OpId, memory_item_id: ItemId) {
    let op_data = stores.ops.get_op_io(op_id);
    let src_op_loc = stores.ops.get_token(op_id).location;
    stores.values.set_value_const(
        op_data.outputs[0],
        ConstVal::Ptr {
            id: PtrId::Mem(memory_item_id),
            src_op_loc,
            offset: Some(0),
        },
    );
}

pub(crate) fn analyze_while(stores: &mut Stores, op_id: OpId) {
    // Because the while loop may overwrite pre-values, we need to clear their
    // const values if they have any.

    let merges = stores.values.get_while_merges(op_id).unwrap().clone();
    for merge in merges.condition.into_iter().chain(merges.body) {
        stores.values.clear_value_const(merge.pre_value);
    }
}
