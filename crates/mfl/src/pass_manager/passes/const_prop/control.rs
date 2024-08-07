use ariadne::{Color, Label};
use stores::items::ItemId;

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{If, While},
    pass_manager::PassManager,
    simulate::SimulatorValue,
    stores::{item::ItemKind, ops::OpId, values::ConstVal},
    Stores,
};

pub(crate) fn epilogue_return(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);

    for &input_value_id in &op_data.inputs {
        let Some(
            [ConstVal::MultiPtr {
                source_variable: variable_item_id,
                ..
            }
            | ConstVal::SinglePtr {
                source_variable: variable_item_id,
                ..
            }],
        ) = stores.values.value_consts([input_value_id])
        else {
            continue;
        };

        let variable_header = stores.items.get_item_header(variable_item_id);
        // We only care about local memories, not globals.
        let parent_id = variable_header.parent.unwrap(); // Only top-level-modules don't have a parent.
        if stores.items.get_item_header(parent_id).kind == ItemKind::Module {
            continue;
        }

        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(input_value_id, 0, "pointer")],
            Color::Yellow,
            Color::Cyan,
        );

        labels.push(
            Label::new(variable_header.name.location)
                .with_color(Color::Cyan)
                .with_message("points to this variable"),
        );

        let op_loc = stores.ops.get_token(op_id).location;
        diagnostics::emit_error(
            stores,
            op_loc,
            "returning pointer to local variable",
            labels,
            None,
        );

        had_error.set();
    }
}

pub(crate) fn cp_const(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    op_id: OpId,
    const_item_id: ItemId,
) {
    if pass_manager
        .ensure_evaluated_consts_asserts(stores, const_item_id)
        .is_err()
    {
        return;
    }

    let op_data = stores.ops.get_op_io(op_id);
    let Some(output_const_vals) = stores.items.get_consts(const_item_id) else {
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

pub(crate) fn variable(stores: &mut Stores, op_id: OpId, variable_item_id: ItemId) {
    let op_data = stores.ops.get_op_io(op_id);
    stores.values.set_value_const(
        op_data.outputs[0],
        ConstVal::SinglePtr {
            source_variable: variable_item_id,
        },
    );
}

pub(crate) fn analyze_if(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    if_op: If,
) {
    super::analyze_block(stores, pass_manager, had_error, if_op.condition);
    super::analyze_block(stores, pass_manager, had_error, if_op.then_block);
    super::analyze_block(stores, pass_manager, had_error, if_op.else_block);
}

pub(crate) fn analyze_while(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    while_op: While,
) {
    super::analyze_block(stores, pass_manager, had_error, while_op.condition);
    super::analyze_block(stores, pass_manager, had_error, while_op.body_block);
}
