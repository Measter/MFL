use ariadne::{Color, Label};
use hashbrown::HashMap;
use stores::items::ItemId;

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{If, While},
    pass_manager::PassManager,
    simulate::SimulatorValue,
    stores::{item::ItemKind, ops::OpId, signatures::StackDefItemNameResolved, values::ConstVal},
    Stores,
};

pub(crate) fn epilogue_return(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);

    for &input_value_id in &op_data.inputs {
        let [ConstVal::MultiPtr {
            source_variable: variable_item_id,
            ..
        }
        | ConstVal::SinglePtr {
            source_variable: variable_item_id,
            ..
        }] = stores.values.value_consts([input_value_id])
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

pub(crate) fn prologue(
    stores: &mut Stores,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    item_id: ItemId,
) {
    let sig = stores.sigs.nrir.get_item_signature(item_id);
    for param in &sig.entry {
        let StackDefItemNameResolved::Var { name, .. } = param else {
            continue;
        };

        *variable_state.get_mut(name).unwrap() = ConstVal::Unknown;
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
    variable_state: &mut HashMap<ItemId, ConstVal>,
    had_error: &mut ErrorSignal,
    proc_item_id: ItemId,
    if_op: If,
) {
    super::analyze_block(
        stores,
        pass_manager,
        variable_state,
        had_error,
        proc_item_id,
        if_op.condition,
    );

    let post_condition_var_state = variable_state.clone();
    super::analyze_block(
        stores,
        pass_manager,
        variable_state,
        had_error,
        proc_item_id,
        if_op.then_block,
    );

    let post_then_var_state = variable_state.clone();
    variable_state.clone_from(&post_condition_var_state);
    super::analyze_block(
        stores,
        pass_manager,
        variable_state,
        had_error,
        proc_item_id,
        if_op.else_block,
    );

    for (var_id, else_state) in variable_state {
        let then_state = post_then_var_state[var_id];

        match (then_state, *else_state) {
            (ConstVal::Uninitialized, _) | (_, ConstVal::Uninitialized) => {
                *else_state = ConstVal::Uninitialized
            }
            (ConstVal::Unknown, _) | (_, ConstVal::Unknown) => *else_state = ConstVal::Unknown,
            _ if then_state == *else_state => {}
            _ => *else_state = ConstVal::Unknown,
        }
    }
}

pub(crate) fn analyze_while(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    had_error: &mut ErrorSignal,
    proc_item_id: ItemId,
    while_op: While,
) {
    super::analyze_block(
        stores,
        pass_manager,
        variable_state,
        had_error,
        proc_item_id,
        while_op.condition,
    );

    let post_condition_var_state = variable_state.clone();
    super::analyze_block(
        stores,
        pass_manager,
        variable_state,
        had_error,
        proc_item_id,
        while_op.body_block,
    );
    variable_state.clone_from(&post_condition_var_state);
}
