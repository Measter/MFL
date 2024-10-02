use hashbrown::HashMap;
use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    ir::{Cond, While},
    pass_manager::PassManager,
    simulate::SimulatorValue,
    stores::{
        diagnostics::Diagnostic, item::ItemKind, ops::OpId, signatures::StackDefItemNameResolved,
        values::ConstVal,
    },
    Stores,
};

use super::{new_const_val_for_type, ConstFieldInitState};

pub(crate) fn epilogue_return(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);

    for &input_value_id in &op_data.inputs {
        let [ConstVal::Pointer {
            source_variable: variable_item_id,
            ..
        }] = stores.values.value_consts([input_value_id])
        else {
            continue;
        };

        let variable_header = stores.items.get_item_header(*variable_item_id);
        // We only care about local memories, not globals.
        let parent_id = variable_header.parent.unwrap(); // Only top-level-modules don't have a parent.
        if stores.items.get_item_header(parent_id).kind == ItemKind::Module {
            continue;
        }

        let op_loc = stores.ops.get_token(op_id).location;
        Diagnostic::error(op_loc, "returning pointer to local variable")
            .with_help_label(variable_header.name.location, "points to this variable")
            .with_label_chain(input_value_id, 0, "pointer")
            .attached(stores.diags, item_id);

        had_error.set();
    }
}

pub(crate) fn prologue(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    item_id: ItemId,
) {
    let nr_sig = stores.sigs.nrir.get_item_signature(item_id).clone();
    let tr_sig = stores.sigs.trir.get_item_signature(item_id).clone();
    for (param, param_type_id) in nr_sig.entry.iter().zip(&tr_sig.entry) {
        let StackDefItemNameResolved::Var { name, .. } = param else {
            continue;
        };

        *variable_state.get_mut(name).unwrap() = new_const_val_for_type(
            stores,
            pass_manager,
            had_error,
            *param_type_id,
            ConstFieldInitState::Unknown,
        );
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
            SimulatorValue::EnumValue { id, discrim } => ConstVal::Enum(*id, *discrim),
        };

        stores.values.set_value_const(value_id, output_const_value);
    }
}

pub(crate) fn call_function(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    op_id: OpId,
) {
    let outputs = stores.ops.get_op_io(op_id).outputs.clone();

    for value_id in outputs {
        let [output_type_id] = stores.values.value_types([value_id]).unwrap();

        let new_value = new_const_val_for_type(
            stores,
            pass_manager,
            had_error,
            output_type_id,
            ConstFieldInitState::Unknown,
        );

        stores.values.set_value_const(value_id, new_value);
    }
}

pub(crate) fn variable(stores: &mut Stores, op_id: OpId, variable_item_id: ItemId) {
    let op_data = stores.ops.get_op_io(op_id);
    stores.values.set_value_const(
        op_data.outputs[0],
        ConstVal::Pointer {
            source_variable: variable_item_id,
            offsets: Some(Vec::new()),
        },
    );
}

pub(crate) fn analyze_cond(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    had_error: &mut ErrorSignal,
    proc_item_id: ItemId,
    cond_op: Cond,
) {
    let pre_cond_variable_state = variable_state.clone();
    let mut final_variable_state = HashMap::new();

    for arm in &cond_op.arms {
        super::analyze_block(
            stores,
            pass_manager,
            variable_state,
            had_error,
            proc_item_id,
            arm.condition,
        );

        super::analyze_block(
            stores,
            pass_manager,
            variable_state,
            had_error,
            proc_item_id,
            arm.block,
        );

        if final_variable_state.is_empty() {
            // If we've not checked anything yet, start from the first arm's state.
            // If we started from pre_cond_variable_state then anything uninitialized
            // would stay uninitialized, even if all arms assigned.
            final_variable_state.clone_from(variable_state);
        } else {
            for (var_id, final_state) in &mut final_variable_state {
                let post_block_state = &variable_state[var_id];
                merge_branched_const_val(post_block_state, final_state);
            }
        }

        variable_state.clone_from(&pre_cond_variable_state);
    }

    super::analyze_block(
        stores,
        pass_manager,
        variable_state,
        had_error,
        proc_item_id,
        cond_op.else_block,
    );

    for (var_id, final_state) in &mut final_variable_state {
        let post_block_state = &variable_state[var_id];
        merge_branched_const_val(post_block_state, final_state);
    }

    *variable_state = final_variable_state;
}

fn merge_branched_const_val(post_block_state: &ConstVal, final_state: &mut ConstVal) {
    if post_block_state == final_state {
        return;
    }

    match (post_block_state, &mut *final_state) {
        (ConstVal::Uninitialized, _) | (_, ConstVal::Uninitialized) => {
            *final_state = ConstVal::Uninitialized
        }
        (
            ConstVal::Aggregate {
                sub_values: pb_substates,
            },
            ConstVal::Aggregate {
                sub_values: final_substates,
            },
        ) => {
            for (pbss, fss) in pb_substates.iter().zip(final_substates) {
                merge_branched_const_val(pbss, fss);
            }
        }
        _ => *final_state = ConstVal::Unknown,
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
