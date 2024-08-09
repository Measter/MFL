use ariadne::{Color, Label};
use hashbrown::HashMap;
use intcast::IntCast;
use stores::items::ItemId;

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    n_ops::SliceNOps,
    stores::{
        ops::OpId,
        types::{Integer, TypeKind},
        values::ConstVal,
    },
    Stores,
};

pub(crate) fn insert_extract_array(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let &[.., array_value_id, idx_value_id] = op_data.inputs.as_slice() else {
        unreachable!()
    };
    let [ConstVal::Int(Integer::Unsigned(idx))] = stores.values.value_consts([idx_value_id]) else {
        // We're only doing bounds checking here, so nothing to do if we don't know the index.
        return;
    };

    let [array_type_id] = stores.values.value_types([array_value_id]).unwrap();
    let array_type_info = stores.types.get_type_info(array_type_id);

    let array_length = match array_type_info.kind {
        TypeKind::Array { length, .. } => length,
        TypeKind::MultiPointer(ptee_id) | TypeKind::SinglePointer(ptee_id) => {
            let info = stores.types.get_type_info(ptee_id);
            match info.kind {
                TypeKind::Array { length, .. } => length,
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
                TypeKind::Integer(_)
                | TypeKind::Float(_)
                | TypeKind::MultiPointer(_)
                | TypeKind::SinglePointer(_)
                | TypeKind::Bool
                | TypeKind::GenericStructBase(_) => unreachable!(),
            }
        }
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
        TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_) => unreachable!(),
    };

    if idx.to_usize() < array_length {
        return;
    }

    let array_type_name = stores.strings.resolve(array_type_info.friendly_name);
    let idx_value = idx.to_string();
    let mut labels = diagnostics::build_creator_label_chain(
        stores,
        [
            (array_value_id, 0, array_type_name),
            (idx_value_id, 1, &idx_value),
        ],
        Color::Yellow,
        Color::Cyan,
    );
    let op_loc = stores.ops.get_token(op_id).location;
    labels.push(Label::new(op_loc).with_color(Color::Red));

    diagnostics::emit_error(stores, op_loc, "index out of bounds", labels, None);

    had_error.set();
}

pub(crate) fn load(
    stores: &mut Stores,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    had_error: &mut ErrorSignal,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let var_value_id = op_data.inputs[0];
    let [var_const_value] = stores.values.value_consts([var_value_id]);

    let ConstVal::SinglePtr { source_variable } = var_const_value else {
        return;
    };

    let Some(state) = variable_state.get(&source_variable) else {
        // It's a global variable, we can't handle those.
        return;
    };

    if matches!(state, ConstVal::Uninitialized) {
        let var_header = stores.items.get_item_header(source_variable);
        let op_loc = stores.ops.get_token(op_id);

        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(var_value_id, 0, "variable pointer")],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op_loc.location).with_color(Color::Red));
        labels.push(
            Label::new(var_header.name.location)
                .with_color(Color::Cyan)
                .with_message("Variable defined here"),
        );

        diagnostics::emit_error(
            stores,
            op_loc.location,
            "Read from uninitialized variable",
            labels,
            None,
        );

        had_error.set();
    }
}

pub(crate) fn store(
    stores: &mut Stores,
    variable_state: &mut HashMap<ItemId, ConstVal>,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_ids = *op_data.inputs.as_arr();
    let [data_const_val, var_const_value] = stores.values.value_consts(input_value_ids);

    let ConstVal::SinglePtr { source_variable } = var_const_value else {
        return;
    };

    let Some(state) = variable_state.get_mut(&source_variable) else {
        // It's a global variable, we can't handle those.
        return;
    };

    *state = data_const_val;
}
