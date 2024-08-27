use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    ir::Compare,
    n_ops::SliceNOps,
    pass_manager::static_analysis::promote_int_type_bidirectional,
    stores::{
        diagnostics::Diagnostic,
        ops::OpId,
        types::{Integer, TypeKind},
        values::ConstVal,
    },
    Stores,
};

pub(crate) fn equal(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    comp_code: Compare,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let input_type_ids = stores.values.value_types(input_value_ids).unwrap();
    let input_const_vals = stores.values.value_consts(input_value_ids);

    let output_const_val = match input_const_vals {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] =
                input_type_ids.map(|id| stores.types.get_type_info(id).kind)
            else {
                unreachable!()
            };

            // The casts are already type checked.
            let biggest_input_int = promote_int_type_bidirectional(a_int, b_int).unwrap();
            let a_kind = a.cast(biggest_input_int);
            let b_kind = b.cast(biggest_input_int);
            let res = match (a_kind, b_kind) {
                (Integer::Signed(a), Integer::Signed(b)) => {
                    comp_code.get_signed_binary_op()(a, b) != 0
                }
                (Integer::Unsigned(a), Integer::Unsigned(b)) => {
                    comp_code.get_unsigned_binary_op()(a, b) != 0
                }

                _ => unreachable!(),
            };
            ConstVal::Bool(res)
        }

        [ConstVal::Float(a), ConstVal::Float(b)] => {
            let [TypeKind::Float(a_float), TypeKind::Float(b_float)] =
                input_type_ids.map(|id| stores.types.get_type_info(id).kind)
            else {
                unreachable!()
            };

            let biggest_input_float = a_float.max(b_float);
            let a_kind = a.cast(biggest_input_float);
            let b_kind = b.cast(biggest_input_float);
            let res = comp_code.get_float_binary_op()(a_kind.0, b_kind.0);
            ConstVal::Bool(res)
        }

        [ConstVal::Bool(a), ConstVal::Bool(b)] => {
            let res = comp_code.get_bool_binary_op()(a, b);
            ConstVal::Bool(res)
        }

        // Static pointers with different IDs.
        [ConstVal::MultiPtr {
            source_variable: id1,
            ..
        }, ConstVal::MultiPtr {
            source_variable: id2,
            ..
        }]
        | [ConstVal::SinglePtr {
            source_variable: id1,
            ..
        }, ConstVal::SinglePtr {
            source_variable: id2,
            ..
        }] if id1 != id2 => {
            Diagnostic::error(op_loc, "pointers have different sources")
                .with_label_chain(input_value_ids[1], 1, "comparing this...")
                .with_label_chain(input_value_ids[0], 0, "... and this")
                .attached(stores.diags, item_id);

            had_error.set();
            ConstVal::Bool(false)
        }

        // Single-Pointers with same IDs
        [ConstVal::SinglePtr { .. }, ConstVal::SinglePtr { .. }] => {
            Diagnostic::warning(op_loc, "pointers always equal")
                .with_label_chain(input_value_ids[1], 1, "comparing this...")
                .with_label_chain(input_value_ids[0], 0, "... and this")
                .attached(stores.diags, item_id);

            let res = comp_code.get_unsigned_binary_op()(1, 1) != 0;
            ConstVal::Bool(res)
        }

        // Multi-Pointers with same IDs
        [ConstVal::MultiPtr {
            offset: Some(offset1),
            ..
        }, ConstVal::MultiPtr {
            offset: Some(offset2),
            ..
        }] => {
            let msg = if offset1 == offset2 {
                "pointers always equal"
            } else {
                "pointers never equal"
            };

            Diagnostic::warning(op_loc, msg)
                .with_label_chain(input_value_ids[1], 1, "comparing this...")
                .with_label_chain(input_value_ids[0], 0, "... and this")
                .attached(stores.diags, item_id);

            let res = comp_code.get_unsigned_binary_op()(offset1, offset2) != 0;
            ConstVal::Bool(res)
        }

        [ConstVal::Uninitialized, _] | [_, ConstVal::Uninitialized] => ConstVal::Uninitialized,
        [ConstVal::Unknown, _] | [_, ConstVal::Unknown] => ConstVal::Unknown,
        _ => return,
    };

    let output_value_id = op_data.outputs[0];
    stores
        .values
        .set_value_const(output_value_id, output_const_val);
}

pub(crate) fn compare(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    comp_code: Compare,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let input_type_ids = stores.values.value_types(input_value_ids).unwrap();
    let input_const_vals = stores.values.value_consts(input_value_ids);

    let output_const_val = match input_const_vals {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] =
                input_type_ids.map(|id| stores.types.get_type_info(id).kind)
            else {
                unreachable!()
            };

            // The casts are already type checked.
            let biggest_input_int = promote_int_type_bidirectional(a_int, b_int).unwrap();
            let a_kind = a.cast(biggest_input_int);
            let b_kind = b.cast(biggest_input_int);

            let res = match (a_kind, b_kind) {
                (Integer::Signed(a), Integer::Signed(b)) => {
                    comp_code.get_signed_binary_op()(a, b) != 0
                }
                (Integer::Unsigned(a), Integer::Unsigned(b)) => {
                    comp_code.get_unsigned_binary_op()(a, b) != 0
                }

                _ => unreachable!(),
            };
            ConstVal::Bool(res)
        }

        [ConstVal::Float(a), ConstVal::Float(b)] => {
            let [TypeKind::Float(a_float), TypeKind::Float(b_float)] =
                input_type_ids.map(|id| stores.types.get_type_info(id).kind)
            else {
                unreachable!()
            };

            // The casts are already type checked.
            let biggest_input_float = a_float.max(b_float);
            let a_kind = a.cast(biggest_input_float);
            let b_kind = b.cast(biggest_input_float);
            let res = comp_code.get_float_binary_op()(a_kind.0, b_kind.0);
            ConstVal::Bool(res)
        }

        // Static pointers with different IDs.
        [ConstVal::MultiPtr {
            source_variable: id1,
            ..
        }, ConstVal::MultiPtr {
            source_variable: id2,
            ..
        }] if id1 != id2 => {
            let op_loc = stores.ops.get_token(op_id).location;
            Diagnostic::error(op_loc, "pointers have different sources")
                .with_label_chain(input_value_ids[1], 1, "comparing this...")
                .with_label_chain(input_value_ids[0], 0, "... and this")
                .attached(stores.diags, item_id);

            had_error.set();
            ConstVal::Bool(false)
        }

        // Pointers with same IDs, but different static offsets.
        [ConstVal::MultiPtr {
            offset: Some(offset1),
            ..
        }, ConstVal::MultiPtr {
            offset: Some(offset2),
            ..
        }] => {
            let res = comp_code.get_unsigned_binary_op()(offset1, offset2) != 0;
            ConstVal::Bool(res)
        }

        [ConstVal::Uninitialized, _] | [_, ConstVal::Uninitialized] => ConstVal::Uninitialized,
        [ConstVal::Unknown, _] | [_, ConstVal::Unknown] => ConstVal::Unknown,
        _ => return,
    };

    let output_value_value = op_data.outputs[0];
    stores
        .values
        .set_value_const(output_value_value, output_const_val);
}

pub(crate) fn is_null(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_id = op_data.inputs[0];
    let [input_const_val] = stores.values.value_consts([input_value_id]);
    let output_value_id = op_data.outputs[0];

    let new_output_const_val = match input_const_val {
        ConstVal::MultiPtr { .. } | ConstVal::SinglePtr { .. } => {
            // We have a const value from a statically known pointer, so it can't be null.
            ConstVal::Bool(false)
        }
        ConstVal::Uninitialized => ConstVal::Uninitialized,
        ConstVal::Unknown => ConstVal::Unknown,
        ConstVal::Int(_) | ConstVal::Float(_) | ConstVal::Bool(_) => unreachable!(),
    };

    stores
        .values
        .set_value_const(output_value_id, new_output_const_val);
}
