use intcast::IntCast;
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
        values::{ConstVal, Offset},
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
            let res = comp_code.get_bool_binary_op()(*a, *b);
            ConstVal::Bool(res)
        }

        // Static pointers with different IDs.
        [ConstVal::Pointer {
            source_variable: id1,
            ..
        }, ConstVal::Pointer {
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

        // Multi-Pointers with same IDs, and known indices.
        [ConstVal::Pointer {
            source_variable,
            offsets: Some(offset1),
            ..
        }, ConstVal::Pointer {
            offsets: Some(offset2),
            ..
        }] => {
            if offset1.len() != offset2.len() {
                // User tried to compare pointers at different depths within a variable.
                Diagnostic::error(op_loc, "pointers have different sources")
                    .with_label_chain(input_value_ids[1], 1, "comparing this...")
                    .with_label_chain(input_value_ids[0], 0, "... and this")
                    .attached(stores.diags, item_id);

                had_error.set();
                ConstVal::Bool(false)
            } else if offset1.is_empty() {
                // Both pointers point at the head of the variable.
                ConstVal::Bool(true)
            } else {
                let [head_front @ .., head_last] = &**offset1 else {
                    unreachable!()
                };
                let [tail_front @ .., tails_last] = &**offset2 else {
                    unreachable!()
                };

                let mut const_val = ConstVal::Unknown;
                let mut early_break = false;
                let mut pointed_at_type = stores.sigs.trir.get_variable_type(*source_variable);
                for (head, tail) in head_front.iter().zip(tail_front) {
                    match (head, tail) {
                        (Offset::Known(h), Offset::Known(t)) => {
                            if h != t {
                                Diagnostic::error(op_loc, "pointers have different sources")
                                    .with_label_chain(input_value_ids[1], 1, "comparing this...")
                                    .with_label_chain(input_value_ids[0], 0, "... and this")
                                    .attached(stores.diags, item_id);

                                had_error.set();
                                early_break = true;
                                break;
                            }

                            let var_type_info = stores.types.get_type_info(pointed_at_type);
                            match var_type_info.kind {
                                TypeKind::Array { type_id, .. } => {
                                    pointed_at_type = type_id;
                                }
                                TypeKind::Struct(_) => {
                                    let struct_def = stores.types.get_struct_def(pointed_at_type);
                                    pointed_at_type = struct_def.fields[h.to_usize()].kind.inner;
                                }
                                _ => unreachable!(),
                            }
                        }
                        _ => {
                            const_val = ConstVal::Unknown;
                            early_break = true;
                            break;
                        }
                    }
                }

                if !early_break {
                    let pointed_type_info = stores.types.get_type_info(pointed_at_type);
                    if !matches!(pointed_type_info.kind, TypeKind::Array { .. }) {
                        // The last type we're indexing into is not an array, which means the user
                        // is trying to subtract pointers to different fields of the same struct.
                        Diagnostic::error(op_loc, "cannot compare field pointers")
                            .with_label_chain(input_value_ids[1], 1, "comparing this...")
                            .with_label_chain(input_value_ids[0], 0, "... and this")
                            .attached(stores.diags, item_id);

                        had_error.set();
                    } else {
                        // We know the user is comparing pointers within an array.
                        if let (Offset::Known(h), Offset::Known(t)) = (head_last, tails_last) {
                            let res = comp_code.get_unsigned_binary_op()(*h, *t);
                            const_val = ConstVal::Bool(res != 0);
                        }
                    }
                }

                const_val
            }
        }

        // Different IDs, one or both with unknown indices.
        [ConstVal::Pointer { .. }, ConstVal::Pointer { .. }] => ConstVal::Unknown,
        [ConstVal::Uninitialized, _] | [_, ConstVal::Uninitialized] => ConstVal::Uninitialized,

        #[expect(clippy::match_same_arms)]
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

            // The casts are already type checked.
            let biggest_input_float = a_float.max(b_float);
            let a_kind = a.cast(biggest_input_float);
            let b_kind = b.cast(biggest_input_float);
            let res = comp_code.get_float_binary_op()(a_kind.0, b_kind.0);
            ConstVal::Bool(res)
        }

        // Static pointers with different IDs.
        [ConstVal::Pointer {
            source_variable: id1,
            ..
        }, ConstVal::Pointer {
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

        // Pointers with same IDs, and with known indices.
        [ConstVal::Pointer {
            source_variable,
            offsets: Some(offset1),
            ..
        }, ConstVal::Pointer {
            offsets: Some(offset2),
            ..
        }] => {
            if offset1.len() != offset2.len() {
                // User tried to compare pointers at different depths within a variable.
                Diagnostic::error(op_loc, "pointers have different sources")
                    .with_label_chain(input_value_ids[1], 1, "comparing this...")
                    .with_label_chain(input_value_ids[0], 0, "... and this")
                    .attached(stores.diags, item_id);

                had_error.set();
                ConstVal::Bool(false)
            } else if offset1.is_empty() {
                // Both pointers point at the head of the variable.
                ConstVal::Bool(true)
            } else {
                let [head_front @ .., head_last] = &**offset1 else {
                    unreachable!()
                };
                let [tail_front @ .., tails_last] = &**offset2 else {
                    unreachable!()
                };

                let mut const_val = ConstVal::Unknown;
                let mut early_break = false;
                let mut pointed_at_type = stores.sigs.trir.get_variable_type(*source_variable);
                for (head, tail) in head_front.iter().zip(tail_front) {
                    match (head, tail) {
                        (Offset::Known(h), Offset::Known(t)) => {
                            if h != t {
                                Diagnostic::error(op_loc, "pointers have different sources")
                                    .with_label_chain(input_value_ids[1], 1, "comparing this...")
                                    .with_label_chain(input_value_ids[0], 0, "... and this")
                                    .attached(stores.diags, item_id);

                                had_error.set();
                                early_break = true;
                                break;
                            }

                            let var_type_info = stores.types.get_type_info(pointed_at_type);
                            match var_type_info.kind {
                                TypeKind::Array { type_id, .. } => {
                                    pointed_at_type = type_id;
                                }
                                TypeKind::Struct(_) => {
                                    let struct_def = stores.types.get_struct_def(pointed_at_type);
                                    pointed_at_type = struct_def.fields[h.to_usize()].kind.inner;
                                }
                                _ => unreachable!(),
                            }
                        }
                        _ => {
                            const_val = ConstVal::Unknown;
                            early_break = true;
                            break;
                        }
                    }
                }

                if !early_break {
                    let pointed_type_info = stores.types.get_type_info(pointed_at_type);
                    if !matches!(pointed_type_info.kind, TypeKind::Array { .. }) {
                        // The last type we're indexing into is not an array, which means the user
                        // is trying to subtract pointers to different fields of the same struct.
                        Diagnostic::error(op_loc, "cannot compare field pointers")
                            .with_label_chain(input_value_ids[1], 1, "comparing this...")
                            .with_label_chain(input_value_ids[0], 0, "... and this")
                            .attached(stores.diags, item_id);

                        had_error.set();
                    } else {
                        // We know the user is comparing pointers within an array.
                        if let (Offset::Known(h), Offset::Known(t)) = (head_last, tails_last) {
                            let res = comp_code.get_unsigned_binary_op()(*h, *t);
                            const_val = ConstVal::Bool(res != 0);
                        }
                    }
                }

                const_val
            }
        }

        // Different IDs, one or both with unknown indices.
        [ConstVal::Pointer { .. }, ConstVal::Pointer { .. }] => ConstVal::Unknown,
        [ConstVal::Uninitialized, _] | [_, ConstVal::Uninitialized] => ConstVal::Uninitialized,

        #[expect(clippy::match_same_arms)]
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
        ConstVal::Pointer { .. } => {
            // We have a const value from a statically known pointer, so it can't be null.
            ConstVal::Bool(false)
        }
        ConstVal::Uninitialized => ConstVal::Uninitialized,
        ConstVal::Unknown => ConstVal::Unknown,
        ConstVal::Int(_)
        | ConstVal::Enum(_, _)
        | ConstVal::Float(_)
        | ConstVal::Bool(_)
        | ConstVal::Aggregate { .. } => {
            unreachable!()
        }
    };

    stores
        .values
        .set_value_const(output_value_id, new_output_const_val);
}
