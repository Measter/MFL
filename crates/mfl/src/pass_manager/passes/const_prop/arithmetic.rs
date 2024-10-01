use num_traits::Zero;
use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    ir::Arithmetic,
    n_ops::SliceNOps,
    stores::{
        diagnostics::Diagnostic,
        ops::OpId,
        types::{Float, Integer, TypeKind},
        values::ConstVal,
    },
    Stores,
};

pub(crate) fn add(stores: &mut Stores, op_id: OpId, arith_code: Arithmetic) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let Some([output_type_id]) = stores.values.value_types([op_data.outputs[0]]) else {
        return;
    };
    let output_type_info = stores.types.get_type_info(output_type_id);
    let input_const_values = stores.values.value_consts(input_value_ids);

    let new_const_val = match input_const_values {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };

            // The cast has already been type checked.
            let a_kind = a.cast(output_int);
            let b_kind = b.cast(output_int);
            let kind = match (a_kind, b_kind) {
                (Integer::Signed(a), Integer::Signed(b)) => {
                    Integer::Signed(arith_code.get_signed_binary_op()(a, b))
                }
                (Integer::Unsigned(a), Integer::Unsigned(b)) => {
                    Integer::Unsigned(arith_code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };

            ConstVal::Int(kind)
        }

        [ConstVal::Float(a), ConstVal::Float(b)] => {
            let TypeKind::Float(output_float) = output_type_info.kind else {
                unreachable!()
            };

            // The cast has already been type checked.
            let a_kind = a.cast(output_float);
            let b_kind = b.cast(output_float);
            let output_kind = Float(arith_code.get_float_binary_op()(a_kind.0, b_kind.0));
            // Re-perform the cast to ensure the float is correctly truncated if it's an f32.
            ConstVal::Float(output_kind.cast(output_float))
        }

        // Pointer offset.
        [ConstVal::Pointer {
            source_variable: id,
            offset: Some(offset),
        }, ConstVal::Int(Integer::Unsigned(v))]
        | [ConstVal::Int(Integer::Unsigned(v)), ConstVal::Pointer {
            source_variable: id,
            offset: Some(offset),
        }] => ConstVal::Pointer {
            source_variable: *id,
            offset: Some(offset + v),
        },

        [ConstVal::Uninitialized, _] | [_, ConstVal::Uninitialized] => ConstVal::Uninitialized,
        [ConstVal::Unknown, _] | [_, ConstVal::Unknown] => ConstVal::Unknown,
        _ => return,
    };

    let output_id = op_data.outputs[0];
    stores.values.set_value_const(output_id, new_const_val);
}

pub(crate) fn bitand_bitor_bitxor(stores: &mut Stores, op_id: OpId, arith_code: Arithmetic) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let input_const_vals = stores.values.value_consts(input_value_ids);

    let Some([output_type_id]) = stores.values.value_types([op_data.outputs[0]]) else {
        return;
    };
    let output_type_info = stores.types.get_type_info(output_type_id);

    let output_const_val = match input_const_vals {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };

            // The cast is already type checked.
            let a_kind = a.cast(output_int);
            let b_kind = b.cast(output_int);
            let kind = match (a_kind, b_kind) {
                (Integer::Signed(a), Integer::Signed(b)) => {
                    Integer::Signed(arith_code.get_signed_binary_op()(a, b))
                }
                (Integer::Unsigned(a), Integer::Unsigned(b)) => {
                    Integer::Unsigned(arith_code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };

            ConstVal::Int(kind)
        }
        [ConstVal::Bool(a), ConstVal::Bool(b)] => {
            ConstVal::Bool(arith_code.get_bool_binary_op()(*a, *b))
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

pub(crate) fn bitnot(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_id = op_data.inputs[0];
    let [input_const_val] = stores.values.value_consts([input_value_id]);
    let Some([output_type_id]) = stores.values.value_types([op_data.outputs[0]]) else {
        return;
    };
    let output_type_info = stores.types.get_type_info(output_type_id);

    let output_const_val = match input_const_val {
        ConstVal::Int(Integer::Unsigned(a)) => {
            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };
            ConstVal::Int(Integer::Unsigned((!a) & output_int.width.mask()))
        }
        ConstVal::Int(Integer::Signed(a)) => {
            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };
            ConstVal::Int(Integer::Signed((!a) & output_int.width.mask() as i64))
        }
        ConstVal::Bool(b) => ConstVal::Bool(!b),
        ConstVal::Uninitialized => ConstVal::Uninitialized,
        ConstVal::Unknown => ConstVal::Unknown,
        _ => return,
    };

    let output_value_id = op_data.outputs[0];
    stores
        .values
        .set_value_const(output_value_id, output_const_val);
}

pub(crate) fn multiply_div_rem_shift(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    arith_code: Arithmetic,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let Some([output_type_id]) = stores.values.value_types([op_data.outputs[0]]) else {
        return;
    };
    let output_type_info = stores.types.get_type_info(output_type_id);

    let [a_const_val, b_const_val] = stores.values.value_consts(input_value_ids);

    // If we can, check the b-side for invalid or out-of-range values.
    match arith_code {
        Arithmetic::ShiftLeft | Arithmetic::ShiftRight
            if matches!(b_const_val, ConstVal::Int(_)) =>
        {
            let ConstVal::Int(b_const_val) = b_const_val else {
                unreachable!()
            };

            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };

            let (is_out_of_range, shift_value_string) = match b_const_val {
                Integer::Signed(v @ 0..) if *v < output_int.width.bit_width() as _ => {
                    (false, String::new())
                }
                Integer::Unsigned(v @ 0..) if *v < output_int.width.bit_width() as _ => {
                    (false, String::new())
                }

                Integer::Signed(v) => (true, v.to_string()),
                Integer::Unsigned(v) => (true, v.to_string()),
            };

            if is_out_of_range {
                let output_type_name = stores.strings.resolve(output_type_info.friendly_name);

                Diagnostic::warning(op_loc, "shift value out of range")
                .with_note(
                    format!(
                        "shift value ({shift_value_string}) masked to the width of a {output_type_name}"
                    ),
                )
                .with_label_chain(input_value_ids[1], 0, "shift value from here").attached(stores.diags, item_id);
            }
        }

        Arithmetic::Div | Arithmetic::Rem => {
            let div_is_zero = matches!(
                b_const_val,
                ConstVal::Int(Integer::Signed(0) | Integer::Unsigned(0))
                    | ConstVal::Float(Float(0.0))
            );
            if div_is_zero {
                Diagnostic::error(op_loc, "division by 0")
                    .with_label_chain(input_value_ids[1], 0, "divisor from here")
                    .attached(stores.diags, item_id);

                had_error.set();
            }
        }

        _ => {}
    }

    let output_value = match [a_const_val, b_const_val] {
        [ConstVal::Int(a_const_val), ConstVal::Int(b_const_val)] => {
            if b_const_val.is_zero() {
                return;
            }

            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };

            let a_val = a_const_val.cast(output_int);
            let b_val = b_const_val.cast(output_int);

            let new_kind = match (a_val, b_val) {
                (Integer::Signed(a), Integer::Signed(b)) => {
                    Integer::Signed(arith_code.get_signed_binary_op()(a, b))
                }
                (Integer::Unsigned(a), Integer::Unsigned(b)) => {
                    Integer::Unsigned(arith_code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };

            ConstVal::Int(new_kind)
        }
        [ConstVal::Float(a_const_val), ConstVal::Float(b_const_val)] => {
            if b_const_val.0.is_zero() {
                return;
            }

            let TypeKind::Float(output_float) = output_type_info.kind else {
                unreachable!()
            };

            let a_val = a_const_val.cast(output_float);
            let b_val = b_const_val.cast(output_float);

            let new_kind = arith_code.get_float_binary_op()(a_val.0, b_val.0);
            let new_kind = Float(new_kind).cast(output_float);
            ConstVal::Float(new_kind)
        }

        [ConstVal::Uninitialized, _] | [_, ConstVal::Uninitialized] => ConstVal::Uninitialized,
        [ConstVal::Unknown, _] | [_, ConstVal::Unknown] => ConstVal::Unknown,
        _ => unreachable!(),
    };

    let output_value_id = op_data.outputs[0];
    stores.values.set_value_const(output_value_id, output_value);
}

pub(crate) fn subtract(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    arith_code: Arithmetic,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let input_const_vals = stores.values.value_consts(input_value_ids);
    let Some([output_type_id]) = stores.values.value_types([op_data.outputs[0]]) else {
        return;
    };
    let output_type_info = stores.types.get_type_info(output_type_id);

    let output_const_value = match input_const_vals {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };

            // Cast is already type checked.
            let a_kind = a.cast(output_int);
            let b_kind = b.cast(output_int);
            let kind = match (a_kind, b_kind) {
                (Integer::Signed(a), Integer::Signed(b)) => {
                    Integer::Signed(arith_code.get_signed_binary_op()(a, b))
                }
                (Integer::Unsigned(a), Integer::Unsigned(b)) => {
                    Integer::Unsigned(arith_code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };

            ConstVal::Int(kind)
        }

        [ConstVal::Float(a), ConstVal::Float(b)] => {
            let TypeKind::Float(output_float) = output_type_info.kind else {
                unreachable!()
            };

            // Cast is already type checked.
            let a_kind = a.cast(output_float);
            let b_kind = b.cast(output_float);
            let new_kind = arith_code.get_float_binary_op()(a_kind.0, b_kind.0);
            let new_kind = Float(new_kind).cast(output_float);

            ConstVal::Float(new_kind)
        }

        // Known pointer, constant offset.
        [ConstVal::Pointer {
            source_variable: id,
            offset,
        }, ConstVal::Int(Integer::Unsigned(v))] => ConstVal::Pointer {
            source_variable: *id,
            offset: offset.map(|off| off - v),
        },

        // Pointers with different known sources.
        // Clearly an error.
        [ConstVal::Pointer {
            source_variable: id1,
            ..
        }, ConstVal::Pointer {
            source_variable: id2,
            ..
        }] if id1 != id2 => {
            Diagnostic::error(op_loc, "subtracting pointers of different sources")
                .with_label_chain(input_value_ids[1], 1, "subtracting this...")
                .with_label_chain(input_value_ids[0], 0, "... from this")
                .attached(stores.diags, item_id);

            had_error.set();
            return;
        }

        // Pointers to the same known source, with known offsets.
        [ConstVal::Pointer {
            offset: Some(offset1),
            ..
        }, ConstVal::Pointer {
            offset: Some(offset2),
            ..
        }] => {
            if offset2 > offset1 {
                // Subtracting the end from the start.
                let offset1_label = format!("...from this offset: {offset1}");
                let offset2_label = format!("subtracting offset {offset2}...");

                Diagnostic::error(op_loc, "subtracting later pointer from earlier")
                    .with_label_chain(input_value_ids[0], 0, offset1_label)
                    .with_label_chain(input_value_ids[1], 1, offset2_label)
                    .attached(stores.diags, item_id);

                had_error.set();
                return;
            }

            ConstVal::Int(Integer::Unsigned(offset2 - offset1))
        }

        // Pointers with the same ID, but one or both have runtime offsets.
        [ConstVal::Pointer {
            source_variable: id,
            ..
        }, ConstVal::Pointer { .. }] => ConstVal::Pointer {
            source_variable: *id,
            offset: None,
        },

        [ConstVal::Uninitialized, _] | [_, ConstVal::Uninitialized] => ConstVal::Uninitialized,
        [ConstVal::Unknown, _] | [_, ConstVal::Unknown] => ConstVal::Unknown,
        _ => unreachable!(),
    };

    let output_value_id = op_data.outputs[0];
    stores
        .values
        .set_value_const(output_value_id, output_const_value);
}
