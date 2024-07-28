use ariadne::{Color, Label};

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{Arithmetic, IntKind},
    n_ops::SliceNOps,
    stores::{analyzer::ConstVal, ops::OpId, types::TypeKind},
    Stores,
};

pub(crate) fn add(stores: &mut Stores, op_id: OpId, arith_code: Arithmetic) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let Some([output_type_id]) = stores.values.value_types([op_data.outputs[0]]) else {
        return;
    };
    let output_type_info = stores.types.get_type_info(output_type_id);
    let Some(input_const_values) = stores.values.value_consts(input_value_ids) else {
        return;
    };

    let new_const_val = match input_const_values {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };

            // The cast has already been type checked.
            let a_kind = a.cast(output_int);
            let b_kind = b.cast(output_int);
            let kind = match (a_kind, b_kind) {
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    IntKind::Signed(arith_code.get_signed_binary_op()(a, b))
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    IntKind::Unsigned(arith_code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };

            ConstVal::Int(kind)
        }

        // Pointer offset.
        [ConstVal::Ptr {
            id,
            src_op_loc,
            offset: Some(offset),
        }, ConstVal::Int(IntKind::Unsigned(v))]
        | [ConstVal::Int(IntKind::Unsigned(v)), ConstVal::Ptr {
            id,
            src_op_loc,
            offset: Some(offset),
        }] => ConstVal::Ptr {
            id,
            src_op_loc,
            offset: Some(offset + v),
        },
        _ => return,
    };

    let output_id = op_data.outputs[0];
    stores.values.set_value_const(output_id, new_const_val);
}

pub(crate) fn bitand_bitor_bitxor(stores: &mut Stores, op_id: OpId, arith_code: Arithmetic) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let Some(input_const_vals) = stores.values.value_consts(input_value_ids) else {
        return;
    };
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
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    IntKind::Signed(arith_code.get_signed_binary_op()(a, b))
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    IntKind::Unsigned(arith_code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };

            ConstVal::Int(kind)
        }
        [ConstVal::Bool(a), ConstVal::Bool(b)] => {
            ConstVal::Bool(arith_code.get_bool_binary_op()(a, b))
        }
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
    let Some([input_const_val]) = stores.values.value_consts([input_value_id]) else {
        return;
    };
    let Some([output_type_id]) = stores.values.value_types([op_data.outputs[0]]) else {
        return;
    };
    let output_type_info = stores.types.get_type_info(output_type_id);

    let output_const_val = match input_const_val {
        ConstVal::Int(IntKind::Unsigned(a)) => {
            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };
            ConstVal::Int(IntKind::Unsigned((!a) & output_int.width.mask()))
        }
        ConstVal::Int(IntKind::Signed(a)) => {
            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };
            ConstVal::Int(IntKind::Signed((!a) & output_int.width.mask() as i64))
        }
        ConstVal::Bool(b) => ConstVal::Bool(!b),
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
    let TypeKind::Integer(output_int) = output_type_info.kind else {
        unreachable!()
    };

    let Some([ConstVal::Int(a_const_val), ConstVal::Int(b_const_val)]) =
        stores.values.value_consts(input_value_ids)
    else {
        return;
    };

    match arith_code {
        Arithmetic::ShiftLeft | Arithmetic::ShiftRight => {
            let (is_out_of_range, shift_value_string) = match b_const_val {
                IntKind::Signed(v @ 0..) if v < output_int.width.bit_width() as _ => {
                    (false, String::new())
                }
                IntKind::Unsigned(v @ 0..) if v < output_int.width.bit_width() as _ => {
                    (false, String::new())
                }

                IntKind::Signed(v) => (true, v.to_string()),
                IntKind::Unsigned(v) => (true, v.to_string()),
            };

            if is_out_of_range {
                let output_type_name = stores.strings.resolve(output_type_info.friendly_name);

                let mut labels = diagnostics::build_creator_label_chain(
                    stores,
                    [(input_value_ids[1], 0, "shift value from here")],
                    Color::Cyan,
                    Color::Green,
                );
                labels.push(Label::new(op_loc).with_color(Color::Yellow));
                diagnostics::emit_warning(
                    stores,
                    op_loc,
                    "shift value out of range",
                    labels,
                    format!(
                        "shift value ({shift_value_string}) masked to the width of a {output_type_name}"
                    ),
                );
            }
        }

        Arithmetic::Div | Arithmetic::Rem => {
            let div_is_zero = matches!(b_const_val, IntKind::Signed(0) | IntKind::Unsigned(0));
            if div_is_zero {
                let mut labels = diagnostics::build_creator_label_chain(
                    stores,
                    [(input_value_ids[1], 0, "divisor value from here")],
                    Color::Cyan,
                    Color::Green,
                );
                labels.push(Label::new(op_loc).with_color(Color::Yellow));
                diagnostics::emit_error(stores, op_loc, "division by 0", labels, None);

                had_error.set();
                return;
            }
        }

        _ => unreachable!(),
    }

    let a_val = a_const_val.cast(output_int);
    let b_val = b_const_val.cast(output_int);

    let new_kind = match (a_val, b_val) {
        (IntKind::Signed(a), IntKind::Signed(b)) => {
            IntKind::Signed(arith_code.get_signed_binary_op()(a, b))
        }
        (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
            IntKind::Unsigned(arith_code.get_unsigned_binary_op()(a, b))
        }
        _ => unreachable!(),
    };

    let output_value_id = op_data.outputs[0];
    stores
        .values
        .set_value_const(output_value_id, ConstVal::Int(new_kind));
}

pub(crate) fn subtract(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    arith_code: Arithmetic,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let Some(input_const_vals) = stores.values.value_consts(input_value_ids) else {
        return;
    };
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
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    IntKind::Signed(arith_code.get_signed_binary_op()(a, b))
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    IntKind::Unsigned(arith_code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };

            ConstVal::Int(kind)
        }

        // Known pointer, constant offset.
        [ConstVal::Ptr {
            id,
            src_op_loc,
            offset,
        }, ConstVal::Int(IntKind::Unsigned(v))] => ConstVal::Ptr {
            id,
            src_op_loc,
            offset: offset.map(|off| off - v),
        },

        // Pointers with different known sources.
        // Clearly an error.
        [ConstVal::Ptr { id: id1, .. }, ConstVal::Ptr { id: id2, .. }] if id1 != id2 => {
            let mut labels = diagnostics::build_creator_label_chain(
                stores,
                [
                    (input_value_ids[0], 0, "...from this"),
                    (input_value_ids[1], 1, "sutracting this..."),
                ],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(op_loc).with_color(Color::Red));
            diagnostics::emit_error(
                stores,
                op_loc,
                "subtracting pointers of different sources",
                labels,
                None,
            );

            had_error.set();
            return;
        }

        // Pointers to the same known source, with known offsets.
        [ConstVal::Ptr {
            offset: Some(offset1),
            ..
        }, ConstVal::Ptr {
            offset: Some(offset2),
            ..
        }] => {
            if offset2 > offset1 {
                // Subtracting the end from the start.
                let offset1_label = format!("...from this offset: {offset1}");
                let offset2_label = format!("subtracting offset {offset2}...");

                let mut labels = diagnostics::build_creator_label_chain(
                    stores,
                    [
                        (input_value_ids[0], 0, offset1_label.as_str()),
                        (input_value_ids[1], 1, offset2_label.as_str()),
                    ],
                    Color::Yellow,
                    Color::Cyan,
                );
                labels.push(Label::new(op_loc).with_color(Color::Red));

                diagnostics::emit_error(
                    stores,
                    op_loc,
                    "subtracting end of array from start",
                    labels,
                    None,
                );

                had_error.set();
                return;
            }

            ConstVal::Int(IntKind::Unsigned(offset2 - offset1))
        }

        // Pointers with the same ID, but one or both have runtime offsets.
        [ConstVal::Ptr { id, src_op_loc, .. }, ConstVal::Ptr { .. }] => ConstVal::Ptr {
            id,
            src_op_loc,
            offset: None,
        },

        _ => unreachable!(),
    };

    let output_value_id = op_data.outputs[0];
    stores
        .values
        .set_value_const(output_value_id, output_const_value);
}
