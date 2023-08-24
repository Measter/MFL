use ariadne::{Color, Label};

use crate::{
    diagnostics,
    n_ops::SliceNOps,
    opcode::{IntKind, Op, OpCode},
    program::static_analysis::{Analyzer, ConstVal},
    source_file::SourceStorage,
    type_store::{TypeKind, TypeStore},
};

pub fn add(analyzer: &mut Analyzer, type_store: &TypeStore, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let val_ids = *op_data.inputs.as_arr::<2>();
    let Some([output_type_id]) = analyzer.value_types([op_data.outputs()[0]]) else {
        return;
    };
    let output_type_info = type_store.get_type_info(output_type_id);
    let Some(input_const_vals) = analyzer.value_consts(val_ids) else {
        return;
    };

    let new_const_val = match input_const_vals {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let TypeKind::Integer {
                width: output_width,
                signed: output_signed,
            } = output_type_info.kind
            else {
                unreachable!()
            };

            // If we got here then the cast already type-checked.
            let a_kind = a.cast(output_width, output_signed);
            let b_kind = b.cast(output_width, output_signed);
            let kind = match (a_kind, b_kind) {
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    IntKind::Signed(op.code.get_signed_binary_op()(a, b))
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    IntKind::Unsigned(op.code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };

            ConstVal::Int(kind)
        }

        // Const pointer with a constant offset.
        [ConstVal::Ptr {
            offset: Some(offset),
            id,
            src_op_loc,
        }, ConstVal::Int(IntKind::Unsigned(v))] => ConstVal::Ptr {
            offset: Some(offset + v),
            id,
            src_op_loc,
        },
        // Const pointer with a constant offset.
        [ConstVal::Int(IntKind::Unsigned(v)), ConstVal::Ptr {
            offset: Some(offset),
            id,
            src_op_loc,
        }] => ConstVal::Ptr {
            offset: Some(offset + v),
            id,
            src_op_loc,
        },

        _ => return,
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, new_const_val);
}

pub fn subtract(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(input_const_vals) = analyzer.value_consts(input_ids) else {
        return;
    };
    let Some([output_type_id]) = analyzer.value_types([op_data.outputs()[0]]) else {
        unreachable!()
    };
    let output_type_info = type_store.get_type_info(output_type_id);

    let new_const_val = match input_const_vals {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let TypeKind::Integer {
                width: output_width,
                signed: output_signed,
            } = output_type_info.kind
            else {
                unreachable!()
            };

            // If we got here then the cast already type-checked.
            let a_kind = a.cast(output_width, output_signed);
            let b_kind = b.cast(output_width, output_signed);
            let kind = match (a_kind, b_kind) {
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    IntKind::Signed(op.code.get_signed_binary_op()(a, b))
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    IntKind::Unsigned(op.code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };
            ConstVal::Int(kind)
        }

        // Static pointer, constant offset.
        [ConstVal::Ptr {
            id,
            src_op_loc,
            offset,
        }, ConstVal::Int(IntKind::Unsigned(v))] => ConstVal::Ptr {
            id,
            src_op_loc,
            offset: offset.map(|off| off - v),
        },

        // Pointers with different const sources.
        // Clearly and error.
        [ConstVal::Ptr {
            id: id1,
            src_op_loc: src_op1,
            ..
        }, ConstVal::Ptr {
            id: id2,
            src_op_loc: src_op2,
            ..
        }] if id1 != id2 => {
            diagnostics::emit_error(
                op.token.location,
                "subtracting pointers of different sources",
                [
                    Label::new(op.token.location)
                        .with_color(Color::Red)
                        .with_message("here"),
                    Label::new(src_op1)
                        .with_color(Color::Cyan)
                        .with_message("...from this")
                        .with_order(2),
                    Label::new(src_op2)
                        .with_color(Color::Cyan)
                        .with_message("subtracting this...")
                        .with_order(1),
                ],
                None,
                source_store,
            );
            *had_error = true;
            return;
        }

        // Pointers with the same static ID, with constant offsets.
        [ConstVal::Ptr {
            src_op_loc: src_op1,
            offset: Some(offset1),
            ..
        }, ConstVal::Ptr {
            src_op_loc: src_op2,
            offset: Some(offset2),
            ..
        }] => {
            if offset2 > offset1 {
                // Subtracting the end from the start.
                diagnostics::emit_error(
                    op.token.location,
                    "subtracting end from start",
                    [
                        Label::new(op.token.location)
                            .with_color(Color::Red)
                            .with_message("here"),
                        Label::new(src_op1)
                            .with_color(Color::Cyan)
                            .with_message(format!("...from this offset {offset1}"))
                            .with_order(2),
                        Label::new(src_op2)
                            .with_color(Color::Cyan)
                            .with_message(format!("subtracting offset {offset2}..."))
                            .with_order(1),
                    ],
                    None,
                    source_store,
                );
                *had_error = true;
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

        _ => return,
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, new_const_val);
}

pub fn bitnot(analyzer: &mut Analyzer, type_store: &TypeStore, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs[0];
    let Some([types]) = analyzer.value_consts([input_id]) else {
        return;
    };
    let Some([output_type_id]) = analyzer.value_types([op_data.outputs()[0]]) else {
        unreachable!()
    };
    let output_type_info = type_store.get_type_info(output_type_id);
    let TypeKind::Integer {
        width: output_width,
        ..
    } = output_type_info.kind
    else {
        unreachable!()
    };

    let new_const_val = match types {
        ConstVal::Int(IntKind::Unsigned(a)) => {
            ConstVal::Int(IntKind::Unsigned((!a) & output_width.mask()))
        }
        ConstVal::Int(IntKind::Signed(a)) => {
            ConstVal::Int(IntKind::Signed((!a) & output_width.mask() as i64))
        }
        ConstVal::Bool(a) => ConstVal::Bool(!a),
        _ => return,
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, new_const_val);
}

pub fn bitand_bitor_bitxor(analyzer: &mut Analyzer, type_store: &TypeStore, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(input_const_vals) = analyzer.value_consts(input_ids) else {
        return;
    };
    let Some([output_type_id]) = analyzer.value_types([op_data.outputs()[0]]) else {
        return;
    };
    let output_type_info = type_store.get_type_info(output_type_id);

    let new_const_val = match input_const_vals {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let TypeKind::Integer {
                width: output_width,
                signed: output_signed,
            } = output_type_info.kind
            else {
                unreachable!()
            };

            // If we got here then the cast already type-checked.
            let a_kind = a.cast(output_width, output_signed);
            let b_kind = b.cast(output_width, output_signed);
            let kind = match (a_kind, b_kind) {
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    IntKind::Signed(op.code.get_signed_binary_op()(a, b))
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    IntKind::Unsigned(op.code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };

            ConstVal::Int(kind)
        }
        [ConstVal::Bool(a), ConstVal::Bool(b)] => {
            ConstVal::Bool(op.code.get_bool_binary_op()(a, b))
        }
        _ => return,
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, new_const_val);
}

pub fn multiply_div_rem_shift(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();

    let Some([output_type_id]) = analyzer.value_types([op_data.outputs()[0]]) else {
        return;
    };
    let output_type_info = type_store.get_type_info(output_type_id);
    let TypeKind::Integer {
        width: output_width,
        signed: output_sign,
    } = output_type_info.kind
    else {
        unreachable!()
    };

    let Some([ConstVal::Int(a_const_val), ConstVal::Int(b_const_val)]) =
        analyzer.value_consts(input_ids)
    else {
        return;
    };

    if matches!(&op.code, OpCode::ShiftLeft | OpCode::ShiftRight) {
        let shift_amount = match b_const_val {
            IntKind::Signed(v) => v as u8,
            IntKind::Unsigned(v) => v as u8,
        };

        if shift_amount > 63 {
            let [shift_val] = analyzer.values([input_ids[1]]);
            diagnostics::emit_warning(
                op.token.location,
                "shift value exceeds 63",
                [
                    Label::new(op.token.location)
                        .with_color(Color::Yellow)
                        .with_message("here"),
                    Label::new(shift_val.source_location)
                        .with_color(Color::Cyan)
                        .with_message("Shift value from here")
                        .with_order(1),
                ],
                format!("shift value ({shift_amount}) will be masked to the lower 6 bits"),
                source_store,
            );
        }

        if (shift_amount & 63) >= output_width.bit_width() {
            let [shift_val] = analyzer.values([input_ids[1]]);
            diagnostics::emit_warning(
                op.token.location,
                "shift value exceeds 63",
                [
                    Label::new(op.token.location)
                        .with_color(Color::Yellow)
                        .with_message("here"),
                    Label::new(shift_val.source_location)
                        .with_color(Color::Cyan)
                        .with_message("Shift value from here")
                        .with_order(1),
                ],
                format!("shift value ({shift_amount}) exceeds width"),
                source_store,
            );
        }
    } else if matches!(&op.code, OpCode::Div | OpCode::Rem) {
        let div_amount = match b_const_val {
            IntKind::Signed(v) => v as u64,
            IntKind::Unsigned(v) => v,
        };
        if div_amount == 0 {
            let [div_val] = analyzer.values([input_ids[1]]);
            diagnostics::emit_error(
                op.token.location,
                "division by 0",
                [
                    Label::new(op.token.location).with_color(Color::Red),
                    Label::new(div_val.source_location)
                        .with_color(Color::Cyan)
                        .with_message("divisor from here")
                        .with_order(1),
                ],
                None,
                source_store,
            );
            *had_error = true;
            return;
        }
    }
    let a_val = a_const_val.cast(output_width, output_sign);
    let b_val = b_const_val.cast(output_width, output_sign);

    let new_kind = match (a_val, b_val) {
        (IntKind::Signed(a), IntKind::Signed(b)) => {
            IntKind::Signed(op.code.get_signed_binary_op()(a, b))
        }
        (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
            IntKind::Unsigned(op.code.get_unsigned_binary_op()(a, b))
        }
        _ => unreachable!(),
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, ConstVal::Int(new_kind));
}
