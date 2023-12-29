use ariadne::{Color, Label};

use crate::{
    diagnostics,
    n_ops::SliceNOps,
    opcode::{IntKind, Op},
    program::static_analysis::{promote_int_type_bidirectional, Analyzer, ConstVal},
    type_store::TypeKind,
    Stores,
};

pub fn compare(stores: &Stores, analyzer: &mut Analyzer, had_error: &mut bool, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let input_type_ids = analyzer.value_types(input_ids).unwrap();
    let Some(input_const_val) = analyzer.value_consts(input_ids) else {
        return;
    };

    let new_const_val = match input_const_val {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] =
                input_type_ids.map(|id| stores.types.get_type_info(id).kind)
            else {
                unreachable!()
            };

            // If we got here then the cast already type-checked.
            let (output_sign, output_width) = promote_int_type_bidirectional(a_int, b_int).unwrap();

            let a_kind = a.cast(output_width, output_sign);
            let b_kind = b.cast(output_width, output_sign);

            match (a_kind, b_kind) {
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    op.code.get_signed_binary_op()(a, b) != 0
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    op.code.get_unsigned_binary_op()(a, b) != 0
                }
                _ => unreachable!(),
            }
        }

        // Static pointers with different IDs.
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
                stores,
                op.token.location,
                "pointers have different sources",
                [
                    Label::new(op.token.location)
                        .with_color(Color::Yellow)
                        .with_message("here"),
                    Label::new(src_op1)
                        .with_color(Color::Cyan)
                        .with_message("...and this")
                        .with_order(2),
                    Label::new(src_op2)
                        .with_color(Color::Cyan)
                        .with_message("comparing this...")
                        .with_order(1),
                ],
                None,
            );
            *had_error = true;
            return;
        }

        // Static pointers with the same ID, but different static offsets.
        [ConstVal::Ptr {
            offset: Some(offset1),
            ..
        }, ConstVal::Ptr {
            offset: Some(offset2),
            ..
        }] => op.code.get_unsigned_binary_op()(offset1, offset2) != 0,

        _ => {
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, ConstVal::Bool(new_const_val));
}

pub fn equal(stores: &Stores, analyzer: &mut Analyzer, had_error: &mut bool, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(input_type_ids) = analyzer.value_types(input_ids) else {
        return;
    };
    let Some(input_const_vals) = analyzer.value_consts(input_ids) else {
        return;
    };

    let new_const_val = match input_const_vals {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let [TypeKind::Integer(a_int), TypeKind::Integer(b_int)] =
                input_type_ids.map(|id| stores.types.get_type_info(id).kind)
            else {
                unreachable!()
            };

            // If we got here then the cast already type-checked.
            let (output_sign, output_width) = promote_int_type_bidirectional(a_int, b_int).unwrap();

            // If we got here then the cast already type-checked.
            let a_kind = a.cast(output_width, output_sign);
            let b_kind = b.cast(output_width, output_sign);
            match (a_kind, b_kind) {
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    op.code.get_signed_binary_op()(a, b) != 0
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    op.code.get_unsigned_binary_op()(a, b) != 0
                }
                _ => unreachable!(),
            }
        }
        [ConstVal::Bool(a), ConstVal::Bool(b)] => op.code.get_bool_binary_op()(a, b),

        // Static pointers with different IDs.
        [ConstVal::Ptr {
            id: id1,
            src_op_loc: src_op1,
            ..
        }, ConstVal::Ptr {
            id: id2,
            src_op_loc: src_op2,
            ..
        }] if id1 != id2 => {
            *had_error = true;
            diagnostics::emit_error(
                stores,
                op.token.location,
                "pointers have different sources",
                [
                    Label::new(op.token.location)
                        .with_color(Color::Yellow)
                        .with_message("here"),
                    Label::new(src_op1)
                        .with_color(Color::Cyan)
                        .with_message("...and this")
                        .with_order(2),
                    Label::new(src_op2)
                        .with_color(Color::Cyan)
                        .with_message("comparing this...")
                        .with_order(1),
                ],
                None,
            );
            return;
        }

        // Static pointers with the same ID, but different static offsets.
        [ConstVal::Ptr {
            src_op_loc: src_op1,
            offset: Some(offset1),
            ..
        }, ConstVal::Ptr {
            src_op_loc: src_op2,
            offset: Some(offset2),
            ..
        }] => {
            if offset1 != offset2 {
                diagnostics::emit_warning(
                    stores,
                    op.token.location,
                    "pointers never equal",
                    [
                        Label::new(op.token.location)
                            .with_color(Color::Yellow)
                            .with_message("here"),
                        Label::new(src_op1)
                            .with_color(Color::Cyan)
                            .with_message("...and this")
                            .with_order(2),
                        Label::new(src_op2)
                            .with_color(Color::Cyan)
                            .with_message("comparing this...")
                            .with_order(1),
                    ],
                    None,
                );
                op.code.get_unsigned_binary_op()(0, 1) != 0
            } else {
                op.code.get_unsigned_binary_op()(1, 1) != 0
            }
        }

        _ => return,
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, ConstVal::Bool(new_const_val));
}

pub fn is_null(analyzer: &mut Analyzer, op: &Op) {
    let op_io = analyzer.get_op_io(op.id);
    let input_id = op_io.inputs()[0];
    if analyzer.value_consts([input_id]).is_none() {
        return;
    }

    let output_id = op_io.outputs()[0];
    analyzer.set_value_const(output_id, ConstVal::Bool(false));
}
