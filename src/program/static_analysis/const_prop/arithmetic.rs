use ariadne::{Color, Label};

use crate::{
    diagnostics,
    n_ops::SliceNOps,
    opcode::{Op, OpCode},
    program::static_analysis::{Analyzer, ConstVal},
    source_file::SourceStorage,
};

pub(super) fn add(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(types) = analyzer.value_consts(input_ids) else { return };

    let new_const_val = match types {
        [ConstVal::Int(a), ConstVal::Int(b)] => ConstVal::Int(a + b),

        // Const pointer with a constant offset.
        [ConstVal::Ptr {
            offset: Some(offset),
            id,
            src_op_loc,
        }, ConstVal::Int(v)] => ConstVal::Ptr {
            offset: Some(offset + v),
            id,
            src_op_loc,
        },
        // Const pointer with a constant offset.
        [ConstVal::Int(v), ConstVal::Ptr {
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

pub(super) fn subtract(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(types) = analyzer.value_consts(input_ids) else { return };

    let new_const_val = match types {
        [ConstVal::Int(a), ConstVal::Int(b)] => ConstVal::Int(a - b),

        // Static pointer, constant offset.
        [ConstVal::Ptr {
            id,
            src_op_loc,
            offset,
        }, ConstVal::Int(v)] => ConstVal::Ptr {
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
            } else {
                ConstVal::Int(offset2 - offset1)
            }
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

pub(super) fn bitnot(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs[0];
    let Some([types]) = analyzer.value_consts([input_id]) else { return };

    let new_const_val = match types {
        ConstVal::Int(a) => ConstVal::Int(!a),
        ConstVal::Bool(a) => ConstVal::Bool(!a),
        _ => return,
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, new_const_val);
}

pub(super) fn bitand_bitor(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(types) = analyzer.value_consts(input_ids) else { return };

    let new_const_val = match types {
        [ConstVal::Int(a), ConstVal::Int(b)] => match op.code {
            OpCode::BitAnd => ConstVal::Int(a & b),
            OpCode::BitOr => ConstVal::Int(a | b),
            _ => unreachable!(),
        },
        [ConstVal::Bool(a), ConstVal::Bool(b)] => match op.code {
            OpCode::BitAnd => ConstVal::Bool(a & b),
            OpCode::BitOr => ConstVal::Bool(a | b),
            _ => unreachable!(),
        },
        _ => return,
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, new_const_val);
}

pub(super) fn multiply_and_shift(analyzer: &mut Analyzer, source_store: &SourceStorage, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(types) = analyzer.value_consts(input_ids) else { return };

    if let (OpCode::ShiftLeft | OpCode::ShiftRight, ConstVal::Int(sv @ 64..)) = (&op.code, types[1])
    {
        let [shift_val] = analyzer.values([input_ids[1]]);
        diagnostics::emit_warning(
            op.token.location,
            "shift value exceeds 63",
            [
                Label::new(op.token.location)
                    .with_color(Color::Yellow)
                    .with_message("here"),
                Label::new(shift_val.creator_token.location)
                    .with_color(Color::Cyan)
                    .with_message("Shift value from here")
                    .with_order(1),
            ],
            format!("shift value ({sv}) will be masked to the lower 6 bits"),
            source_store,
        )
    }

    let new_const_val = match types {
        [ConstVal::Int(a), ConstVal::Int(b)] => match op.code {
            OpCode::Multiply => ConstVal::Int(a * b),
            OpCode::ShiftLeft => ConstVal::Int(a << b),
            OpCode::ShiftRight => ConstVal::Int(a >> b),
            _ => return,
        },
        _ => return,
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, new_const_val);
}

pub(super) fn divmod(analyzer: &mut Analyzer, source_store: &SourceStorage, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<2>();
    let Some(types) = analyzer.value_consts(input_ids) else { return };

    if let ConstVal::Int(0) = types[1] {
        let [div_val] = analyzer.values([input_ids[1]]);
        diagnostics::emit_error(
            op.token.location,
            "division by 0",
            [
                Label::new(op.token.location)
                    .with_color(Color::Red)
                    .with_message("division here"),
                Label::new(div_val.creator_token.location)
                    .with_color(Color::Cyan)
                    .with_message("divisor from here")
                    .with_order(1),
            ],
            None,
            source_store,
        )
    }

    let [new_quot_val, new_rem_val] = match types {
        [ConstVal::Int(a), ConstVal::Int(b @ 1..)] => [ConstVal::Int(a / b), ConstVal::Int(a % b)],
        _ => return,
    };

    let [quot_id, rem_id] = *op_data.outputs.as_arr::<2>();
    analyzer.set_value_const(quot_id, new_quot_val);
    analyzer.set_value_const(rem_id, new_rem_val);
}
