use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::NOps,
    opcode::Op,
    program::static_analysis::{Analyzer, ConstVal, Value, ValueId},
    source_file::SourceStorage,
};

use super::check_allowed_const;

pub(super) fn add(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);

    let input_ids = *op_data.inputs.as_arr::<2>();
    if !check_allowed_const(input_ids, force_non_const_before) {
        return;
    }

    let Some(types) = analyzer.value_consts(input_ids) else {return};

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
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);

    let input_ids = *op_data.inputs.as_arr::<2>();
    if !check_allowed_const(input_ids, force_non_const_before) {
        return;
    }

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
            id: id1,
            src_op_loc: src_op1,
            offset: Some(offset1),
        }, ConstVal::Ptr {
            id: id2,
            src_op_loc: src_op2,
            offset: Some(offset2),
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
                            .with_message(format!("...from this offset {}", offset1))
                            .with_order(2),
                        Label::new(src_op2)
                            .with_color(Color::Cyan)
                            .with_message(format!("subtracting offset {}...", offset2))
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

pub(super) fn bitnot(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn bitand_bitor(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn multiply_and_shift(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn divmod(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}
