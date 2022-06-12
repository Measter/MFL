use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{Analyzer, ConstVal, ValueId},
    source_file::SourceStorage,
};

use super::check_allowed_const;

pub(super) fn compare(
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
        [ConstVal::Int(a), ConstVal::Int(b)] => op.code.get_binary_op()(a, b) != 0,

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
                source_store,
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
        }] => op.code.get_binary_op()(offset1, offset2) != 0,

        _ => {
            return;
        }
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, ConstVal::Bool(new_const_val));
}

pub(super) fn equal(
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
        [ConstVal::Int(a), ConstVal::Int(b)] => op.code.get_binary_op()(a, b) != 0,
        [ConstVal::Bool(a), ConstVal::Bool(b)] => op.code.get_binary_op()(a as _, b as _) != 0,

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
                source_store,
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
                    source_store,
                );
                op.code.get_binary_op()(0, 1) != 0
            } else {
                op.code.get_binary_op()(1, 1) != 0
            }
        }

        _ => return,
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, ConstVal::Bool(new_const_val));
}
