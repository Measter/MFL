use ariadne::{Color, Label};

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{Compare, IntKind, Op, TypeResolvedOp},
    n_ops::SliceNOps,
    pass_manager::static_analysis::{promote_int_type_bidirectional, Analyzer, ConstVal},
    type_store::TypeKind,
    Stores,
};

pub(crate) fn equal(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
    comp_code: Compare,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let input_type_ids = analyzer.value_types(input_value_ids).unwrap();
    let Some(input_const_vals) = analyzer.value_consts(input_value_ids) else {
        return;
    };

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
            match (a_kind, b_kind) {
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    comp_code.get_signed_binary_op()(a, b) != 0
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    comp_code.get_unsigned_binary_op()(a, b) != 0
                }

                _ => unreachable!(),
            }
        }

        [ConstVal::Bool(a), ConstVal::Bool(b)] => comp_code.get_bool_binary_op()(a, b),

        // Static pointers with different IDs.
        [ConstVal::Ptr { id: id1, .. }, ConstVal::Ptr { id: id2, .. }] if id1 != id2 => {
            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [
                    (input_value_ids[0], 0, "..and this"),
                    (input_value_ids[1], 1, "comparing this..."),
                ],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op.token.location,
                "pointers have different sources",
                labels,
                None,
            );

            had_error.set();
            return;
        }

        // Pointers with same IDs, but different static offsets.
        [ConstVal::Ptr {
            offset: Some(offset1),
            ..
        }, ConstVal::Ptr {
            offset: Some(offset2),
            ..
        }] => {
            let msg = if offset1 != offset2 {
                "pointers never equal"
            } else {
                "pointers always equal"
            };

            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [
                    (input_value_ids[0], 0, "..and this"),
                    (input_value_ids[1], 1, "comparing this..."),
                ],
                Color::Cyan,
                Color::Green,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Yellow));
            diagnostics::emit_error(stores, op.token.location, msg, labels, None);

            comp_code.get_unsigned_binary_op()(offset1, offset2) != 0
        }

        _ => return,
    };

    let output_value_id = op_data.outputs[0];
    analyzer.set_value_const(output_value_id, ConstVal::Bool(output_const_val));
}

pub(crate) fn compare(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
    comp_code: Compare,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let input_type_ids = analyzer.value_types(input_value_ids).unwrap();
    let Some(input_const_vals) = analyzer.value_consts(input_value_ids) else {
        return;
    };

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

            match (a_kind, b_kind) {
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    comp_code.get_signed_binary_op()(a, b) != 0
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    comp_code.get_unsigned_binary_op()(a, b) != 0
                }

                _ => unreachable!(),
            }
        }

        // Static pointers with different IDs.
        [ConstVal::Ptr { id: id1, .. }, ConstVal::Ptr { id: id2, .. }] if id1 != id2 => {
            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [
                    (input_value_ids[0], 0, "..and this"),
                    (input_value_ids[1], 1, "comparing this..."),
                ],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op.token.location,
                "pointers have different sources",
                labels,
                None,
            );

            had_error.set();
            return;
        }

        // Pointers with same IDs, but different static offsets.
        [ConstVal::Ptr {
            offset: Some(offset1),
            ..
        }, ConstVal::Ptr {
            offset: Some(offset2),
            ..
        }] => comp_code.get_unsigned_binary_op()(offset1, offset2) != 0,

        _ => return,
    };

    let output_value_value = op_data.outputs[0];
    analyzer.set_value_const(output_value_value, ConstVal::Bool(output_const_val));
}

pub(crate) fn is_null(analyzer: &mut Analyzer, op: &Op<TypeResolvedOp>) {
    let op_data = analyzer.get_op_io(op.id);
    let input_value_id = op_data.inputs[0];
    if analyzer.value_consts([input_value_id]).is_none() {
        return;
    }

    // We only have a const value from a statically known pointer, so it can't be null.
    let output_value_id = op_data.outputs[0];
    analyzer.set_value_const(output_value_id, ConstVal::Bool(false));
}