use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::{NOps, PopN},
    opcode::Op,
    source_file::SourceStorage,
    type_check::PorthTypeKind,
};

use super::{
    generate_stack_exhaustion_diag, generate_type_mismatch_diag, Analyzer, ConstVal, Value, ValueId,
};

pub(super) fn compare(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op_idx: usize,
    op: &Op,
) {
    for &value_id in stack.lastn(2).unwrap_or(&*stack) {
        analyzer.consume(value_id, op_idx);
    }

    let (inputs, new_type, const_val) = match stack.popn::<2>() {
        None => {
            generate_stack_exhaustion_diag(source_store, op, stack.len(), 2);
            *had_error = true;
            stack.clear();

            (None, PorthTypeKind::Unknown, None)
        }
        Some(vals) => {
            let (new_type, const_val) = match analyzer.get_values(vals) {
                type_pattern!(a @ PorthTypeKind::Int, b @ PorthTypeKind::Int)
                | type_pattern!(a @ PorthTypeKind::Ptr, b @ PorthTypeKind::Ptr) => {
                    (PorthTypeKind::Bool, (*a).zip(*b))
                }
                vals => {
                    // Type mismatch
                    *had_error = true;
                    if vals.iter().all(|v| v.porth_type != PorthTypeKind::Unknown) {
                        let lexeme = interner.resolve_lexeme(op.token.lexeme);
                        generate_type_mismatch_diag(source_store, lexeme, op, &vals);
                    }
                    (PorthTypeKind::Unknown, None)
                }
            };

            (Some(vals), new_type, const_val)
        }
    };

    let const_val = match const_val {
        Some((ConstVal::Int(a), ConstVal::Int(b))) => Some(op.code.get_binary_op()(a, b) != 0),

        // Static pointers with different IDs.
        Some((
            ConstVal::Ptr {
                id: a_id,
                src_op_loc: a_op,
                ..
            },
            ConstVal::Ptr {
                id: b_id,
                src_op_loc: b_op,
                ..
            },
        )) if a_id != b_id => {
            diagnostics::emit_error(
                op.token.location,
                "pointers have different sources",
                [
                    Label::new(op.token.location)
                        .with_color(Color::Yellow)
                        .with_message("here"),
                    Label::new(a_op)
                        .with_color(Color::Cyan)
                        .with_message("...and this")
                        .with_order(2),
                    Label::new(b_op)
                        .with_color(Color::Cyan)
                        .with_message("comparing this...")
                        .with_order(1),
                ],
                None,
                source_store,
            );
            Some(op.code.get_binary_op()(0, 1) != 0)
        }

        // Static pointers with the same ID, but different static offsets.
        Some((
            ConstVal::Ptr {
                offset: Some(off_a),
                ..
            },
            ConstVal::Ptr {
                offset: Some(off_b),
                ..
            },
        )) => Some(op.code.get_binary_op()(off_a, off_b) != 0),

        _ => None,
    };

    let (new_id, new_value) = analyzer.new_value(new_type, op_idx, op.token);
    new_value.const_val = const_val.map(ConstVal::Bool);

    let inputs = inputs.as_ref().map(|i| i.as_slice()).unwrap_or(&[]);
    analyzer.set_io(op_idx, op.token, inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn equal(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op_idx: usize,
    op: &Op,
) {
    for &value_id in stack.lastn(2).unwrap_or(&*stack) {
        analyzer.consume(value_id, op_idx);
    }
    let (inputs, new_type, const_val) = match stack.popn::<2>() {
        None => {
            generate_stack_exhaustion_diag(source_store, op, stack.len(), 2);
            *had_error = true;
            stack.clear();

            (None, PorthTypeKind::Unknown, None)
        }
        Some(vals) => {
            let (new_type, const_val) = match analyzer.get_values(vals) {
                type_pattern!(a @ PorthTypeKind::Bool, b @ PorthTypeKind::Bool)
                | type_pattern!(a @ PorthTypeKind::Ptr, b @ PorthTypeKind::Ptr)
                | type_pattern!(b @ PorthTypeKind::Int, a @ PorthTypeKind::Int) => {
                    (PorthTypeKind::Bool, (*a).zip(*b))
                }
                vals => {
                    // Type mismatch
                    *had_error = true;
                    // Don't emit an diagnostic here if any are Unknown, as it's a result of
                    // an earlier error.
                    if vals.iter().all(|v| v.porth_type != PorthTypeKind::Unknown) {
                        let lexeme = interner.resolve_lexeme(op.token.lexeme);
                        generate_type_mismatch_diag(source_store, lexeme, op, &vals);
                    }
                    (PorthTypeKind::Unknown, None)
                }
            };

            (Some(vals), new_type, const_val)
        }
    };

    let const_val = match const_val {
        Some((ConstVal::Int(a), ConstVal::Int(b))) => Some(op.code.get_binary_op()(a, b) != 0),
        Some((ConstVal::Bool(a), ConstVal::Bool(b))) => {
            Some(op.code.get_binary_op()(a as _, b as _) != 0)
        }

        // Static pointers with different IDs.
        Some((
            ConstVal::Ptr {
                id: a_id,
                src_op_loc: a_op,
                ..
            },
            ConstVal::Ptr {
                id: b_id,
                src_op_loc: b_op,
                ..
            },
        )) if a_id != b_id => {
            diagnostics::emit_error(
                op.token.location,
                "pointers have different sources",
                [
                    Label::new(op.token.location)
                        .with_color(Color::Yellow)
                        .with_message("here"),
                    Label::new(a_op)
                        .with_color(Color::Cyan)
                        .with_message("...and this")
                        .with_order(2),
                    Label::new(b_op)
                        .with_color(Color::Cyan)
                        .with_message("comparing this...")
                        .with_order(1),
                ],
                None,
                source_store,
            );
            Some(op.code.get_binary_op()(0, 1) != 0)
        }

        // Static pointers with the same ID, but different static offsets.
        Some((
            ConstVal::Ptr {
                src_op_loc: a_op,
                offset: Some(off_a),
                ..
            },
            ConstVal::Ptr {
                src_op_loc: b_op,
                offset: Some(off_b),
                ..
            },
        )) => {
            if off_a != off_b {
                diagnostics::emit_warning(
                    op.token.location,
                    "pointers never equal",
                    [
                        Label::new(op.token.location)
                            .with_color(Color::Yellow)
                            .with_message("here"),
                        Label::new(a_op)
                            .with_color(Color::Cyan)
                            .with_message("...and this")
                            .with_order(2),
                        Label::new(b_op)
                            .with_color(Color::Cyan)
                            .with_message("comparing this...")
                            .with_order(1),
                    ],
                    None,
                    source_store,
                );
                Some(op.code.get_binary_op()(0, 1) != 0)
            } else {
                Some(op.code.get_binary_op()(1, 1) != 0)
            }
        }

        _ => None,
    };

    let (new_id, new_value) = analyzer.new_value(new_type, op_idx, op.token);
    new_value.const_val = const_val.map(ConstVal::Bool);

    let inputs = inputs.as_ref().map(|i| i.as_slice()).unwrap_or(&[]);
    analyzer.set_io(op_idx, op.token, inputs, &[new_id]);
    stack.push(new_id);
}
