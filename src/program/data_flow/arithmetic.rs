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

pub(super) fn add(
    stack: &mut Vec<ValueId>,
    analyzer: &mut Analyzer,
    op_idx: usize,
    source_store: &SourceStorage,
    op: &Op,
    had_error: &mut bool,
    interner: &Interners,
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
                type_pattern!(a @ PorthTypeKind::Int, b @ PorthTypeKind::Int) => {
                    (PorthTypeKind::Int, (*a).zip(*b))
                }

                type_pattern!(a @ PorthTypeKind::Ptr, b @ PorthTypeKind::Int)
                | type_pattern!(b @ PorthTypeKind::Int, a @ PorthTypeKind::Ptr) => {
                    (PorthTypeKind::Ptr, (*a).zip(*b))
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
    let const_val = const_val.map(|mut cv| {
        match &mut cv {
            (ConstVal::Int(a), ConstVal::Int(b)) => *a += *b,

            // Static pointer with a constant offset.
            (
                ConstVal::Ptr {
                    offset: Some(offset),
                    ..
                },
                ConstVal::Int(v),
            ) => *offset += *v,

            // Static pointer with a runtime offset.
            (ConstVal::Ptr { .. }, ConstVal::Int(_)) => {}
            _ => unreachable!(),
        }
        cv.0
    });
    let (new_id, new_value) = analyzer.new_value(new_type, op_idx, op.token);
    new_value.const_val = const_val;

    let inputs = inputs.as_ref().map(|i| i.as_slice()).unwrap_or(&[]);
    analyzer.set_io(op_idx, op.token, inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn subtract(
    stack: &mut Vec<ValueId>,
    analyzer: &mut Analyzer,
    op_idx: usize,
    source_store: &SourceStorage,
    op: &Op,
    had_error: &mut bool,
    interner: &Interners,
) {
    for &value_id in stack.lastn(2).unwrap_or(&*stack) {
        analyzer.consume(value_id, op_idx);
    }
    let (inputs, new_type, const_val) = match stack.popn::<2>() {
        None => {
            generate_stack_exhaustion_diag(source_store, op, stack.len(), 2);
            *had_error = true;
            stack.clear();

            (None, PorthTypeKind::Unknown, (None, None))
        }
        Some(vals) => {
            let (new_type, const_val) = match analyzer.get_values(vals) {
                type_pattern!(a @ PorthTypeKind::Int, b @ PorthTypeKind::Int) => {
                    (PorthTypeKind::Int, (*a, *b))
                }
                type_pattern!(a @ PorthTypeKind::Ptr, b @ PorthTypeKind::Ptr) => {
                    (PorthTypeKind::Int, (*a, *b))
                }
                type_pattern!(b @ PorthTypeKind::Ptr, a @ PorthTypeKind::Int) => {
                    (PorthTypeKind::Ptr, (*a, *b))
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
                    (PorthTypeKind::Unknown, (None, None))
                }
            };
            (Some(vals), new_type, const_val)
        }
    };

    let const_val = match const_val {
        (Some(ConstVal::Int(a)), Some(ConstVal::Int(b))) => Some(ConstVal::Int(a - b)),

        // Static pointer, constant offset.
        // Note that we don't emit a diagnostic if we subtract out of bounds
        // because it could be part of a larger calculation.
        (
            Some(ConstVal::Ptr {
                id,
                offset,
                src_op_loc,
            }),
            Some(ConstVal::Int(v)),
        ) => Some(ConstVal::Ptr {
            id,
            src_op_loc,
            offset: offset.map(|off| off - v),
        }),

        // Static pointer, runtime offset.
        (Some(ConstVal::Ptr { id, src_op_loc, .. }), None) => Some(ConstVal::Ptr {
            id,
            src_op_loc,
            offset: None,
        }),

        // Pointers with differant static IDs.
        // Obviously an error.
        (
            Some(ConstVal::Ptr { id, src_op_loc, .. }),
            Some(ConstVal::Ptr {
                id: id2,
                src_op_loc: src_op_loc2,
                ..
            }),
        ) if id != id2 => {
            diagnostics::emit_error(
                op.token.location,
                "subtracting pointers of different sources",
                [
                    Label::new(op.token.location)
                        .with_color(Color::Red)
                        .with_message("here"),
                    Label::new(src_op_loc)
                        .with_color(Color::Cyan)
                        .with_message("...from this")
                        .with_order(2),
                    Label::new(src_op_loc2)
                        .with_color(Color::Cyan)
                        .with_message("subtracting this...")
                        .with_order(1),
                ],
                None,
                source_store,
            );
            *had_error = true;
            None
        }

        // Pointers with the same static ID, with constant offsets.
        (
            Some(ConstVal::Ptr {
                id,
                src_op_loc,
                offset: Some(offset),
                ..
            }),
            Some(ConstVal::Ptr {
                src_op_loc: src_op_loc2,
                offset: Some(offset2),
                ..
            }),
        ) => {
            if offset2 > offset {
                diagnostics::emit_error(
                    op.token.location,
                    "subtracting out of bounds",
                    [
                        Label::new(op.token.location)
                            .with_color(Color::Red)
                            .with_message("here"),
                        Label::new(src_op_loc)
                            .with_color(Color::Cyan)
                            .with_message(format!("...from this offset {}", offset))
                            .with_order(2),
                        Label::new(src_op_loc2)
                            .with_color(Color::Cyan)
                            .with_message(format!("subtracting offset {}...", offset2))
                            .with_order(1),
                    ],
                    None,
                    source_store,
                );
                *had_error = true;
                None
            } else {
                Some(ConstVal::Ptr {
                    id,
                    src_op_loc,
                    offset: Some(offset - offset2),
                })
            }
        }

        // Pointers with the same ID, but we have a runtime offset for one or both.
        (Some(ConstVal::Ptr { id, src_op_loc, .. }), Some(ConstVal::Ptr { .. })) => {
            Some(ConstVal::Ptr {
                id,
                src_op_loc,
                offset: None,
            })
        }

        _ => None,
    };

    let (new_id, new_value) = analyzer.new_value(new_type, op_idx, op.token);
    new_value.const_val = const_val;

    let inputs = inputs.as_ref().map(|i| i.as_slice()).unwrap_or(&[]);
    analyzer.set_io(op_idx, op.token, inputs, &[new_id]);

    stack.push(new_id);
}
