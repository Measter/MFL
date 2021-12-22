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
    for value_id in stack.lastn(2).unwrap_or(&*stack) {
        let value = analyzer.values.get_mut(value_id).unwrap();
        value.consumer = Some(op_idx);
    }
    let (new_type, const_val) = match stack.popn::<2>() {
        None => {
            generate_stack_exhaustion_diag(source_store, op, stack.len(), 2);
            *had_error = true;

            (PorthTypeKind::Unknown, None)
        }
        Some(vals) => {
            let new_tv = match analyzer.get_values(vals) {
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

            new_tv
        }
    };
    let const_val = const_val.map(|mut cv| {
        match &mut cv {
            (ConstVal::Int(a), ConstVal::Int(b)) => *a += *b,
            (ConstVal::Ptr { offset, .. }, ConstVal::Int(v)) => *offset += *v,
            _ => unreachable!(),
        }
        cv.0
    });
    let (new_id, new_value) = analyzer.new_value(new_type, op_idx, op.token);
    new_value.const_val = const_val;
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
    for value_id in stack.lastn(2).unwrap_or(&*stack) {
        let value = analyzer.values.get_mut(value_id).unwrap();
        value.consumer = Some(op_idx);
    }
    let (new_type, const_val) = match stack.popn::<2>() {
        None => {
            generate_stack_exhaustion_diag(source_store, op, stack.len(), 2);
            *had_error = true;

            (PorthTypeKind::Unknown, None)
        }
        Some(vals) => {
            let new_tv = match analyzer.get_values(vals) {
                type_pattern!(a @ PorthTypeKind::Int, b @ PorthTypeKind::Int) => {
                    (PorthTypeKind::Int, (*a).zip(*b))
                }
                type_pattern!(a @ PorthTypeKind::Ptr, b @ PorthTypeKind::Ptr) => {
                    (PorthTypeKind::Int, (*a).zip(*b))
                }
                type_pattern!(b @ PorthTypeKind::Ptr, a @ PorthTypeKind::Int) => {
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
            new_tv
        }
    };

    let const_val = const_val.map(|mut cv| {
        match &mut cv {
            (ConstVal::Int(a), ConstVal::Int(b)) => *a -= *b,
            (ConstVal::Ptr { offset, .. }, ConstVal::Int(v)) => *offset -= *v,
            (
                ConstVal::Ptr {
                    id,
                    source_op_location,
                    offset,
                    ..
                },
                ConstVal::Ptr {
                    id: id2,
                    source_op_location: source_op_location2,
                    offset: offset2,
                    ..
                },
            ) => {
                if id != id2 {
                    diagnostics::emit(
                        op.token.location,
                        "subtracting pointers of different sources",
                        [
                            Label::new(op.token.location)
                                .with_color(Color::Red)
                                .with_message("here"),
                            Label::new(*source_op_location)
                                .with_color(Color::Cyan)
                                .with_message("...from this")
                                .with_order(2),
                            Label::new(*source_op_location2)
                                .with_color(Color::Cyan)
                                .with_message("subtracting this...")
                                .with_order(1),
                        ],
                        None,
                        source_store,
                    );
                    *had_error = true;
                } else if offset2 > offset {
                    diagnostics::emit(
                        op.token.location,
                        "subtracting out of bounds",
                        [
                            Label::new(op.token.location)
                                .with_color(Color::Red)
                                .with_message("here"),
                            Label::new(*source_op_location)
                                .with_color(Color::Cyan)
                                .with_message(format!("...from this offset {}", offset))
                                .with_order(2),
                            Label::new(*source_op_location2)
                                .with_color(Color::Cyan)
                                .with_message(format!("subtracting offset {}...", offset2))
                                .with_order(1),
                        ],
                        None,
                        source_store,
                    );
                    *had_error = true;
                } else {
                    *offset -= *offset2;
                }
            }
            _ => unreachable!(),
        }
        cv.0
    });
    let (new_id, new_value) = analyzer.new_value(new_type, op_idx, op.token);
    new_value.const_val = const_val;
    stack.push(new_id);
}
