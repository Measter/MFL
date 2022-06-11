use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::{NOps, PopN},
    opcode::{Op, OpCode},
    source_file::SourceStorage,
};

use super::{
    super::{
        generate_stack_length_mismatch_diag, generate_type_mismatch_diag, Analyzer, ConstVal,
        Value, ValueId,
    },
    ensure_stack_depth,
};

pub(super) fn eat_two_make_one(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }
    let new_id = analyzer.new_value(op);

    analyzer.set_op_io(op.id, op.token, &inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn bitand_bitor(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    for &value_id in stack.lastn(2).unwrap_or(&*stack) {
        analyzer.consume(value_id, op.id);
    }

    let (inputs, new_type, const_val) = match stack.popn::<2>() {
        None => {
            generate_stack_length_mismatch_diag(
                source_store,
                op,
                op.token.location,
                stack.len(),
                2,
            );
            *had_error = true;
            stack.clear();

            (None, PorthTypeKind::Unknown, None)
        }
        Some(vals) => {
            let (new_type, const_val) = match analyzer.get_values(vals) {
                type_pattern!(a @ PorthTypeKind::Int, b @ PorthTypeKind::Int) => {
                    (PorthTypeKind::Int, (*a).zip(*b))
                }
                type_pattern!(a @ PorthTypeKind::Bool, b @ PorthTypeKind::Bool) => {
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

    let allow_const = check_allowed_const(inputs, force_non_const_before);

    let const_val = if allow_const {
        const_val.map(|mut cv| {
            match &mut cv {
                (ConstVal::Int(a), ConstVal::Int(b)) => match op.code {
                    OpCode::BitAnd => *a &= *b,
                    OpCode::BitOr => *a |= *b,
                    _ => unreachable!(),
                },
                (ConstVal::Bool(a), ConstVal::Bool(b)) => match op.code {
                    OpCode::BitAnd => *a &= *b,
                    OpCode::BitOr => *a |= *b,
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            }
            cv.0
        })
    } else {
        None
    };

    let (new_id, new_val) = analyzer.new_value(new_type, op.id, op.token);
    new_val.const_val = const_val;

    let inputs = inputs.as_ref().map(|i| i.as_slice()).unwrap_or(&[]);
    analyzer.set_io(op.id, op.token, inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn bitnot(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    if let Some(&value_id) = stack.last() {
        analyzer.consume(value_id, op.id);
    }

    let (inputs, new_type, const_val) = match stack.pop() {
        None => {
            generate_stack_length_mismatch_diag(
                source_store,
                op,
                op.token.location,
                stack.len(),
                2,
            );
            *had_error = true;
            stack.clear();

            (None, PorthTypeKind::Unknown, None)
        }
        Some(val) => {
            let (new_type, const_val) = match analyzer.get_values([val]) {
                type_pattern!(a @ PorthTypeKind::Int) => (PorthTypeKind::Int, *a),
                type_pattern!(a @ PorthTypeKind::Bool) => (PorthTypeKind::Bool, *a),
                [val] => {
                    // Type mismatch
                    *had_error = true;
                    if val.porth_type != PorthTypeKind::Unknown {
                        let lexeme = interner.resolve_lexeme(op.token.lexeme);
                        generate_type_mismatch_diag(source_store, lexeme, op, &[val]);
                    }
                    (PorthTypeKind::Unknown, None)
                }
            };

            (Some(val), new_type, const_val)
        }
    };

    let allow_const = check_allowed_const(inputs.map(|a| [a]), force_non_const_before);

    let const_val = if allow_const {
        const_val.map(|cv| match cv {
            ConstVal::Int(a) => ConstVal::Int(!a),
            ConstVal::Bool(a) => ConstVal::Bool(!a),
            _ => unreachable!(),
        })
    } else {
        None
    };

    let (new_id, new_val) = analyzer.new_value(new_type, op.id, op.token);
    new_val.const_val = const_val;

    let inputs = inputs.as_ref().map(std::slice::from_ref).unwrap_or(&[]);
    analyzer.set_io(op.id, op.token, inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn divmod(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    for &value_id in stack.lastn(2).unwrap_or(&*stack) {
        analyzer.consume(value_id, op.id);
    }
    let (inputs, new_type, const_val) = match stack.popn::<2>() {
        None => {
            generate_stack_length_mismatch_diag(
                source_store,
                op,
                op.token.location,
                stack.len(),
                2,
            );
            *had_error = true;
            stack.clear();
            (None, PorthTypeKind::Unknown, (None, None))
        }
        Some(vals) => {
            let (new_type, const_val) = match analyzer.get_values(vals) {
                type_pattern!(a @ PorthTypeKind::Int, b @ PorthTypeKind::Int) => {
                    (PorthTypeKind::Int, (*a, *b))
                }
                vals => {
                    // Type mismatch
                    *had_error = true;
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

    let allow_const = check_allowed_const(inputs, force_non_const_before);

    if let Some(ConstVal::Int(0)) = const_val.1 {
        let [div_val] = analyzer.get_values([inputs.unwrap()[1]]);
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

    let (quot_const_val, rem_const_val) = if allow_const {
        match const_val {
            (Some(ConstVal::Int(a)), Some(ConstVal::Int(b @ 1..))) => {
                (Some(ConstVal::Int(a / b)), Some(ConstVal::Int(a % b)))
            }
            _ => (None, None),
        }
    } else {
        (None, None)
    };

    let (quot_id, quot_val) = analyzer.new_value(new_type, op.id, op.token);
    quot_val.const_val = quot_const_val;
    let (rem_id, rem_val) = analyzer.new_value(new_type, op.id, op.token);
    rem_val.const_val = rem_const_val;

    let inputs = inputs.as_ref().map(|i| i.as_slice()).unwrap_or(&[]);
    analyzer.set_io(op.id, op.token, inputs, &[quot_id, rem_id]);
    stack.push(quot_id);
    stack.push(rem_id);
}

pub(super) fn multiply_and_shift(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    for &value_id in stack.lastn(2).unwrap_or(&*stack) {
        analyzer.consume(value_id, op.id);
    }
    let (inputs, new_type, const_val) = match stack.popn::<2>() {
        None => {
            generate_stack_length_mismatch_diag(
                source_store,
                op,
                op.token.location,
                stack.len(),
                2,
            );
            *had_error = true;
            stack.clear();
            (None, PorthTypeKind::Unknown, (None, None))
        }
        Some(vals) => {
            let (new_type, const_val) = match analyzer.get_values(vals) {
                type_pattern!(a @ PorthTypeKind::Int, b @ PorthTypeKind::Int) => {
                    (PorthTypeKind::Int, (*a, *b))
                }
                vals => {
                    // Type mismatch
                    *had_error = true;
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

    let allow_const = check_allowed_const(inputs, force_non_const_before);

    if let (OpCode::ShiftLeft | OpCode::ShiftRight, Some(ConstVal::Int(sv @ 64..))) =
        (&op.code, const_val.1)
    {
        let [shift_val] = analyzer.get_values([inputs.unwrap()[1]]);
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
            format!("shift value ({}) will be masked to the lower 6 bits", sv),
            source_store,
        )
    }

    let const_val = if allow_const {
        match const_val {
            (Some(ConstVal::Int(a)), Some(ConstVal::Int(b))) => {
                match op.code {
                    OpCode::Multiply => Some(ConstVal::Int(a * b)),
                    OpCode::ShiftLeft => Some(ConstVal::Int(a << b)),
                    OpCode::ShiftRight => Some(ConstVal::Int(a >> b)),
                    _ => unreachable!(),
                }
                //
            }
            _ => None,
        }
    } else {
        None
    };

    let (new_id, new_value) = analyzer.new_value(new_type, op.id, op.token);
    new_value.const_val = const_val;

    let inputs = inputs.as_ref().map(|i| i.as_slice()).unwrap_or(&[]);
    analyzer.set_op_io(op.id, op.token, inputs, &[new_id]);
    stack.push(new_id);
}
