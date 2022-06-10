use lasso::Spur;

use crate::{
    interners::Interners, opcode::Op, source_file::SourceStorage, type_check::PorthTypeKind,
};

use super::super::{
    check_allowed_const, generate_stack_length_mismatch_diag, generate_type_mismatch_diag,
    Analyzer, ConstVal, PtrId, Value, ValueId,
};

pub(super) fn cast_int(
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

    let (input, new_type, const_val) = match stack.pop() {
        None => {
            generate_stack_length_mismatch_diag(
                source_store,
                op,
                op.token.location,
                stack.len(),
                1,
            );
            *had_error = true;

            (None, PorthTypeKind::Unknown, None)
        }
        Some(val) => {
            let (new_type, const_val) = match analyzer.get_values([val]) {
                type_pattern!(a @ PorthTypeKind::Bool)
                | type_pattern!(a @ PorthTypeKind::Int)
                | type_pattern!(a @ PorthTypeKind::Ptr) => (PorthTypeKind::Int, *a),
                [val] => {
                    // Type mismatch. Only case at the moment is if the type was Unknown.
                    // We'll handle it properly anyway.
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

    let allow_const = check_allowed_const(input.map(|a| [a]), force_non_const_before);

    let const_val = if allow_const {
        match const_val {
            Some(ConstVal::Int(v)) => Some(ConstVal::Int(v)),
            Some(ConstVal::Bool(v)) => Some(ConstVal::Int(v as _)),

            // The actual pointer address is a runtime address.
            Some(ConstVal::Ptr { .. }) | None => None,
        }
    } else {
        None
    };

    let (new_id, new_value) = analyzer.new_value(new_type, op.id, op.token);
    new_value.const_val = const_val;

    let inputs = input.as_ref().map(std::slice::from_ref).unwrap_or(&[]);
    analyzer.set_io(op.id, op.token, inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn cast_ptr(
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

    let (input, new_type, const_val) = match stack.pop() {
        None => {
            generate_stack_length_mismatch_diag(
                source_store,
                op,
                op.token.location,
                stack.len(),
                1,
            );
            *had_error = true;

            (None, PorthTypeKind::Unknown, None)
        }
        Some(val) => {
            let (new_type, const_val) = match analyzer.get_values([val]) {
                type_pattern!(a @ PorthTypeKind::Int) | type_pattern!(a @ PorthTypeKind::Ptr) => {
                    (PorthTypeKind::Ptr, *a)
                }
                [val] => {
                    // Type mismatch.
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

    let allow_const = check_allowed_const(input.map(|a| [a]), force_non_const_before);

    let const_val = if allow_const {
        match const_val {
            Some(ptr @ ConstVal::Ptr { .. }) => Some(ptr),
            _ => None,
        }
    } else {
        None
    };

    let (new_id, new_value) = analyzer.new_value(new_type, op.id, op.token);
    new_value.const_val = const_val;

    let inputs = input.as_ref().map(std::slice::from_ref).unwrap_or(&[]);
    analyzer.set_io(op.id, op.token, inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn drop(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    match stack.pop() {
        None => {
            generate_stack_length_mismatch_diag(source_store, op, op.token.location, 0, 1);
            *had_error = true;
        }
        Some(val_id) => {
            analyzer.consume(val_id, op.id);
            analyzer.set_io(op.id, op.token, &[val_id], &[]);
        }
    }
}

pub(super) fn dup(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
    depth: usize,
) {
    if stack.len() < (depth + 1) {
        generate_stack_length_mismatch_diag(
            source_store,
            op,
            op.token.location,
            stack.len(),
            depth + 1,
        );
        *had_error = true;
        let (new_id, _) = analyzer.new_value(PorthTypeKind::Unknown, op.id, op.token);
        stack.push(new_id);
        return;
    }

    let val_id = stack[stack.len() - 1 - depth];
    let value = analyzer.value_mut(val_id);
    let val_type = value.porth_type;

    let allow_const = check_allowed_const(Some([val_id]), force_non_const_before);
    let val_const_val = if allow_const { value.const_val } else { None };

    let (new_id, new_val) = analyzer.new_value(val_type, op.id, op.token);
    new_val.const_val = val_const_val;

    analyzer.set_io(op.id, op.token, &[val_id], &[new_id]);

    stack.push(new_id);
}

pub(super) fn dup_pair(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    match &**stack {
        [.., a, b] => {
            let a = *a;
            let b = *b;

            let [a_val, b_val] = analyzer.get_values([a, b]);
            let a_type = a_val.porth_type;
            let a_const = a_val.const_val;
            let b_type = b_val.porth_type;
            let b_const = b_val.const_val;

            let (dup_a_id, dup_a) = analyzer.new_value(a_type, op.id, op.token);
            let allow_const = check_allowed_const(Some([a]), force_non_const_before);
            dup_a.const_val = if allow_const { a_const } else { None };
            stack.push(dup_a_id);

            let (dup_b_id, dup_b) = analyzer.new_value(b_type, op.id, op.token);
            let allow_const = check_allowed_const(Some([b]), force_non_const_before);
            dup_b.const_val = if allow_const { b_const } else { None };
            stack.push(dup_b_id);

            analyzer.set_io(op.id, op.token, &[a, b], &[dup_a_id, dup_b_id]);
        }
        [a] => {
            let a = *a;
            generate_stack_length_mismatch_diag(
                source_store,
                op,
                op.token.location,
                stack.len(),
                op.code.pop_count(),
            );
            *had_error = true;

            let (dup_b_id, _) = analyzer.new_value(PorthTypeKind::Unknown, op.id, op.token);
            stack.push(dup_b_id);

            let [a_val] = analyzer.get_values([a]);
            let a_type = a_val.porth_type;
            let a_const = a_val.const_val;

            let (dup_a_id, dup_a) = analyzer.new_value(a_type, op.id, op.token);
            let allow_const = check_allowed_const(Some([a]), force_non_const_before);
            dup_a.const_val = if allow_const { a_const } else { None };
            stack.push(dup_a_id);

            analyzer.set_io(op.id, op.token, &[a], &[dup_b_id, dup_a_id]);
        }
        [] => {
            generate_stack_length_mismatch_diag(
                source_store,
                op,
                op.token.location,
                stack.len(),
                op.code.pop_count(),
            );
            *had_error = true;

            let (dup_b_id, _) = analyzer.new_value(PorthTypeKind::Unknown, op.id, op.token);
            stack.push(dup_b_id);
            let (dup_a_id, _) = analyzer.new_value(PorthTypeKind::Unknown, op.id, op.token);
            stack.push(dup_a_id);

            analyzer.set_io(op.id, op.token, &[], &[dup_b_id, dup_a_id])
        }
    }
}

pub(super) fn push_argc(analyzer: &mut Analyzer, stack: &mut Vec<ValueId>, op: &Op) {
    let (new_id, _) = analyzer.new_value(PorthTypeKind::Int, op.id, op.token);
    stack.push(new_id);
    analyzer.set_io(op.id, op.token, &[], &[new_id]);
}

pub(super) fn push_argv(analyzer: &mut Analyzer, stack: &mut Vec<ValueId>, op: &Op) {
    let (new_id, _) = analyzer.new_value(PorthTypeKind::Ptr, op.id, op.token);
    stack.push(new_id);
    analyzer.set_io(op.id, op.token, &[], &[new_id]);
}

pub(super) fn push_bool(analyzer: &mut Analyzer, stack: &mut Vec<ValueId>, op: &Op, v: bool) {
    let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Bool, op.id, op.token);
    new_value.const_val = Some(ConstVal::Bool(v));
    stack.push(new_id);
    analyzer.set_io(op.id, op.token, &[], &[new_id]);
}

pub(super) fn push_int(analyzer: &mut Analyzer, stack: &mut Vec<ValueId>, op: &Op, v: u64) {
    let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Int, op.id, op.token);
    new_value.const_val = Some(ConstVal::Int(v));
    stack.push(new_id);
    analyzer.set_io(op.id, op.token, &[], &[new_id]);
}

pub(super) fn push_str(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    interner: &Interners,
    op: &Op,
    is_c_str: bool,
    id: Spur,
) {
    let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Ptr, op.id, op.token);
    new_value.const_val = Some(ConstVal::Ptr {
        id: PtrId::Str(id),
        src_op_loc: op.token.location,
        offset: Some(0),
    });

    let mut outputs = [new_id, new_id];
    if !is_c_str {
        let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Int, op.id, op.token);
        let string = interner.resolve_literal(id);
        new_value.const_val = Some(ConstVal::Int((string.len() - 1) as u64));
        stack.push(new_id);
        outputs[0] = new_id;
    }

    stack.push(new_id);
    analyzer.set_io(
        op.id,
        op.token,
        &[],
        is_c_str.then(|| &outputs[1..]).unwrap_or(&outputs),
    )
}

pub(super) fn rot(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    if stack.len() < 3 {
        generate_stack_length_mismatch_diag(
            source_store,
            op,
            op.token.location,
            stack.len(),
            op.code.pop_count(),
        );
        *had_error = true;
        stack.resize_with(3, || {
            analyzer
                .new_value(PorthTypeKind::Unknown, op.id, op.token)
                .0
        });
    }
    let start = stack.len() - 3;
    stack[start..].rotate_left(1);
}

pub(super) fn swap(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    match stack.as_mut_slice() {
        [.., a, b] => std::mem::swap(a, b),
        _ => {
            generate_stack_length_mismatch_diag(
                source_store,
                op,
                op.token.location,
                stack.len(),
                2,
            );
            *had_error = true;
            stack.resize_with(2, || {
                analyzer
                    .new_value(PorthTypeKind::Unknown, op.id, op.token)
                    .0
            });
        }
    }
}
