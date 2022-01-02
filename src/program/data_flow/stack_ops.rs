use lasso::Spur;

use crate::{
    interners::Interners, opcode::Op, source_file::SourceStorage, type_check::PorthTypeKind,
};

use super::{generate_stack_exhaustion_diag, Analyzer, ConstVal, PtrId, ValueId};

pub(super) fn drop(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op_idx: usize,
    op: &Op,
) {
    match stack.pop() {
        None => {
            generate_stack_exhaustion_diag(source_store, op, 0, 1);
            *had_error = true;
        }
        Some(val_id) => {
            analyzer.consume(val_id, op_idx);
            analyzer.set_io(op_idx, op.token, &[val_id], &[]);
        }
    }
}

pub(super) fn dup(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op_idx: usize,
    op: &Op,
    depth: usize,
) {
    if stack.len() < (depth + 1) {
        generate_stack_exhaustion_diag(source_store, op, stack.len(), depth + 1);
        *had_error = true;
        let (new_id, _) = analyzer.new_value(PorthTypeKind::Unknown, op_idx, op.token);
        stack.push(new_id);
        return;
    }

    let val_id = stack[stack.len() - 1 - depth];
    let value = analyzer.value_mut(val_id);
    let val_type = value.porth_type;
    let val_const_val = value.const_val;

    let (new_id, new_val) = analyzer.new_value(val_type, op_idx, op.token);
    new_val.const_val = val_const_val;

    analyzer.set_io(op_idx, op.token, &[val_id], &[new_id]);

    stack.push(new_id);
}

pub(super) fn dup_pair(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op_idx: usize,
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

            let (dup_a_id, dup_a) = analyzer.new_value(a_type, op_idx, op.token);
            dup_a.const_val = a_const;
            stack.push(dup_a_id);

            let (dup_b_id, dup_b) = analyzer.new_value(b_type, op_idx, op.token);
            dup_b.const_val = b_const;
            stack.push(dup_b_id);

            analyzer.set_io(op_idx, op.token, &[a, b], &[dup_a_id, dup_b_id]);
        }
        [a] => {
            let a = *a;
            generate_stack_exhaustion_diag(source_store, op, stack.len(), op.code.pop_count());
            *had_error = true;

            let (dup_b_id, _) = analyzer.new_value(PorthTypeKind::Unknown, op_idx, op.token);
            stack.push(dup_b_id);

            let [a_val] = analyzer.get_values([a]);
            let a_type = a_val.porth_type;
            let a_const = a_val.const_val;

            let (dup_a_id, dup_a) = analyzer.new_value(a_type, op_idx, op.token);
            dup_a.const_val = a_const;
            stack.push(dup_a_id);

            analyzer.set_io(op_idx, op.token, &[a], &[dup_b_id, dup_a_id]);
        }
        [] => {
            generate_stack_exhaustion_diag(source_store, op, stack.len(), op.code.pop_count());
            *had_error = true;

            let (dup_b_id, _) = analyzer.new_value(PorthTypeKind::Unknown, op_idx, op.token);
            stack.push(dup_b_id);
            let (dup_a_id, _) = analyzer.new_value(PorthTypeKind::Unknown, op_idx, op.token);
            stack.push(dup_a_id);

            analyzer.set_io(op_idx, op.token, &[], &[dup_b_id, dup_a_id])
        }
    }
}

pub(super) fn push_bool(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    op_idx: usize,
    op: &Op,
    v: bool,
) {
    let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Bool, op_idx, op.token);
    new_value.const_val = Some(ConstVal::Bool(v));
    stack.push(new_id);
    analyzer.set_io(op_idx, op.token, &[], &[new_id]);
}

pub(super) fn push_int(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    op_idx: usize,
    op: &Op,
    v: u64,
) {
    let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Int, op_idx, op.token);
    new_value.const_val = Some(ConstVal::Int(v));
    stack.push(new_id);
    analyzer.set_io(op_idx, op.token, &[], &[new_id]);
}

pub(super) fn push_str(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    interner: &Interners,
    op_idx: usize,
    op: &Op,
    is_c_str: bool,
    id: Spur,
) {
    let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Ptr, op_idx, op.token);
    new_value.const_val = Some(ConstVal::Ptr {
        id: PtrId::Str(id),
        src_op_loc: op.token.location,
        offset: Some(0),
    });

    let mut outputs = [new_id, new_id];
    if !is_c_str {
        let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Int, op_idx, op.token);
        let string = interner.resolve_literal(id);
        new_value.const_val = Some(ConstVal::Int((string.len() - 1) as u64));
        stack.push(new_id);
        outputs[0] = new_id;
    }

    stack.push(new_id);
    analyzer.set_io(
        op_idx,
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
    op_idx: usize,
    op: &Op,
) {
    if stack.len() < 3 {
        generate_stack_exhaustion_diag(source_store, op, stack.len(), op.code.pop_count());
        *had_error = true;
        stack.resize_with(3, || {
            analyzer
                .new_value(PorthTypeKind::Unknown, op_idx, op.token)
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
    op_idx: usize,
    op: &Op,
) {
    match stack.as_mut_slice() {
        [.., a, b] => std::mem::swap(a, b),
        _ => {
            generate_stack_exhaustion_diag(source_store, op, stack.len(), 2);
            *had_error = true;
            stack.resize_with(2, || {
                analyzer
                    .new_value(PorthTypeKind::Unknown, op_idx, op.token)
                    .0
            });
        }
    }
}
