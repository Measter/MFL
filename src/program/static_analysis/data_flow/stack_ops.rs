use lasso::Spur;

use crate::{interners::Interners, n_ops::SliceNOps, opcode::Op, source_file::SourceStorage};

use super::{
    super::{
        generate_stack_length_mismatch_diag, generate_type_mismatch_diag, Analyzer, ConstVal,
        PtrId, Value, ValueId,
    },
    ensure_stack_depth,
};

pub(super) fn drop(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 1);

    let input = stack.pop().unwrap();

    analyzer.consume_value(input, op.id);
    analyzer.set_op_io(op, &[input], &[]);
}

pub(super) fn dup(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    depth: usize,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, depth + 1);

    let src_id = stack[stack.len() - 1 - depth];
    let new_id = analyzer.new_value(op);
    stack.push(new_id);

    analyzer.set_op_io(op, &[src_id], &[new_id]);
}

pub(super) fn dup_pair(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);

    let input_ids = *stack.lastn(2).unwrap().as_arr::<2>();
    let new_id1 = analyzer.new_value(op);
    let new_id2 = analyzer.new_value(op);
    stack.push(new_id1);
    stack.push(new_id2);

    analyzer.set_op_io(op, &[new_id1, new_id2], &input_ids);
}

pub(super) fn push_str(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    interner: &Interners,
    op: &Op,
    is_c_str: bool,
    id: Spur,
) {
    let ptr_id = analyzer.new_value(op);

    if is_c_str {
        stack.push(ptr_id);
        analyzer.set_op_io(op, &[], &[ptr_id]);
    } else {
        let len_id = analyzer.new_value(op);
        stack.push(len_id);
        stack.push(ptr_id);
        analyzer.set_op_io(op, &[], &[len_id, ptr_id]);
    };
}

pub(super) fn rot(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 3);
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
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);
    let start = stack.len() - 2;
    stack[start..].rotate_left(1);
}
