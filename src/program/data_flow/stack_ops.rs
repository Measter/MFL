use lasso::Spur;

use crate::{
    interners::Interners, opcode::Op, source_file::SourceStorage, type_check::PorthTypeKind,
};

use super::{generate_stack_exhaustion_diag, Analyzer, ConstVal, PtrId, ValueId};

pub(super) fn swap(
    stack: &mut Vec<ValueId>,
    analyzer: &mut Analyzer,
    op_idx: usize,
    source_store: &SourceStorage,
    op: &Op,
    had_error: &mut bool,
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

pub(super) fn drop(
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    op: &Op,
    had_error: &mut bool,
    analyzer: &mut Analyzer,
    op_idx: usize,
) {
    match stack.pop() {
        None => {
            generate_stack_exhaustion_diag(source_store, op, 0, 1);
            *had_error = true;
        }
        Some(val_id) => {
            analyzer.consume(val_id, op_idx);
        }
    }
}

pub(super) fn push_str(
    is_c_str: bool,
    analyzer: &mut Analyzer,
    op_idx: usize,
    op: &Op,
    interner: &Interners,
    id: Spur,
    stack: &mut Vec<ValueId>,
) {
    if !is_c_str {
        let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Int, op_idx, op.token);
        let string = interner.resolve_literal(id);
        new_value.const_val = Some(ConstVal::Int((string.len() - 1) as u64));
        stack.push(new_id);
    }
    let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Ptr, op_idx, op.token);
    new_value.const_val = Some(ConstVal::Ptr {
        id: PtrId::Str(id),
        source_op_location: op.token.location,
        offset: 0,
    });
    stack.push(new_id);
}

pub(super) fn push_int(
    analyzer: &mut Analyzer,
    op_idx: usize,
    op: &Op,
    v: u64,
    stack: &mut Vec<ValueId>,
) {
    let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Int, op_idx, op.token);
    new_value.const_val = Some(ConstVal::Int(v));
    stack.push(new_id);
}

pub(super) fn push_bool(
    analyzer: &mut Analyzer,
    op_idx: usize,
    op: &Op,
    v: bool,
    stack: &mut Vec<ValueId>,
) {
    let (new_id, new_value) = analyzer.new_value(PorthTypeKind::Bool, op_idx, op.token);
    new_value.const_val = Some(ConstVal::Bool(v));
    stack.push(new_id);
}
