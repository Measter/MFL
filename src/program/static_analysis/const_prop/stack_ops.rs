use lasso::Spur;

use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{Analyzer, ConstVal, PtrId, ValueId},
    source_file::SourceStorage,
};

use super::check_allowed_const;

pub(super) fn cast_int(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);

    let input_ids = *op_data.inputs.as_arr::<1>();
    if !check_allowed_const(input_ids, force_non_const_before) {
        return;
    }

    let Some([types]) = analyzer.value_consts(input_ids) else { return };

    let new_const_val = match types {
        ConstVal::Int(v) => ConstVal::Int(v),
        ConstVal::Bool(b) => ConstVal::Int(b as _),
        _ => return,
    };

    analyzer.set_value_const(op_data.outputs[0], new_const_val);
}
pub(super) fn cast_ptr(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);

    let input_ids = *op_data.inputs.as_arr::<1>();
    if !check_allowed_const(input_ids, force_non_const_before) {
        return;
    }

    let Some([types]) = analyzer.value_consts(input_ids) else { return };

    if !matches!(types, ConstVal::Ptr { .. }) {
        return;
    }

    analyzer.set_value_const(op_data.outputs[0], types);
}

pub(super) fn dup(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
    depth: usize,
) {
    let op_data = analyzer.get_op_io(op.id);

    let input_ids = *op_data.inputs.as_arr::<1>();
    if !check_allowed_const(input_ids, force_non_const_before) {
        return;
    }

    let Some([types]) = analyzer.value_consts(input_ids) else { return };
    analyzer.set_value_const(op_data.outputs[0], types);
}

pub(super) fn dup_pair(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);

    for (&input_id, &output_id) in op_data.inputs.iter().zip(&op_data.outputs) {
        if !check_allowed_const([input_id], force_non_const_before) {
            continue;
        }
        let Some([input_type]) = analyzer.value_consts([input_id]) else { continue };
        analyzer.set_value_const(output_id, input_type);
    }
}

pub(super) fn push_bool(analyzer: &mut Analyzer, op: &Op, value: bool) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_const(op_data.outputs[0], ConstVal::Bool(value));
}

pub(super) fn push_int(analyzer: &mut Analyzer, op: &Op, value: u64) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_const(op_data.outputs[0], ConstVal::Int(value));
}

pub(super) fn push_str(
    analyzer: &mut Analyzer,
    interner: &Interners,
    op: &Op,
    id: Spur,
    is_c_str: bool,
) {
    let op_data = analyzer.get_op_io(op.id);

    if is_c_str {
        analyzer.set_value_const(
            op_data.outputs[0],
            ConstVal::Ptr {
                id: PtrId::Str(id),
                src_op_loc: op.token.location,
                offset: Some(0),
            },
        );
    } else {
        let str_len = interner.resolve_literal(id).len() - 1; // All strings are null-terminated.
        analyzer.set_value_const(op_data.outputs[0], ConstVal::Int(str_len as u64));
        analyzer.set_value_const(
            op_data.outputs[1],
            ConstVal::Ptr {
                id: PtrId::Str(id),
                src_op_loc: op.token.location,
                offset: Some(0),
            },
        );
    };
}
