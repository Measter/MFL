use crate::{
    interners::Interners,
    n_ops::NOps,
    opcode::Op,
    program::static_analysis::{check_allowed_const2, Analyzer, ConstVal, Value, ValueId},
    source_file::SourceStorage,
};

pub(super) fn add(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    force_non_const_before: Option<ValueId>,
    op: &Op,
) {
    let op_data = analyzer.get_io(op.id);

    let input_ids = *op_data.inputs.as_arr::<2>();
    if !check_allowed_const2(input_ids, force_non_const_before) {
        return;
    }

    let inputs = analyzer.get_values(input_ids);

    let types = match inputs {
        const_pattern!(a, b) => (*a, *b),
        _ => return,
    };

    let new_const_val = match types {
        (ConstVal::Int(a), ConstVal::Int(b)) => ConstVal::Int(a + b),

        // Const pointer with a constant offset.
        (
            ConstVal::Ptr {
                offset: Some(offset),
                id,
                src_op_loc,
            },
            ConstVal::Int(v),
        ) => ConstVal::Ptr {
            offset: Some(offset + v),
            id,
            src_op_loc,
        },
        // Const pointer with a constant offset.
        (
            ConstVal::Int(v),
            ConstVal::Ptr {
                offset: Some(offset),
                id,
                src_op_loc,
            },
        ) => ConstVal::Ptr {
            offset: Some(offset + v),
            id,
            src_op_loc,
        },

        _ => return,
    };

    let output_id = op_data.outputs[0];
    let output = analyzer.value_mut(output_id);
    output.const_val = Some(new_const_val);
}

pub(super) fn subtract(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn bitnot(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn bitand_bitor(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn multiply_and_shift(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}

pub(super) fn divmod(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    todo!()
}
