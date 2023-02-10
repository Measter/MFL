use intcast::IntCast;
use lasso::Spur;

use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{Analyzer, ConstVal, IntWidth, PtrId},
};

pub(super) fn cast_int(analyzer: &mut Analyzer, op: &Op, width: IntWidth) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<1>();
    let Some([types]) = analyzer.value_consts(input_ids) else { return };

    let new_const_val = match types {
        ConstVal::Int(v) => ConstVal::Int(v & width.mask()),
        ConstVal::Bool(b) => ConstVal::Int(b as _),
        _ => return,
    };

    analyzer.set_value_const(op_data.outputs[0], new_const_val);
}

pub(super) fn dup(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs = op_data.inputs().to_owned();
    let outputs = op_data.outputs().to_owned();

    for (input, output) in inputs.into_iter().zip(outputs) {
        let Some([const_val]) = analyzer.value_consts([input]) else { continue };
        analyzer.set_value_const(output, const_val);
    }
}

pub(super) fn over(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input = op_data.inputs()[0];
    let output = op_data.outputs()[0];

    let Some([input_const])  = analyzer.value_consts([input]) else { return };
    analyzer.set_value_const(output, input_const);
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
        let [len, ptr] = *op_data.outputs.as_arr::<2>();
        analyzer.set_value_const(len, ConstVal::Int(str_len.to_u64()));
        analyzer.set_value_const(
            ptr,
            ConstVal::Ptr {
                id: PtrId::Str(id),
                src_op_loc: op.token.location,
                offset: Some(0),
            },
        );
    };
}
