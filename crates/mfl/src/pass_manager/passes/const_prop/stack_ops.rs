use crate::{
    ir::{IntKind, Op, TypeResolvedOp},
    pass_manager::static_analysis::{Analyzer, ConstVal},
};

pub(crate) fn dup_over(analyzer: &mut Analyzer, op: &Op<TypeResolvedOp>) {
    let op_data = analyzer.get_op_io(op.id).clone();

    for (input_value_id, output_value_id) in op_data.inputs.into_iter().zip(op_data.outputs) {
        let Some([input_const_val]) = analyzer.value_consts([input_value_id]) else {
            continue;
        };

        analyzer.set_value_const(output_value_id, input_const_val);
    }
}

pub(crate) fn push_bool(analyzer: &mut Analyzer, op: &Op<TypeResolvedOp>, value: bool) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_const(op_data.outputs[0], ConstVal::Bool(value));
}

pub(crate) fn push_int(analyzer: &mut Analyzer, op: &Op<TypeResolvedOp>, value: IntKind) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_const(op_data.outputs[0], ConstVal::Int(value));
}
