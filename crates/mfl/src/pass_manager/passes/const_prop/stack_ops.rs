use crate::{
    ir::{Op, TypeResolvedOp},
    pass_manager::static_analysis::Analyzer,
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
