use lasso::Spur;

use crate::{
    n_ops::SliceNOps,
    opcode::{IntKind, Op},
    program::static_analysis::{Analyzer, ConstVal, IntWidth, PtrId},
    type_store::{Signedness, TypeId},
};

pub fn cast_to_int(analyzer: &mut Analyzer, op: &Op, to_width: IntWidth, to_signed: Signedness) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<1>();
    let Some([input_const_val]) = analyzer.value_consts(input_ids) else {
        return;
    };

    let new_const_val = match input_const_val {
        ConstVal::Int(v) => ConstVal::Int(v.cast(to_width, to_signed)),
        ConstVal::Bool(b) => ConstVal::Int(IntKind::Unsigned(b as _)),
        ConstVal::Ptr { .. } => return,
    };

    analyzer.set_value_const(op_data.outputs[0], new_const_val);
}

pub fn cast_to_ptr(analyzer: &mut Analyzer, op: &Op, to_kind: TypeId) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs()[0];
    let Some([input_const_val]) = analyzer.value_consts([input_id]) else {
        return;
    };

    let [input_type_id] = analyzer.value_types([input_id]).unwrap();
    if input_type_id == to_kind {
        analyzer.set_value_const(input_id, input_const_val);
    }
}

pub fn dup(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs = op_data.inputs().to_owned();
    let outputs = op_data.outputs().to_owned();

    for (input, output) in inputs.into_iter().zip(outputs) {
        let Some([const_val]) = analyzer.value_consts([input]) else {
            continue;
        };
        analyzer.set_value_const(output, const_val);
    }
}

pub fn over(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input = op_data.inputs()[0];
    let output = op_data.outputs()[0];

    let Some([input_const]) = analyzer.value_consts([input]) else {
        return;
    };
    analyzer.set_value_const(output, input_const);
}

pub fn push_bool(analyzer: &mut Analyzer, op: &Op, value: bool) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_const(op_data.outputs[0], ConstVal::Bool(value));
}

pub fn push_int(analyzer: &mut Analyzer, op: &Op, value: IntKind) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_const(op_data.outputs[0], ConstVal::Int(value));
}

pub fn push_str(analyzer: &mut Analyzer, op: &Op, id: Spur, is_c_str: bool) {
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
    }
}
