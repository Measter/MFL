use crate::{
    ir::{Arithmetic, IntKind, Op, TypeResolvedOp},
    n_ops::SliceNOps,
    pass_manager::static_analysis::{Analyzer, ConstVal},
    type_store::TypeKind,
    Stores,
};

pub(crate) fn add(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    op: &Op<TypeResolvedOp>,
    arith_code: Arithmetic,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_value_ids = *op_data.inputs.as_arr::<2>();
    let Some([output_type_id]) = analyzer.value_types([op_data.outputs[0]]) else {
        return;
    };
    let output_type_info = stores.types.get_type_info(output_type_id);
    let Some(input_const_values) = analyzer.value_consts(input_value_ids) else {
        return;
    };

    let new_const_val = match input_const_values {
        [ConstVal::Int(a), ConstVal::Int(b)] => {
            let TypeKind::Integer(output_int) = output_type_info.kind else {
                unreachable!()
            };

            // The cast has already been type checked.
            let a_kind = a.cast(output_int);
            let b_kind = b.cast(output_int);
            let kind = match (a_kind, b_kind) {
                (IntKind::Signed(a), IntKind::Signed(b)) => {
                    IntKind::Signed(arith_code.get_signed_binary_op()(a, b))
                }
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => {
                    IntKind::Unsigned(arith_code.get_unsigned_binary_op()(a, b))
                }
                _ => unreachable!(),
            };

            ConstVal::Int(kind)
        }

        // Pointer offset.
        [ConstVal::Ptr {
            id,
            src_op_loc,
            offset: Some(offset),
        }, ConstVal::Int(IntKind::Unsigned(v))] => ConstVal::Ptr {
            id,
            src_op_loc,
            offset: Some(offset + v),
        },

        [ConstVal::Int(IntKind::Unsigned(v)), ConstVal::Ptr {
            id,
            src_op_loc,
            offset: Some(offset),
        }] => ConstVal::Ptr {
            id,
            src_op_loc,
            offset: Some(offset + v),
        },
        _ => return,
    };

    let output_id = op_data.outputs[0];
    analyzer.set_value_const(output_id, new_const_val);
}
