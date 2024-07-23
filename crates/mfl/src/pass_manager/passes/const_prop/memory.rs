use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{IntKind, Op, TypeResolvedOp},
    pass_manager::static_analysis::{Analyzer, ConstVal},
    stores::types::TypeKind,
    Stores,
};

pub(crate) fn insert_extract_array(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let &[.., array_value_id, idx_value_id] = op_data.inputs.as_slice() else {
        unreachable!()
    };
    let Some([ConstVal::Int(IntKind::Unsigned(idx))]) = analyzer.value_consts([idx_value_id])
    else {
        return;
    };

    let [array_type_id] = analyzer.value_types([array_value_id]).unwrap();
    let array_type_info = stores.types.get_type_info(array_type_id);

    let array_length = match array_type_info.kind {
        TypeKind::Array { length, .. } => length,
        TypeKind::Pointer(ptee_id) => {
            let info = stores.types.get_type_info(ptee_id);
            match info.kind {
                TypeKind::Array { length, .. } => length,
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
                TypeKind::Integer(_)
                | TypeKind::Pointer(_)
                | TypeKind::Bool
                | TypeKind::GenericStructBase(_) => unreachable!(),
            }
        }
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
        TypeKind::Integer(_) | TypeKind::Bool | TypeKind::GenericStructBase(_) => unreachable!(),
    };

    if idx.to_usize() < array_length {
        return;
    }

    let array_type_name = stores.strings.resolve(array_type_info.name);
    let idx_value = idx.to_string();
    let mut labels = diagnostics::build_creator_label_chain(
        analyzer,
        [
            (array_value_id, 0, array_type_name),
            (idx_value_id, 1, &idx_value),
        ],
        Color::Yellow,
        Color::Cyan,
    );
    labels.push(Label::new(op.token.location).with_color(Color::Red));

    diagnostics::emit_error(
        stores,
        op.token.location,
        "index out of bounds",
        labels,
        None,
    );

    had_error.set();
}
