use intcast::IntCast;

use crate::{
    error_signal::ErrorSignal,
    pass_manager::PassManager,
    stores::{
        ops::OpId,
        types::{Float, FloatWidth, IntKind, Integer, TypeId, TypeKind},
        values::ConstVal,
    },
    Stores,
};

use super::{new_const_val_for_type, ConstFieldInitState};

pub(crate) fn dup_over_rotate_swap_reverse(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id).clone();

    for (input_value_id, output_value_id) in op_data.inputs.into_iter().zip(op_data.outputs) {
        let [input_const_val] = stores.values.value_consts([input_value_id]);

        stores
            .values
            .set_value_const(output_value_id, input_const_val.clone());
    }
}

pub(crate) fn push_bool(stores: &mut Stores, op_id: OpId, value: bool) {
    let op_data = stores.ops.get_op_io(op_id);
    stores
        .values
        .set_value_const(op_data.outputs[0], ConstVal::Bool(value));
}

pub(crate) fn push_int(stores: &mut Stores, op_id: OpId, value: Integer) {
    let op_data = stores.ops.get_op_io(op_id);
    stores
        .values
        .set_value_const(op_data.outputs[0], ConstVal::Int(value));
}

pub(crate) fn push_float(stores: &mut Stores, op_id: OpId, value: Float) {
    let op_data = stores.ops.get_op_io(op_id);
    stores
        .values
        .set_value_const(op_data.outputs[0], ConstVal::Float(value));
}

pub(crate) fn push_str(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let output_value_id = op_data.outputs[0];
    let [output_type_id] = stores.values.value_types([output_value_id]).unwrap();

    let new_const_value = new_const_val_for_type(
        stores,
        pass_manager,
        had_error,
        output_type_id,
        ConstFieldInitState::Unknown,
    );

    stores
        .values
        .set_value_const(output_value_id, new_const_value);
}

pub(crate) fn cast(stores: &mut Stores, op_id: OpId, target_type_id: TypeId) {
    let target_type_info = stores.types.get_type_info(target_type_id);

    match target_type_info.kind {
        TypeKind::Integer(int_kind) => cast_to_int(stores, op_id, int_kind),
        TypeKind::Float(width) => cast_to_float(stores, op_id, width),
        TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) => cast_to_ptr(stores, op_id),
        TypeKind::Array { .. }
        | TypeKind::Bool
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => unreachable!(),
    }
}

fn cast_to_ptr(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_id = op_data.inputs[0];
    let output_value_id = op_data.outputs[0];
    let [input_const_val] = stores.values.value_consts([input_value_id]);
    let Some(type_ids @ [input_type_id, output_type_id]) =
        stores.values.value_types([input_value_id, output_value_id])
    else {
        return;
    };
    let type_kinds = type_ids.map(|id| stores.types.get_type_info(id).kind);

    let new_output_const_val = match type_kinds {
        [TypeKind::SinglePointer(_), TypeKind::MultiPointer(_)]
        | [TypeKind::MultiPointer(_), TypeKind::SinglePointer(_)]
            if matches!(input_const_val, ConstVal::Pointer { .. }) =>
        {
            input_const_val.clone()
        }

        // Just echo the previous const val
        _ if input_type_id == output_type_id => input_const_val.clone(),

        _ if input_const_val == &ConstVal::Uninitialized => ConstVal::Uninitialized,
        _ => ConstVal::Unknown,
    };

    stores
        .values
        .set_value_const(output_value_id, new_output_const_val);
}

fn cast_to_int(stores: &mut Stores, op_id: OpId, int_kind: IntKind) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_id = op_data.inputs[0];
    let [input_const_val] = stores.values.value_consts([input_value_id]);

    let output_const_val = match input_const_val {
        ConstVal::Int(v) => ConstVal::Int(v.cast(int_kind)),
        ConstVal::Enum(_, d) => ConstVal::Int(Integer::Unsigned(d.to_u64())),
        ConstVal::Float(_) => todo!(),
        ConstVal::Bool(b) if int_kind.is_unsigned() => ConstVal::Int(Integer::Unsigned(*b as _)),
        ConstVal::Bool(b) => ConstVal::Int(Integer::Signed(*b as _)),
        ConstVal::Pointer { .. } | ConstVal::Aggregate { .. } => unreachable!(),
        ConstVal::Uninitialized | ConstVal::Unknown => input_const_val.clone(),
    };

    stores
        .values
        .set_value_const(op_data.outputs[0], output_const_val)
}

fn cast_to_float(stores: &mut Stores, op_id: OpId, to_width: FloatWidth) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_value_id = op_data.inputs[0];
    let [input_const_val] = stores.values.value_consts([input_value_id]);

    let output_const_value = match input_const_val {
        ConstVal::Int(v) => {
            let float = match (to_width, v) {
                (FloatWidth::F32, Integer::Signed(v)) => Float(*v as f32 as f64),
                (FloatWidth::F32, Integer::Unsigned(v)) => Float(*v as f32 as f64),
                (FloatWidth::F64, Integer::Signed(v)) => Float(*v as f64),
                (FloatWidth::F64, Integer::Unsigned(v)) => Float(*v as f64),
            };

            ConstVal::Float(float)
        }
        ConstVal::Float(Float(input_float)) => {
            let [input_type_id] = stores.values.value_types([input_value_id]).unwrap();
            let input_type_info = stores.types.get_type_info(input_type_id);
            let TypeKind::Float(input_width) = input_type_info.kind else {
                unreachable!()
            };

            match (input_width, to_width) {
                (FloatWidth::F32, _) | (FloatWidth::F64, FloatWidth::F64) => {
                    input_const_val.clone()
                }
                (FloatWidth::F64, FloatWidth::F32) => {
                    ConstVal::Float(Float(*input_float as f32 as f64))
                }
            }
        }
        ConstVal::Bool(_)
        | ConstVal::Enum(_, _)
        | ConstVal::Pointer { .. }
        | ConstVal::Aggregate { .. } => {
            unreachable!()
        }
        ConstVal::Uninitialized | ConstVal::Unknown => input_const_val.clone(),
    };

    stores
        .values
        .set_value_const(op_data.outputs[0], output_const_value)
}

pub(crate) fn size_of(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    op_id: OpId,
    type_id: TypeId,
) {
    let type_info = stores.types.get_type_info(type_id);

    match type_info.kind {
        TypeKind::Struct(struct_item_id) | TypeKind::GenericStructInstance(struct_item_id) => {
            if pass_manager
                .ensure_define_structs(stores, struct_item_id)
                .is_err()
            {
                return;
            }
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::MultiPointer(_)
        | TypeKind::SinglePointer(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => {}
    }

    let size_info = stores.types.get_size_info(type_id);
    push_int(stores, op_id, Integer::Unsigned(size_info.byte_width));
}
