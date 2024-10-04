use std::ops::ControlFlow;

use intcast::IntCast;
use lasso::Spur;
use prettytable::{row, Table};
use smallvec::SmallVec;
use stores::{items::ItemId, source::Spanned};

use crate::{
    diagnostics::TABLE_FORMAT,
    error_signal::ErrorSignal,
    ir::PartiallyResolvedType,
    n_ops::SliceNOps,
    pass_manager::{
        static_analysis::{can_promote_float_unidirectional, can_promote_int_unidirectional},
        PassManager,
    },
    stores::{
        diagnostics::Diagnostic,
        ops::OpId,
        types::{IntKind, IntSignedness, IntWidth, TypeId, TypeInfo, TypeKind},
    },
    Stores,
};

fn is_slice_like_struct(stores: &mut Stores, struct_info: TypeInfo) -> Option<TypeId> {
    let mut has_valid_length_field = false;
    let mut store_type_id = None;

    let length_spur = stores.strings.intern("length");
    let pointer_spur = stores.strings.intern("pointer");

    let struct_def = stores.types.get_struct_def(struct_info.id);

    for field in &struct_def.fields {
        let field_kind = stores.types.get_type_info(field.kind.inner).kind;

        match field_kind {
            TypeKind::Integer(IntKind::U64) if field.name.inner == length_spur => {
                has_valid_length_field = true
            }
            TypeKind::MultiPointer(ptr_id) if field.name.inner == pointer_spur => {
                store_type_id = Some(ptr_id)
            }
            _ => {}
        }
    }

    if has_valid_length_field {
        store_type_id
    } else {
        None
    }
}

pub(crate) fn extract_array(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    emit_array: bool,
) {
    let op_data = stores.ops.get_op_io(op_id).clone();
    let op_loc = stores.ops.get_token(op_id).location;
    let inputs @ [array_value_id, idx_value_id] = *op_data.inputs.as_arr();
    let Some(type_ids) = stores.values.value_types(inputs) else {
        return;
    };
    let [array_type_info, idx_type_info] = type_ids.map(|id| stores.types.get_type_info(id));

    let output_value_id = if emit_array {
        let output_array_id = op_data.outputs[0];
        stores
            .values
            .set_value_type(output_array_id, array_type_info.id);
        op_data.outputs[1]
    } else {
        op_data.outputs[0]
    };

    let mut make_error_for_aggr = |stores: &mut Stores, note: Option<String>| {
        let value_type_name = stores.strings.resolve(array_type_info.friendly_name);

        let mut diag = Diagnostic::error(op_loc, format!("cannot extract a `{value_type_name}`"))
            .with_label_chain(array_value_id, 0, value_type_name);

        if let Some(note) = note {
            diag.set_note(note);
        }

        diag.attached(stores.diags, item_id);

        had_error.set();
    };

    let store_type = match array_type_info.kind {
        TypeKind::Array { type_id, .. } => type_id,
        TypeKind::MultiPointer(sub_type) | TypeKind::SinglePointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            match ptr_type_info.kind {
                TypeKind::Array { type_id, .. } => type_id,
                TypeKind::Struct(item_id) | TypeKind::GenericStructInstance(item_id) => {
                    if pass_manager.ensure_define_structs(stores, item_id).is_err() {
                        had_error.set();
                        return;
                    };
                    let Some(store_type) = is_slice_like_struct(stores, ptr_type_info) else {
                        make_error_for_aggr(
                            stores,
                            Some(
                                "Struct must be slice-like (must have a pointer and length field)"
                                    .to_owned(),
                            ),
                        );
                        return;
                    };
                    store_type
                }
                _ => {
                    make_error_for_aggr(stores, None);
                    return;
                }
            }
        }

        TypeKind::Struct(item_id) | TypeKind::GenericStructInstance(item_id) => {
            if pass_manager.ensure_define_structs(stores, item_id).is_err() {
                had_error.set();
                return;
            }
            let Some(store_type) = is_slice_like_struct(stores, array_type_info) else {
                make_error_for_aggr(
                    stores,
                    Some(
                        "Struct must be slice-like (must have a pointer and length field)"
                            .to_owned(),
                    ),
                );
                return;
            };
            store_type
        }
        TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => {
            make_error_for_aggr(stores, None);
            return;
        }
    };

    if !idx_type_info.kind.is_unsigned_int() {
        let idx_type_name = stores.strings.resolve(idx_type_info.friendly_name);
        Diagnostic::error(
            op_loc,
            format!("cannot index an array with `{idx_type_name}`"),
        )
        .with_label_chain(idx_value_id, 1, idx_type_name)
        .attached(stores.diags, item_id);

        had_error.set();
        return;
    }

    stores.values.set_value_type(output_value_id, store_type);
}

pub(crate) fn extract_struct(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    field_name: Spanned<Spur>,
    emit_struct: bool,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_struct_value_id = op_data.inputs[0];
    let Some([input_struct_type_id]) = stores.values.value_types([input_struct_value_id]) else {
        return;
    };
    let input_struct_type_info = stores.types.get_type_info(input_struct_type_id);

    let output_data_id = if emit_struct {
        let [output_struct_id, output_data_id] = *op_data.outputs.as_arr();
        stores
            .values
            .set_value_type(output_struct_id, input_struct_type_id);
        output_data_id
    } else {
        op_data.outputs[0]
    };

    let (actual_struct_type_id, actual_struct_item_id) = match input_struct_type_info.kind {
        TypeKind::Struct(struct_item_id) | TypeKind::GenericStructInstance(struct_item_id) => {
            (input_struct_type_id, struct_item_id)
        }
        TypeKind::MultiPointer(sub_type) | TypeKind::SinglePointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            let (TypeKind::Struct(struct_item_id)
            | TypeKind::GenericStructInstance(struct_item_id)) = ptr_type_info.kind
            else {
                Diagnostic::not_a_struct(
                    stores,
                    item_id,
                    input_struct_type_info,
                    input_struct_value_id,
                    op_id,
                    "extract from",
                );
                had_error.set();
                return;
            };
            (sub_type, struct_item_id)
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => {
            Diagnostic::not_a_struct(
                stores,
                item_id,
                input_struct_type_info,
                input_struct_value_id,
                op_id,
                "extract from",
            );
            had_error.set();
            return;
        }
    };

    if pass_manager
        .ensure_define_structs(stores, actual_struct_item_id)
        .is_err()
    {
        had_error.set();
        return;
    }

    let struct_def = stores.types.get_struct_def(actual_struct_type_id).clone();
    let Some(field_info) = struct_def
        .fields
        .iter()
        .find(|fi| fi.name.inner == field_name.inner)
    else {
        Diagnostic::field_not_found(
            stores,
            item_id,
            field_name,
            &struct_def,
            input_struct_type_info,
            input_struct_value_id,
        );

        had_error.set();
        return;
    };

    stores
        .values
        .set_value_type(output_data_id, field_info.kind.inner);
}

pub(crate) fn field_access(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    field_name: Spanned<Spur>,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let input_struct_value_id = op_data.inputs[0];
    let Some([input_struct_type_id]) = stores.values.value_types([input_struct_value_id]) else {
        return;
    };
    let input_struct_type_info = stores.types.get_type_info(input_struct_type_id);
    let output_pointer_id = op_data.outputs[0];

    let (actual_struct_type_id, actual_struct_item_id) = match input_struct_type_info.kind {
        TypeKind::MultiPointer(sub_type) | TypeKind::SinglePointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            let (TypeKind::Struct(struct_item_id)
            | TypeKind::GenericStructInstance(struct_item_id)) = ptr_type_info.kind
            else {
                Diagnostic::not_a_struct(
                    stores,
                    item_id,
                    input_struct_type_info,
                    input_struct_value_id,
                    op_id,
                    "access",
                );
                had_error.set();
                return;
            };
            (sub_type, struct_item_id)
        }

        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            let op_loc = stores.ops.get_token(op_id);
            let struct_type_name = stores.strings.resolve(input_struct_type_info.friendly_name);

            Diagnostic::error(op_loc.location, "field access not support on struct value")
                .with_note("Struct must be behind a pointer")
                .with_label_chain(input_struct_value_id, 1, struct_type_name)
                .attached(stores.diags, item_id);

            had_error.set();
            return;
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => {
            Diagnostic::not_a_struct(
                stores,
                item_id,
                input_struct_type_info,
                input_struct_value_id,
                op_id,
                "access",
            );
            had_error.set();
            return;
        }
    };

    if pass_manager
        .ensure_define_structs(stores, actual_struct_item_id)
        .is_err()
    {
        had_error.set();
        return;
    }

    let struct_def = stores.types.get_struct_def(actual_struct_type_id).clone();
    let Some(field_info) = struct_def
        .fields
        .iter()
        .find(|fi| fi.name.inner == field_name.inner)
    else {
        Diagnostic::field_not_found(
            stores,
            item_id,
            field_name,
            &struct_def,
            input_struct_type_info,
            input_struct_value_id,
        );

        had_error.set();
        return;
    };

    let output_type_info = stores
        .types
        .get_single_pointer(stores.strings, field_info.kind.inner);

    stores
        .values
        .set_value_type(output_pointer_id, output_type_info.id);
}

pub(crate) fn index(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let inputs @ [idx_value_id, array_value_id] = *op_data.inputs.as_arr();
    let output_value_id = op_data.outputs[0];
    let Some(type_ids) = stores.values.value_types(inputs) else {
        return;
    };

    let [idx_type_info, array_type_info] = type_ids.map(|id| stores.types.get_type_info(id));

    if !idx_type_info.kind.is_unsigned_int() {
        let idx_type_name = stores.strings.resolve(idx_type_info.friendly_name);

        Diagnostic::error(
            op_loc,
            format!("cannot index an array with `{idx_type_name}`"),
        )
        .with_label_chain(idx_value_id, 2, idx_type_name)
        .attached(stores.diags, item_id);

        had_error.set();
    }

    let mut make_error_for_aggr = |stores: &mut Stores, note| {
        let value_type_name = stores.strings.resolve(array_type_info.friendly_name);

        let mut diag =
            Diagnostic::error(op_loc, format!("cannot index into a `{value_type_name}`"))
                .with_label_chain(array_value_id, 1, value_type_name);

        if let Some(note) = note {
            diag.set_note(note);
        }

        diag.attached(stores.diags, item_id);

        had_error.set();
    };

    let store_type_id = match array_type_info.kind {
        TypeKind::MultiPointer(sub_type) | TypeKind::SinglePointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            match ptr_type_info.kind {
                TypeKind::Array { type_id, .. } => type_id,
                TypeKind::Struct(struct_item_id)
                | TypeKind::GenericStructInstance(struct_item_id) => {
                    if pass_manager
                        .ensure_define_structs(stores, struct_item_id)
                        .is_err()
                    {
                        had_error.set();
                        return;
                    };
                    let Some(store_type) = is_slice_like_struct(stores, ptr_type_info) else {
                        make_error_for_aggr(
                            stores,
                            Some(
                                "Struct must be slice-like (must have a pointer and length field)"
                                    .to_owned(),
                            ),
                        );
                        return;
                    };
                    store_type
                }
                _ => {
                    make_error_for_aggr(stores, None);
                    return;
                }
            }
        }
        TypeKind::Array { .. }
        | TypeKind::Struct(_)
        | TypeKind::GenericStructInstance(_)
        | TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => {
            make_error_for_aggr(stores, None);
            return;
        }
    };

    let ptr_type = stores
        .types
        .get_single_pointer(stores.strings, store_type_id);

    stores.values.set_value_type(output_value_id, ptr_type.id);
}

pub(crate) fn insert_array(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    emit_array: bool,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let inputs @ [data_value_id, array_value_id, idx_value_id] = *op_data.inputs.as_arr();
    let Some(type_ids @ [data_type_id, array_type_id, _]) = stores.values.value_types(inputs)
    else {
        return;
    };
    let [data_type_info, array_type_info, idx_type_info] =
        type_ids.map(|id| stores.types.get_type_info(id));

    if emit_array {
        let output_id = op_data.outputs[0];
        stores.values.set_value_type(output_id, array_type_id);
    }

    let mut make_error_for_aggr = |stores: &mut Stores, note| {
        let value_type_name = stores.strings.resolve(array_type_info.friendly_name);

        let mut diag =
            Diagnostic::error(op_loc, format!("cannot insert into a `{value_type_name}`"))
                .with_label_chain(array_value_id, 1, value_type_name);

        if let Some(note) = note {
            diag.set_note(note);
        }

        diag.attached(stores.diags, item_id);

        had_error.set();
    };

    let store_type_id = match array_type_info.kind {
        TypeKind::Array { type_id, .. } => type_id,
        TypeKind::MultiPointer(sub_type) | TypeKind::SinglePointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            match ptr_type_info.kind {
                TypeKind::Array { type_id, .. } => type_id,
                TypeKind::Struct(struct_item_id)
                | TypeKind::GenericStructInstance(struct_item_id) => {
                    if pass_manager
                        .ensure_define_structs(stores, struct_item_id)
                        .is_err()
                    {
                        had_error.set();
                        return;
                    };
                    let Some(store_type) = is_slice_like_struct(stores, ptr_type_info) else {
                        make_error_for_aggr(
                            stores,
                            Some(
                                "Struct must be slice-like (must have a pointer and length field)"
                                    .to_owned(),
                            ),
                        );
                        return;
                    };
                    store_type
                }
                _ => {
                    make_error_for_aggr(stores, None);
                    return;
                }
            }
        }
        TypeKind::Struct(struct_item_id) | TypeKind::GenericStructInstance(struct_item_id) => {
            if pass_manager
                .ensure_define_structs(stores, struct_item_id)
                .is_err()
            {
                had_error.set();
                return;
            };

            let Some(store_type) = is_slice_like_struct(stores, array_type_info) else {
                make_error_for_aggr(
                    stores,
                    Some(
                        "Struct must be slice-like (must have a pointer and length field)"
                            .to_owned(),
                    ),
                );
                return;
            };
            store_type
        }
        TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => {
            make_error_for_aggr(stores, None);
            return;
        }
    };

    let store_type_info = stores.types.get_type_info(store_type_id);

    if !idx_type_info.kind.is_unsigned_int() {
        let idx_type_name = stores.strings.resolve(idx_type_info.friendly_name);

        Diagnostic::error(
            op_loc,
            format!("cannot index an array with `{idx_type_name}`"),
        )
        .with_label_chain(idx_value_id, 2, idx_type_name)
        .attached(stores.diags, item_id);

        had_error.set();
    }

    if data_type_id != store_type_id
        && !matches!(
            (store_type_info.kind, data_type_info.kind),
            (TypeKind::Integer(to), TypeKind::Integer(from)) if can_promote_int_unidirectional(from, to)
        )
    {
        let data_type_name = stores.strings.resolve(data_type_info.friendly_name);
        let array_type_name = match array_type_info.kind {
            TypeKind::Array { .. } => stores.strings.resolve(array_type_info.friendly_name),
            TypeKind::MultiPointer(sub_type_id) | TypeKind::SinglePointer(sub_type_id) => {
                let sub_type_info = stores.types.get_type_info(sub_type_id);
                stores.strings.resolve(sub_type_info.friendly_name)
            }
            _ => unreachable!(),
        };

        Diagnostic::error(
            op_loc,
            format!("cannot store a value of type `{data_type_name}` in an array of type `{array_type_name}`"),
        )
        .with_label_chain(data_value_id, 0, data_type_name)
        .with_label_chain(array_value_id, 1, array_type_name)
        .attached(stores.diags, item_id);

        had_error.set();
    }
}

pub(crate) fn insert_struct(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    field_name: Spanned<Spur>,
    emit_struct: bool,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let inputs @ [data_value_id, input_struct_value_id] = *op_data.inputs.as_arr();
    let Some(type_ids @ [data_type_id, input_struct_type_id]) = stores.values.value_types(inputs)
    else {
        return;
    };
    let [data_type_info, input_struct_info] = type_ids.map(|id| stores.types.get_type_info(id));

    if emit_struct {
        let output_id = op_data.outputs[0];
        stores
            .values
            .set_value_type(output_id, input_struct_type_id);
    }

    let (actual_struct_type_id, actual_struct_item_id) = match input_struct_info.kind {
        TypeKind::Struct(struct_item_id) | TypeKind::GenericStructInstance(struct_item_id) => {
            (input_struct_type_id, struct_item_id)
        }
        TypeKind::MultiPointer(sub_type) | TypeKind::SinglePointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            let (TypeKind::Struct(struct_item_id)
            | TypeKind::GenericStructInstance(struct_item_id)) = ptr_type_info.kind
            else {
                Diagnostic::not_a_struct(
                    stores,
                    item_id,
                    input_struct_info,
                    input_struct_value_id,
                    op_id,
                    "insert into",
                );
                had_error.set();
                return;
            };

            (sub_type, struct_item_id)
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::FunctionPointer => {
            Diagnostic::not_a_struct(
                stores,
                item_id,
                input_struct_info,
                input_struct_value_id,
                op_id,
                "insert into",
            );
            had_error.set();
            return;
        }
    };

    if pass_manager
        .ensure_define_structs(stores, actual_struct_item_id)
        .is_err()
    {
        had_error.set();
        return;
    }

    let struct_def = stores.types.get_struct_def(actual_struct_type_id).clone();
    let Some(field_info) = struct_def
        .fields
        .iter()
        .find(|fi| fi.name.inner == field_name.inner)
    else {
        Diagnostic::field_not_found(
            stores,
            item_id,
            field_name,
            &struct_def,
            input_struct_info,
            input_struct_value_id,
        );

        return;
    };

    let field_type_info = stores.types.get_type_info(field_info.kind.inner);

    if data_type_id != field_info.kind.inner
        && !matches!(
            (field_type_info.kind, data_type_info.kind),
            (
                TypeKind::Integer(to),
                TypeKind::Integer(from)
            ) if can_promote_int_unidirectional(from, to)
        )
    {
        let data_type_name = stores.strings.resolve(data_type_info.friendly_name);
        let struct_type_name = match input_struct_info.kind {
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                input_struct_info.friendly_name
            }
            TypeKind::MultiPointer(sub_type) | TypeKind::SinglePointer(sub_type) => {
                stores.types.get_type_info(sub_type).friendly_name
            }
            _ => unreachable!(),
        };
        let struct_type_name = stores.strings.resolve(struct_type_name);

        Diagnostic::error(
            op_loc,
            format!("cannot store a value of type `{data_type_name}` into `{struct_type_name}`"),
        )
        .with_help_label(field_info.name.location, "field defined here")
        .with_label_chain(data_value_id, 0, data_type_name)
        .with_label_chain(input_struct_value_id, 1, struct_type_name)
        .attached(stores.diags, item_id);

        had_error.set();
    }
}

pub(crate) fn load(stores: &mut Stores, had_error: &mut ErrorSignal, item_id: ItemId, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id).clone();
    let [inputs @ .., ptr_id] = op_data.inputs.as_slice() else {
        unreachable!()
    };
    let Some([ptr_type]) = stores.values.value_types([*ptr_id]) else {
        return;
    };
    let ptr_info = stores.types.get_type_info(ptr_type);

    match ptr_info.kind {
        TypeKind::MultiPointer(ptee_type_id) | TypeKind::SinglePointer(ptee_type_id) => {
            stores
                .values
                .set_value_type(op_data.outputs[0], ptee_type_id);
        }
        TypeKind::FunctionPointer => {
            let function_args = stores.types.get_function_pointer_args(ptr_info.id).clone();

            for (&expected_type_id, &input_value_id) in function_args.inputs.iter().zip(inputs) {
                let Some([actual_type_id]) = stores.values.value_types([input_value_id]) else {
                    continue;
                };

                if expected_type_id != actual_type_id {
                    let actual_type_info = stores.types.get_type_info(actual_type_id);
                    let expected_type_info = stores.types.get_type_info(expected_type_id);

                    if !matches!((actual_type_info.kind, expected_type_info.kind),
                        (
                            TypeKind::Integer(actual),
                            TypeKind::Integer(expected)
                        ) if can_promote_int_unidirectional(actual, expected)
                    ) && !matches!(
                        (actual_type_info.kind, expected_type_info.kind),
                        (TypeKind::Float(actual), TypeKind::Float(expected))
                        if can_promote_float_unidirectional(actual, expected)
                    ) {
                        let function_type_name = stores.strings.resolve(ptr_info.friendly_name);

                        let mut diag = Diagnostic::error(
                            stores.ops.get_token(op_id).location,
                            "procedure call signature mismatch",
                        )
                        .primary_label_message("called here")
                        .with_label_chain(
                            *ptr_id,
                            op_data.inputs.len().to_u64() - 1,
                            function_type_name,
                        );

                        let mut note = Table::new();
                        note.set_format(*TABLE_FORMAT);
                        note.set_titles(row!("Depth", "Expected", "Actual"));

                        let pairs = function_args.inputs.iter().zip(inputs).enumerate().rev();
                        for (idx, (expected, actual_id)) in pairs {
                            let value_type =
                                stores
                                    .values
                                    .value_types([*actual_id])
                                    .map_or("Unknown", |[v]| {
                                        let type_info = stores.types.get_type_info(v);
                                        stores.strings.resolve(type_info.friendly_name)
                                    });

                            diag.add_label_chain(*actual_id, idx.to_u64(), value_type);

                            let expected_type_info = stores.types.get_type_info(*expected);
                            let expected_name =
                                stores.strings.resolve(expected_type_info.friendly_name);
                            note.add_row(row!(
                                (inputs.len() - idx - 1).to_string(),
                                expected_name,
                                value_type
                            ));
                        }

                        diag.with_note(note.to_string())
                            .attached(stores.diags, item_id);

                        had_error.set();
                        break;
                    }
                }
            }

            let outputs = &op_data.outputs;
            for (&type_id, &value_id) in function_args.outputs.iter().zip(outputs) {
                stores.values.set_value_type(value_id, type_id);
            }
        }
        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::Enum(_)
        | TypeKind::GenericStructInstance(_) => {
            let ptr_type_name = stores.strings.resolve(ptr_info.friendly_name);
            let op_loc = stores.ops.get_token(op_id).location;

            Diagnostic::error(op_loc, "value must be a pointer")
                .with_label_chain(*ptr_id, 0, ptr_type_name)
                .attached(stores.diags, item_id);

            had_error.set();
        }
    }
}

pub(crate) fn pack_array(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    count: u8,
) {
    let op_loc = stores.ops.get_token(op_id).location;

    if count == 0 {
        Diagnostic::error(op_loc, "cannot pack an array of length 0")
            .attached(stores.diags, item_id);

        had_error.set();
        return;
    }

    let op_data = stores.ops.get_op_io(op_id);
    let [first, rest @ ..] = op_data.inputs.as_slice() else {
        unreachable!()
    };
    let Some([first_value_id]) = stores.values.value_types([*first]) else {
        return;
    };
    let expected_store_type = stores.types.get_type_info(first_value_id);

    for (&other_id, id) in rest.iter().zip(1..) {
        let Some([value_type_id]) = stores.values.value_types([other_id]) else {
            continue;
        };
        let value_type_info = stores.types.get_type_info(value_type_id);
        if value_type_id != expected_store_type.id
            && !matches!(
                (expected_store_type.kind, value_type_info.kind),
                (
                    TypeKind::Integer(to),
                    TypeKind::Integer(from)
                ) if can_promote_int_unidirectional(from, to)
            )
        {
            let type_info = stores.types.get_type_info(value_type_id);
            let other_value_name = stores.strings.resolve(type_info.friendly_name);
            let expected_value_name = stores.strings.resolve(expected_store_type.friendly_name);

            Diagnostic::error(
                op_loc,
                format!("unable to pack array: expect `{expected_value_name}`, found `{other_value_name}`"),
            )
            .with_note(format!("Expected `{expected_value_name}` because the first value is that type"))
            .with_label_chain(other_id, id, other_value_name)
            .with_label_chain(*first, 0, expected_value_name).attached(stores.diags, item_id);

            had_error.set();
        }
    }

    let array_type =
        stores
            .types
            .get_array(stores.strings, expected_store_type.id, count.to_usize());
    let output_id = op_data.outputs[0];
    stores.values.set_value_type(output_id, array_type.id);
}

pub(crate) fn store(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let [data_value_id, ptr_value_id] = *op_data.inputs.as_arr();
    let Some([data_type_id, ptr_type_id]) =
        stores.values.value_types([data_value_id, ptr_value_id])
    else {
        return;
    };
    let ptr_type_info = stores.types.get_type_info(ptr_type_id);
    let data_type_info = stores.types.get_type_info(data_type_id);

    let (TypeKind::MultiPointer(ptee_type_id) | TypeKind::SinglePointer(ptee_type_id)) =
        ptr_type_info.kind
    else {
        let ptr_type_name = stores.strings.resolve(ptr_type_info.friendly_name);
        let data_type_name = stores.strings.resolve(data_type_info.friendly_name);

        Diagnostic::error(
            op_loc,
            format!("found `{ptr_type_name}` expected a `{data_type_name}&`"),
        )
        .with_label_chain(ptr_value_id, 1, ptr_type_name)
        .attached(stores.diags, item_id);

        had_error.set();
        return;
    };

    let pointee_type_info = stores.types.get_type_info(ptee_type_id);
    let can_promote_int = matches!(
        (data_type_info.kind, pointee_type_info.kind),
        (TypeKind::Integer(from), TypeKind::Integer(to))
        if can_promote_int_unidirectional(from, to)
    );

    if data_type_id != ptee_type_id && !can_promote_int {
        let data_type_name = stores.strings.resolve(data_type_info.friendly_name);
        let ptee_type_info = stores.types.get_type_info(ptee_type_id);
        let ptee_type_name = stores.strings.resolve(ptee_type_info.friendly_name);

        Diagnostic::error(op_loc, format!("value must be a `{ptee_type_name}`"))
            .with_label_chain(data_value_id, 0, data_type_name)
            .attached(stores.diags, item_id);

        had_error.set();
    }
}

pub(crate) fn unpack(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let outputs: SmallVec<[_; 20]> = op_data.outputs.as_slice().into();
    let aggr_value_id = op_data.inputs[0];
    let Some([aggr_type_id]) = stores.values.value_types([aggr_value_id]) else {
        return;
    };
    let aggr_type_info = stores.types.get_type_info(aggr_type_id);

    match aggr_type_info.kind {
        TypeKind::Array { type_id, .. } => {
            for output_id in outputs {
                stores.values.set_value_type(output_id, type_id);
            }
        }
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            // The stack check already ensured definition.
            let struct_info = stores.types.get_struct_def(aggr_type_id);
            for (output_id, field_info) in outputs.iter().zip(&struct_info.fields) {
                stores
                    .values
                    .set_value_type(*output_id, field_info.kind.inner);
            }
        }
        TypeKind::Integer(_)
        | TypeKind::Float(_)
        | TypeKind::MultiPointer(_)
        | TypeKind::SinglePointer(_)
        | TypeKind::FunctionPointer
        | TypeKind::Bool
        | TypeKind::Enum(_)
        | TypeKind::GenericStructBase(_) => {
            let aggr_type_name = stores.strings.resolve(aggr_type_info.friendly_name);
            let op_loc = stores.ops.get_token(op_id).location;

            Diagnostic::error(
                op_loc,
                format!("expected array or struct, found `{aggr_type_name}`"),
            )
            .with_label_chain(aggr_value_id, 0, aggr_type_name)
            .attached(stores.diags, item_id);

            had_error.set();
        }
    }
}

pub(crate) fn pack_enum(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    enum_id: TypeId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    stores.values.set_value_type(op_data.outputs[0], enum_id);

    let op_loc = stores.ops.get_token(op_id);
    let discrim_value_id = op_data.inputs[0];
    let Some([discrim_type_id]) = stores.values.value_types([discrim_value_id]) else {
        return;
    };

    let discrim_type_info = stores.types.get_type_info(discrim_type_id);

    let TypeKind::Integer(int_kind) = discrim_type_info.kind else {
        let discrim_type_name = stores.strings.resolve(discrim_type_info.friendly_name);

        Diagnostic::error(
            op_loc.location,
            format!("found `{discrim_type_name}` expected a u16"),
        )
        .with_label_chain(discrim_value_id, 1, discrim_type_name)
        .attached(stores.diags, item_id);

        had_error.set();
        return;
    };

    if !can_promote_int_unidirectional(
        int_kind,
        IntKind {
            width: IntWidth::I16,
            signed: IntSignedness::Unsigned,
        },
    ) {
        let discrim_type_name = stores.strings.resolve(discrim_type_info.friendly_name);

        Diagnostic::error(op_loc.location, "value must be a `u16`")
            .with_label_chain(discrim_value_id, 0, discrim_type_name)
            .attached(stores.diags, item_id);

        had_error.set();
    }
}

pub(crate) fn pack_struct(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    op_id: OpId,
    struct_type_id: TypeId,
) {
    // Let's see if we can determine the field type from our inputs for generic structs.
    let struct_type_id = if let TypeKind::GenericStructBase(struct_item_id) =
        stores.types.get_type_info(struct_type_id).kind
    {
        let ControlFlow::Continue(id) = pack_struct_infer_generic(
            stores,
            had_error,
            item_id,
            struct_type_id,
            struct_item_id,
            op_id,
        ) else {
            return;
        };

        id
    } else {
        struct_type_id
    };

    let op_data = stores.ops.get_op_io(op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let inputs = &op_data.inputs;
    let struct_type_info = stores.types.get_struct_def(struct_type_id);

    if struct_type_info.is_union {
        let Some([input_type_id]) = stores.values.value_types([inputs[0]]) else {
            return;
        };

        let mut found_field = false;
        for field_def in &struct_type_info.fields {
            if input_type_id == field_def.kind.inner {
                found_field = true;
                break;
            }
        }

        if !found_field {
            let input_type_info = stores.types.get_type_info(input_type_id);
            let input_type_name = stores.strings.resolve(input_type_info.friendly_name);

            Diagnostic::error(op_loc, "unable to pack union")
                .with_help_label(
                    struct_type_info.name.location,
                    format!("expected a field with type `{input_type_name}` in this union"),
                )
                .with_label_chain(inputs[0], 0, input_type_name)
                .attached(stores.diags, item_id);

            had_error.set();
        }
    } else {
        for ((field_def, &input_value_id), value_idx) in
            struct_type_info.fields.iter().zip(inputs).zip(1..)
        {
            let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
                continue;
            };
            let field_type_info = stores.types.get_type_info(field_def.kind.inner);
            let input_type_info = stores.types.get_type_info(input_type_id);

            if input_type_id != field_def.kind.inner
                && !matches!(
                    (field_type_info.kind, input_type_info.kind),
                    (TypeKind::Integer(to), TypeKind::Integer(from))
                    if can_promote_int_unidirectional(from, to)
                )
            {
                let input_type_name = stores.strings.resolve(input_type_info.friendly_name);
                let field_type_name = stores.strings.resolve(field_type_info.friendly_name);

                Diagnostic::error(op_loc, "unable to pack struct: mismatched input types")
                    .with_note(format!(
                        "Expected type `{field_type_name}`, found `{input_type_name}`"
                    ))
                    .with_help_label(field_def.name.location, "expected type defined here...")
                    .with_help_label(struct_type_info.name.location, "... in this struct")
                    .with_label_chain(input_value_id, value_idx, input_type_name)
                    .attached(stores.diags, item_id);

                had_error.set();
            }
        }
    }

    let output_value_id = op_data.outputs[0];
    stores
        .values
        .set_value_type(output_value_id, struct_type_id);
}

fn pack_struct_infer_generic(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    struct_type_id: TypeId,
    struct_item_id: ItemId,
    op_id: OpId,
) -> ControlFlow<(), TypeId> {
    let generic_def = stores.types.get_generic_base_def(struct_type_id);
    let op_data = stores.ops.get_op_io(op_id);
    let op_loc = stores.ops.get_token(op_id).location;
    let inputs = &op_data.inputs;

    // We can't infer generic parameters for a union, as there may be multiple parameters, but we only
    // take a single input.
    let generic_params = &generic_def.generic_params;
    if generic_def.is_union && generic_params.len() != 1 {
        Diagnostic::error(
            op_loc,
            "unable to infer parameters of generic unions with more than 0 generic parameter",
        )
        .attached(stores.diags, item_id);

        had_error.set();
        return ControlFlow::Break(());
    }

    let mut param_types = Vec::new();

    if generic_def.is_union {
        let Some([input_type_id]) = stores.values.value_types([inputs[0]]) else {
            return ControlFlow::Break(());
        };

        // If we're a generic union, we won't be able to infer the generic paramater if our input is one of the
        // non-generic fields.
        for field in &generic_def.fields {
            let PartiallyResolvedType::Fixed(field_type_id) = field.kind.inner else {
                continue;
            };
            // We've found a fixed field, so we can't infer the generic parameter.
            if field_type_id == input_type_id {
                let input_type_info = stores.types.get_type_info(input_type_id);
                let input_type_name = stores.strings.resolve(input_type_info.friendly_name);

                Diagnostic::error(op_loc, "unable to infer type parameter of generic union")
                    .with_help_label(
                        field.name.location,
                        "input type matches this non-generic field",
                    )
                    .with_label_chain(inputs[0], 0, input_type_name)
                    .attached(stores.diags, item_id);

                had_error.set();
                return ControlFlow::Break(());
            }
        }

        param_types.push(input_type_id);
    } else {
        // Iterate over each of the generic parameters, then search each of the fields looking for a type
        // we can pattern match against to infer the generic type parameter.
        // We are looking for field types of the form `T`, `T&`, and `T[N]`.
        // If we find one such field, we break and go to the next generic parameter.
        let mut local_had_error = ErrorSignal::new();
        for param in generic_params {
            let mut found_field = false;
            for (field, &input_value_id) in generic_def.fields.iter().zip(inputs) {
                let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
                    continue;
                };
                let input_type_info = stores.types.get_type_info(input_type_id);

                let Some(inferred_type_id) =
                    field
                        .kind
                        .inner
                        .match_generic_type(stores, param.inner, input_type_info)
                else {
                    // Not an inferrable pattern.
                    continue;
                };

                param_types.push(inferred_type_id);
                found_field = true;
                break;
            }

            if !found_field {
                Diagnostic::error(op_loc, "Unable to infer type paramater")
                    .with_help_label(param.location, "this parameter")
                    .attached(stores.diags, item_id);

                local_had_error.set();
            }
        }

        if local_had_error.into_err() {
            had_error.set();
            return ControlFlow::Break(());
        }
    }

    let instance_type_info = stores.types.instantiate_generic_struct(
        stores.strings,
        struct_item_id,
        struct_type_id,
        param_types,
    );

    ControlFlow::Continue(instance_type_info.id)
}
