use std::ops::ControlFlow;

use ariadne::{Color, Label};
use intcast::IntCast;
use lasso::Spur;
use smallvec::SmallVec;

use crate::{
    context::{Context, ItemId},
    diagnostics,
    error_signal::ErrorSignal,
    n_ops::SliceNOps,
    pass_manager::{static_analysis::can_promote_int_unidirectional, PassContext},
    stores::{
        ops::OpId,
        source::Spanned,
        types::{GenericPartiallyResolvedFieldKind, Integer, TypeId, TypeInfo, TypeKind},
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
        let field_kind = stores.types.get_type_info(field.kind).kind;

        match field_kind {
            TypeKind::Integer(Integer::U64) if field.name.inner == length_spur => {
                has_valid_length_field = true
            }
            TypeKind::Pointer(ptr_id) if field.name.inner == pointer_spur => {
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
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
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

    let mut make_error_for_aggr = |stores: &mut Stores, note| {
        let value_type_name = stores.strings.resolve(array_type_info.friendly_name);
        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(array_value_id, 0, value_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op_loc,
            format!("cannot extract a `{value_type_name}`"),
            labels,
            note,
        );

        had_error.set();
    };

    let store_type = match array_type_info.kind {
        TypeKind::Array { type_id, .. } => type_id,
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            match ptr_type_info.kind {
                TypeKind::Array { type_id, .. } => type_id,
                TypeKind::Struct(item_id) | TypeKind::GenericStructInstance(item_id) => {
                    if pass_ctx
                        .ensure_define_structs(ctx, stores, item_id)
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

        TypeKind::Struct(item_id) | TypeKind::GenericStructInstance(item_id) => {
            if pass_ctx
                .ensure_define_structs(ctx, stores, item_id)
                .is_err()
            {
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
        TypeKind::Integer(_) | TypeKind::Bool | TypeKind::GenericStructBase(_) => {
            make_error_for_aggr(stores, None);
            return;
        }
    };

    if !idx_type_info.kind.is_unsigned_int() {
        let idx_type_name = stores.strings.resolve(idx_type_info.friendly_name);
        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(idx_value_id, 1, idx_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op_loc,
            format!("cannot index an array with `{idx_type_name}`"),
            labels,
            None,
        );
        had_error.set();
        return;
    }

    stores.values.set_value_type(output_value_id, store_type);
}

pub(crate) fn extract_struct(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
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

    let not_struct_error = || {
        let value_type_name = stores.strings.resolve(input_struct_type_info.friendly_name);
        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(input_struct_value_id, 1, value_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        let op_loc = stores.ops.get_token(op_id).location;
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op_loc,
            format!("cannot extract field from a `{value_type_name}`"),
            labels,
            None,
        );
    };

    let (actual_struct_type_id, actual_struct_item_id) = match input_struct_type_info.kind {
        TypeKind::Struct(struct_item_id) | TypeKind::GenericStructInstance(struct_item_id) => {
            (input_struct_type_id, struct_item_id)
        }
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            let (TypeKind::Struct(struct_item_id)
            | TypeKind::GenericStructInstance(struct_item_id)) = ptr_type_info.kind
            else {
                not_struct_error();
                had_error.set();
                return;
            };
            (sub_type, struct_item_id)
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_) => {
            not_struct_error();
            had_error.set();
            return;
        }
    };

    if pass_ctx
        .ensure_define_structs(ctx, stores, actual_struct_item_id)
        .is_err()
    {
        had_error.set();
        return;
    }

    let struct_def = stores.types.get_struct_def(actual_struct_type_id);
    let Some(field_info) = struct_def
        .fields
        .iter()
        .find(|fi| fi.name.inner == field_name.inner)
    else {
        let unknown_field_name = stores.strings.resolve(field_name.inner);
        let struct_name = stores.strings.resolve(struct_def.name.inner);

        let value_type_name = stores.strings.resolve(input_struct_type_info.friendly_name);
        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(input_struct_value_id, 1, value_type_name)],
            Color::Yellow,
            Color::Cyan,
        );

        labels.extend([
            Label::new(field_name.location).with_color(Color::Red),
            Label::new(struct_def.name.location)
                .with_color(Color::Cyan)
                .with_message("struct defined here"),
        ]);

        diagnostics::emit_error(
            stores,
            field_name.location,
            format!("unknown field `{unknown_field_name}` in struct `{struct_name}`"),
            labels,
            None,
        );

        had_error.set();
        return;
    };

    stores
        .values
        .set_value_type(output_data_id, field_info.kind);
}

pub(crate) fn insert_array(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
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
        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(array_value_id, 1, value_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op_loc,
            format!("cannot insert into a `{value_type_name}`"),
            labels,
            note,
        );

        had_error.set();
    };

    let store_type_id = match array_type_info.kind {
        TypeKind::Array { type_id, .. } => type_id,
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            match ptr_type_info.kind {
                TypeKind::Array { type_id, .. } => type_id,
                TypeKind::Struct(struct_item_id)
                | TypeKind::GenericStructInstance(struct_item_id) => {
                    if pass_ctx
                        .ensure_define_structs(ctx, stores, struct_item_id)
                        .is_err()
                    {
                        had_error.set();
                        return;
                    };
                    let Some(store_type) = is_slice_like_struct(stores, ptr_type_info) else {
                        make_error_for_aggr(
                            stores,
                            Some(
                                "Struct must be slice-like (must have a pointer and length field"
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
            if pass_ctx
                .ensure_define_structs(ctx, stores, struct_item_id)
                .is_err()
            {
                had_error.set();
                return;
            };

            let Some(store_type) = is_slice_like_struct(stores, array_type_info) else {
                make_error_for_aggr(
                    stores,
                    Some(
                        "Struct must be slice-like (must have a pointer and length field"
                            .to_owned(),
                    ),
                );
                return;
            };
            store_type
        }
        TypeKind::Integer(_) | TypeKind::Bool | TypeKind::GenericStructBase(_) => {
            make_error_for_aggr(stores, None);
            return;
        }
    };

    let store_type_info = stores.types.get_type_info(store_type_id);

    if !idx_type_info.kind.is_unsigned_int() {
        let idx_type_name = stores.strings.resolve(idx_type_info.friendly_name);
        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(idx_value_id, 2, idx_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op_loc,
            format!("cannot index an array with `{idx_type_name}`"),
            labels,
            None,
        );

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
            TypeKind::Pointer(sub_type_id) => {
                let sub_type_info = stores.types.get_type_info(sub_type_id);
                stores.strings.resolve(sub_type_info.friendly_name)
            }
            _ => unreachable!(),
        };
        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [
                (data_value_id, 0, data_type_name),
                (array_value_id, 1, array_type_name),
            ],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op_loc,
            format!("cannot store a value of type `{data_type_name}` in an array of type `{array_type_name}`"),
            labels,
            None
        );

        had_error.set();
    }
}

pub(crate) fn insert_struct(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
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

    let not_struct_error = || {
        let value_type_name = stores.strings.resolve(input_struct_info.friendly_name);
        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(input_struct_value_id, 1, value_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op_loc,
            format!("cannot insert field into a `{value_type_name}`"),
            labels,
            None,
        );
    };

    let (actual_struct_type_id, actual_struct_item_id) = match input_struct_info.kind {
        TypeKind::Struct(struct_item_id) | TypeKind::GenericStructInstance(struct_item_id) => {
            (input_struct_type_id, struct_item_id)
        }
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            let (TypeKind::Struct(struct_item_id)
            | TypeKind::GenericStructInstance(struct_item_id)) = ptr_type_info.kind
            else {
                not_struct_error();
                had_error.set();
                return;
            };

            (sub_type, struct_item_id)
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_) => {
            not_struct_error();
            had_error.set();
            return;
        }
    };

    if pass_ctx
        .ensure_define_structs(ctx, stores, actual_struct_item_id)
        .is_err()
    {
        had_error.set();
        return;
    }

    let struct_type_info = stores.types.get_struct_def(actual_struct_type_id);
    let Some(field_info) = struct_type_info
        .fields
        .iter()
        .find(|fi| fi.name.inner == field_name.inner)
    else {
        let unknown_field_name = stores.strings.resolve(field_name.inner);
        let struct_name = stores.strings.resolve(struct_type_info.name.inner);
        let value_type_name = stores.strings.resolve(input_struct_info.friendly_name);

        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(input_struct_value_id, 1, value_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.extend([
            Label::new(field_name.location).with_color(Color::Red),
            Label::new(struct_type_info.name.location)
                .with_color(Color::Cyan)
                .with_message("struct defined here"),
        ]);

        diagnostics::emit_error(
            stores,
            field_name.location,
            format!("unknown field `{unknown_field_name}` in struct `{struct_name}`"),
            labels,
            None,
        );

        return;
    };

    let field_type_info = stores.types.get_type_info(field_info.kind);

    if data_type_id != field_info.kind
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
            TypeKind::Pointer(sub_type) => stores.types.get_type_info(sub_type).friendly_name,
            _ => unreachable!(),
        };
        let struct_type_name = stores.strings.resolve(struct_type_name);

        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [
                (data_value_id, 0, data_type_name),
                (input_struct_value_id, 1, struct_type_name),
            ],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op_loc).with_color(Color::Red));
        labels.push(
            Label::new(field_info.name.location)
                .with_color(Color::Cyan)
                .with_message("field defined here"),
        );

        diagnostics::emit_error(
            stores,
            op_loc,
            format!("cannot store a value of type `{data_type_name}` into `{struct_type_name}`"),
            labels,
            None,
        );

        had_error.set();
    }
}

pub(crate) fn load(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let ptr_id = op_data.inputs[0];
    let Some([ptr_type]) = stores.values.value_types([ptr_id]) else {
        return;
    };
    let ptr_info = stores.types.get_type_info(ptr_type);

    let TypeKind::Pointer(ptee_type_id) = ptr_info.kind else {
        let ptr_type_name = stores.strings.resolve(ptr_info.friendly_name);

        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(ptr_id, 0, ptr_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        let op_loc = stores.ops.get_token(op_id).location;
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(stores, op_loc, "value must be a pointer", labels, None);

        had_error.set();
        return;
    };

    stores
        .values
        .set_value_type(op_data.outputs[0], ptee_type_id);
}

pub(crate) fn pack_array(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId, count: u8) {
    let op_loc = stores.ops.get_token(op_id).location;

    if count == 0 {
        diagnostics::emit_error(
            stores,
            op_loc,
            "cannot pack an array of length 0",
            [Label::new(op_loc).with_color(Color::Red)],
            None,
        );

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

            let mut labels = diagnostics::build_creator_label_chain(
                stores,
                [
                    (other_id, id, other_value_name),
                    (*first, 0, expected_value_name),
                ],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(op_loc).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op_loc,
                format!("unable to pack array: expect `{expected_value_name}`, found `{other_value_name}`"),
                labels,
                format!("Expected `{expected_value_name}` because the first value is that type")
            );
            had_error.set();
        }
    }

    let array_type = stores.types.get_array(
        &mut stores.strings,
        expected_store_type.id,
        count.to_usize(),
    );
    let output_id = op_data.outputs[0];
    stores.values.set_value_type(output_id, array_type.id);
}

pub(crate) fn store(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId) {
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

    let TypeKind::Pointer(ptee_type_id) = ptr_type_info.kind else {
        let ptr_type_name = stores.strings.resolve(ptr_type_info.friendly_name);
        let data_type_name = stores.strings.resolve(data_type_info.friendly_name);

        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(ptr_value_id, 1, ptr_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op_loc,
            format!("found `{ptr_type_name}` expected a `{data_type_name}&`"),
            labels,
            None,
        );

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
        let ptee_type_name = stores.strings.resolve(ptr_type_info.friendly_name);

        let mut labels = diagnostics::build_creator_label_chain(
            stores,
            [(data_value_id, 0, data_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op_loc).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op_loc,
            format!("value must be a `{ptee_type_name}`"),
            labels,
            None,
        );

        had_error.set();
    }
}

pub(crate) fn unpack(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId) {
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
                stores.values.set_value_type(*output_id, field_info.kind);
            }
        }
        TypeKind::Integer(_)
        | TypeKind::Pointer(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_) => {
            let aggr_type_name = stores.strings.resolve(aggr_type_info.friendly_name);

            let mut labels = diagnostics::build_creator_label_chain(
                stores,
                [(aggr_value_id, 0, aggr_type_name)],
                Color::Yellow,
                Color::Cyan,
            );
            let op_loc = stores.ops.get_token(op_id).location;
            labels.push(Label::new(op_loc).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op_loc,
                format!("expected array or struct, found `{aggr_type_name}`"),
                labels,
                None,
            );

            had_error.set();
        }
    }
}

pub(crate) fn pack_struct(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    struct_type_id: TypeId,
) {
    // Let's see if we can determine the field type from our inputs for generic structs.
    let struct_type_id = if let TypeKind::GenericStructBase(struct_item_id) =
        stores.types.get_type_info(struct_type_id).kind
    {
        let ControlFlow::Continue(id) =
            pack_struct_infer_generic(stores, had_error, struct_type_id, struct_item_id, op_id)
        else {
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
            if input_type_id == field_def.kind {
                found_field = true;
                break;
            }
        }

        if !found_field {
            let input_type_info = stores.types.get_type_info(input_type_id);
            let input_type_name = stores.strings.resolve(input_type_info.friendly_name);

            let mut labels = diagnostics::build_creator_label_chain(
                stores,
                [(inputs[0], 0, input_type_name)],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(
                Label::new(struct_type_info.name.location)
                    .with_color(Color::Cyan)
                    .with_message(format!(
                        "expected a field with type `{input_type_name}` in this union"
                    )),
            );
            labels.push(Label::new(op_loc).with_color(Color::Red));

            diagnostics::emit_error(stores, op_loc, "unable to pack union", labels, None);

            had_error.set();
        }
    } else {
        for ((field_def, &input_value_id), value_idx) in
            struct_type_info.fields.iter().zip(inputs).zip(1..)
        {
            let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
                continue;
            };
            let field_type_info = stores.types.get_type_info(field_def.kind);
            let input_type_info = stores.types.get_type_info(input_type_id);

            if input_type_id != field_def.kind
                && !matches!(
                    (field_type_info.kind, input_type_info.kind),
                    (TypeKind::Integer(to), TypeKind::Integer(from))
                    if can_promote_int_unidirectional(from, to)
                )
            {
                let input_type_name = stores.strings.resolve(input_type_info.friendly_name);
                let field_type_name = stores.strings.resolve(field_type_info.friendly_name);

                let mut labels = diagnostics::build_creator_label_chain(
                    stores,
                    [(input_value_id, value_idx, input_type_name)],
                    Color::Yellow,
                    Color::Cyan,
                );
                labels.push(
                    Label::new(field_def.name.location)
                        .with_color(Color::Cyan)
                        .with_message("expected type defined here..."),
                );
                labels.push(
                    Label::new(struct_type_info.name.location)
                        .with_color(Color::Cyan)
                        .with_message("... in this struct"),
                );
                labels.push(Label::new(op_loc).with_color(Color::Red));

                diagnostics::emit_error(
                    stores,
                    op_loc,
                    "unable to pack struct: mismatched input types",
                    labels,
                    format!("Expected type `{field_type_name}`, found `{input_type_name}`"),
                );

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
    if generic_def.is_union && generic_def.generic_params.len() != 1 {
        diagnostics::emit_error(
            stores,
            op_loc,
            "unable to infer parameters of generic unions with more than 1 generic parameter",
            [Label::new(op_loc).with_color(Color::Red)],
            None,
        );

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
            let GenericPartiallyResolvedFieldKind::Fixed(field_type_id) = field.kind else {
                continue;
            };
            // We've found a fixed field, so we can't infer the generic parameter.
            if field_type_id == input_type_id {
                let input_type_info = stores.types.get_type_info(input_type_id);
                let input_type_name = stores.strings.resolve(input_type_info.friendly_name);

                let mut labels = diagnostics::build_creator_label_chain(
                    stores,
                    [(inputs[0], 0, input_type_name)],
                    Color::Yellow,
                    Color::Cyan,
                );
                labels.push(
                    Label::new(field.name.location)
                        .with_color(Color::Green)
                        .with_message("input type matches this non-generic field"),
                );
                labels.push(Label::new(op_loc).with_color(Color::Red));

                diagnostics::emit_error(
                    stores,
                    op_loc,
                    "unable to infer type parameter of generic union",
                    labels,
                    None,
                );

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
        for param in &generic_def.generic_params {
            let mut found_field = false;
            for (field, &input_value_id) in generic_def.fields.iter().zip(inputs) {
                let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
                    continue;
                };
                let input_type_info = stores.types.get_type_info(input_type_id);

                let Some(inferred_type_id) =
                    field
                        .kind
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
                diagnostics::emit_error(
                    stores,
                    op_loc,
                    "unable to infer type parameter",
                    [
                        Label::new(op_loc).with_color(Color::Red),
                        Label::new(param.location).with_color(Color::Cyan),
                    ],
                    None,
                );

                local_had_error.set();
            }
        }

        if local_had_error.into_bool() {
            had_error.set();
            return ControlFlow::Break(());
        }
    }

    let instance_type_info = stores.types.instantiate_generic_struct(
        &mut stores.strings,
        struct_item_id,
        struct_type_id,
        param_types,
    );

    ControlFlow::Continue(instance_type_info.id)
}
