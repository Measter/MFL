use ariadne::{Color, Label};
use intcast::IntCast;
use lasso::Spur;
use smallvec::SmallVec;

use crate::{
    context::Context,
    diagnostics,
    ir::{Op, TypeResolvedOp},
    n_ops::SliceNOps,
    pass_manager::{
        static_analysis::{can_promote_int_unidirectional, Analyzer},
        PassContext,
    },
    source_file::Spanned,
    type_store::{Integer, TypeId, TypeInfo, TypeKind},
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
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
    emit_array: bool,
) {
    let op_data = analyzer.get_op_io(op.id).clone();
    let inputs @ [array_value_id, idx_value_id] = *op_data.inputs.as_arr();
    let Some(type_ids) = analyzer.value_types(inputs) else {
        return;
    };
    let [array_type_info, idx_type_info] = type_ids.map(|id| stores.types.get_type_info(id));

    let output_value_id = if emit_array {
        let output_array_id = op_data.outputs[0];
        analyzer.set_value_type(output_array_id, array_type_info.id);
        op_data.outputs[1]
    } else {
        op_data.outputs[0]
    };

    let mut make_error_for_aggr = |stores: &mut Stores, note| {
        let value_type_name = stores.strings.resolve(array_type_info.name);
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(array_value_id, 0, value_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
            format!("cannot extract a `{value_type_name}`"),
            labels,
            note,
        );

        *had_error = true;
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
                        *had_error = true;
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
                *had_error = true;
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
        let idx_type_name = stores.strings.resolve(idx_type_info.name);
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(idx_value_id, 1, idx_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
            format!("cannot index an array with `{idx_type_name}`"),
            labels,
            None,
        );
        *had_error = true;
        return;
    }

    analyzer.set_value_type(output_value_id, store_type);
}

pub(crate) fn extract_struct(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
    field_name: Spanned<Spur>,
    emit_struct: bool,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_struct_value_id = op_data.inputs[0];
    let Some([input_struct_type_id]) = analyzer.value_types([input_struct_value_id]) else {
        return;
    };
    let input_struct_type_info = stores.types.get_type_info(input_struct_type_id);

    let output_data_id = if emit_struct {
        let [output_struct_id, output_data_id] = *op_data.outputs.as_arr();
        analyzer.set_value_type(output_struct_id, input_struct_type_id);
        output_data_id
    } else {
        op_data.outputs[0]
    };

    let not_struct_error = || {
        let value_type_name = stores.strings.resolve(input_struct_type_info.name);
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(input_struct_value_id, 1, value_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
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
                *had_error = true;
                return;
            };
            (sub_type, struct_item_id)
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_) => {
            not_struct_error();
            *had_error = true;
            return;
        }
    };

    if pass_ctx
        .ensure_define_structs(ctx, stores, actual_struct_item_id)
        .is_err()
    {
        *had_error = true;
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

        let value_type_name = stores.strings.resolve(input_struct_type_info.name);
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
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

        *had_error = true;
        return;
    };

    analyzer.set_value_type(output_data_id, field_info.kind);
}

pub(crate) fn insert_array(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
    emit_array: bool,
) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs @ [data_value_id, array_value_id, idx_value_id] = *op_data.inputs.as_arr();
    let Some(type_ids @ [data_type_id, array_type_id, _]) = analyzer.value_types(inputs) else {
        return;
    };
    let [data_type_info, array_type_info, idx_type_info] =
        type_ids.map(|id| stores.types.get_type_info(id));

    if emit_array {
        let output_id = op_data.outputs[0];
        analyzer.set_value_type(output_id, array_type_id);
    }

    let mut make_error_for_aggr = |stores: &mut Stores, note| {
        let value_type_name = stores.strings.resolve(array_type_info.name);
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(array_value_id, 1, value_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
            format!("cannot insert into a `{value_type_name}`"),
            labels,
            note,
        );

        *had_error = true;
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
                        *had_error = true;
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
                *had_error = true;
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
        let idx_type_name = stores.strings.resolve(idx_type_info.name);
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(idx_value_id, 2, idx_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
            format!("cannot index an array with `{idx_type_name}`"),
            labels,
            None,
        );

        *had_error = true;
    }

    if data_type_id != store_type_id
        && !matches!(
            (store_type_info.kind, data_type_info.kind),
            (TypeKind::Integer(to), TypeKind::Integer(from)) if can_promote_int_unidirectional(from, to)
        )
    {
        let data_type_name = stores.strings.resolve(data_type_info.name);
        let array_type_name = match array_type_info.kind {
            TypeKind::Array { .. } => stores.strings.resolve(array_type_info.name),
            TypeKind::Pointer(sub_type_id) => {
                let sub_type_info = stores.types.get_type_info(sub_type_id);
                stores.strings.resolve(sub_type_info.name)
            }
            _ => unreachable!(),
        };
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [
                (data_value_id, 0, data_type_name),
                (array_value_id, 1, array_type_name),
            ],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
            format!("cannot store a value of type `{data_type_name}` in an array of type `{array_type_name}`"),
            labels,
            None
        );

        *had_error = true;
    }
}

pub(crate) fn insert_struct(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
    field_name: Spanned<Spur>,
    emit_struct: bool,
) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs @ [data_value_id, input_struct_value_id] = *op_data.inputs.as_arr();
    let Some(type_ids @ [data_type_id, input_struct_type_id]) = analyzer.value_types(inputs) else {
        return;
    };
    let [data_type_info, input_struct_info] = type_ids.map(|id| stores.types.get_type_info(id));

    if emit_struct {
        let output_id = op_data.outputs[0];
        analyzer.set_value_type(output_id, input_struct_type_id);
    }

    let not_struct_error = || {
        let value_type_name = stores.strings.resolve(input_struct_info.name);
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(input_struct_value_id, 1, value_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
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
                *had_error = true;
                return;
            };

            (sub_type, struct_item_id)
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_) => {
            not_struct_error();
            *had_error = true;
            return;
        }
    };

    if pass_ctx
        .ensure_define_structs(ctx, stores, actual_struct_item_id)
        .is_err()
    {
        *had_error = true;
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
        let value_type_name = stores.strings.resolve(input_struct_info.name);

        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
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
        let data_type_name = stores.strings.resolve(data_type_info.name);
        let struct_type_name = match input_struct_info.kind {
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => input_struct_info.name,
            TypeKind::Pointer(sub_type) => stores.types.get_type_info(sub_type).name,
            _ => unreachable!(),
        };
        let struct_type_name = stores.strings.resolve(struct_type_name);

        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [
                (data_value_id, 0, data_type_name),
                (input_struct_value_id, 1, struct_type_name),
            ],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));
        labels.push(
            Label::new(field_info.name.location)
                .with_color(Color::Cyan)
                .with_message("field defined here"),
        );

        diagnostics::emit_error(
            stores,
            op.token.location,
            format!("cannot store a value of type `{data_type_name}` into `{struct_type_name}`"),
            labels,
            None,
        );

        *had_error = true;
    }
}

pub(crate) fn load(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let ptr_id = op_data.inputs[0];
    let Some([ptr_type]) = analyzer.value_types([ptr_id]) else {
        return;
    };
    let ptr_info = stores.types.get_type_info(ptr_type);

    let TypeKind::Pointer(ptee_type_id) = ptr_info.kind else {
        let ptr_type_name = stores.strings.resolve(ptr_info.name);

        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(ptr_id, 0, ptr_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
            "value must be a pointer",
            labels,
            None,
        );

        *had_error = true;
        return;
    };

    analyzer.set_value_type(op_data.outputs[0], ptee_type_id);
}

pub(crate) fn pack_array(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
    count: u8,
) {
    if count == 0 {
        diagnostics::emit_error(
            stores,
            op.token.location,
            "cannot pack an array of length 0",
            [Label::new(op.token.location).with_color(Color::Red)],
            None,
        );

        *had_error = true;
        return;
    }

    let op_data = analyzer.get_op_io(op.id);
    let [first, rest @ ..] = op_data.inputs.as_slice() else {
        unreachable!()
    };
    let Some([first_value_id]) = analyzer.value_types([*first]) else {
        return;
    };
    let expected_store_type = stores.types.get_type_info(first_value_id);

    for (&other_id, id) in rest.iter().zip(1..) {
        let Some([value_type_id]) = analyzer.value_types([other_id]) else {
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
            let other_value_name = stores.strings.resolve(type_info.name);
            let expected_value_name = stores.strings.resolve(expected_store_type.name);

            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [
                    (other_id, id, other_value_name),
                    (*first, 0, expected_value_name),
                ],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op.token.location,
                format!("unable to pack array: expect `{expected_value_name}`, found `{other_value_name}`"),
                labels,
                format!("Expected `{expected_value_name}` because the first value is that type")
            );
            *had_error = true;
        }
    }

    let array_type = stores.types.get_array(
        &mut stores.strings,
        expected_store_type.id,
        count.to_usize(),
    );
    let output_id = op_data.outputs[0];
    analyzer.set_value_type(output_id, array_type.id);
}

pub(crate) fn store(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let [data_value_id, ptr_value_id] = *op_data.inputs.as_arr();
    let Some([data_type_id, ptr_type_id]) = analyzer.value_types([data_value_id, ptr_value_id])
    else {
        return;
    };
    let ptr_type_info = stores.types.get_type_info(ptr_type_id);
    let data_type_info = stores.types.get_type_info(data_type_id);

    let TypeKind::Pointer(ptee_type_id) = ptr_type_info.kind else {
        let ptr_type_name = stores.strings.resolve(ptr_type_info.name);
        let data_type_name = stores.strings.resolve(data_type_info.name);

        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(ptr_value_id, 1, ptr_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
            format!("found `{ptr_type_name}` expected a `{data_type_name}&`"),
            labels,
            None,
        );

        *had_error = true;
        return;
    };

    let pointee_type_info = stores.types.get_type_info(ptee_type_id);
    let can_promote_int = matches!(
        (data_type_info.kind, pointee_type_info.kind),
        (TypeKind::Integer(from), TypeKind::Integer(to))
        if can_promote_int_unidirectional(from, to)
    );

    if data_type_id != ptee_type_id && !can_promote_int {
        let data_type_name = stores.strings.resolve(data_type_info.name);
        let ptee_type_name = stores.strings.resolve(ptr_type_info.name);

        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(data_value_id, 0, data_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
            format!("value must be a `{ptee_type_name}`"),
            labels,
            None,
        );

        *had_error = true;
    }
}

pub(crate) fn unpack(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);
    let outputs: SmallVec<[_; 20]> = op_data.outputs.as_slice().into();
    let aggr_value_id = op_data.inputs[0];
    let Some([aggr_type_id]) = analyzer.value_types([aggr_value_id]) else {
        return;
    };
    let aggr_type_info = stores.types.get_type_info(aggr_type_id);

    match aggr_type_info.kind {
        TypeKind::Array { type_id, .. } => {
            for output_id in outputs {
                analyzer.set_value_type(output_id, type_id);
            }
        }
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            // The stack check already ensured definition.
            let struct_info = stores.types.get_struct_def(aggr_type_id);
            for (output_id, field_info) in outputs.iter().zip(&struct_info.fields) {
                analyzer.set_value_type(*output_id, field_info.kind);
            }
        }
        TypeKind::Integer(_)
        | TypeKind::Pointer(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_) => {
            let aggr_type_name = stores.strings.resolve(aggr_type_info.name);

            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [(aggr_value_id, 0, aggr_type_name)],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op.token.location,
                format!("expected array or struct, found `{aggr_type_name}`"),
                labels,
                None,
            );

            *had_error = true;
        }
    }
}