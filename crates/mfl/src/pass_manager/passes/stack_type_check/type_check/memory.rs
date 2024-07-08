use ariadne::{Color, Label};
use lasso::Spur;

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

    let (actual_struct_type_id, actual_struct_item_id) = match input_struct_type_info.kind {
        TypeKind::Struct(struct_item_id) | TypeKind::GenericStructInstance(struct_item_id) => {
            (input_struct_type_id, struct_item_id)
        }
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            let (TypeKind::Struct(struct_item_id)
            | TypeKind::GenericStructInstance(struct_item_id)) = ptr_type_info.kind
            else {
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

                *had_error = true;
                return;
            };
            (sub_type, struct_item_id)
        }

        TypeKind::Array { .. }
        | TypeKind::Integer(_)
        | TypeKind::Bool
        | TypeKind::GenericStructBase(_) => {
            let value_type_name = stores.strings.resolve(input_struct_type_info.name);
            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [(input_struct_value_id, 0, value_type_name)],
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
