use ariadne::{Color, Label};
use intcast::IntCast;
use lasso::Spur;

use crate::{
    diagnostics,
    n_ops::SliceNOps,
    opcode::Op,
    program::{
        static_analysis::{can_promote_int_unidirectional, Analyzer, ConstVal, PtrId},
        Program,
    },
    source_file::Spanned,
    type_store::{GenericPartiallyResolvedFieldKind, Integer, TypeId, TypeInfo, TypeKind},
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

pub fn pack_array(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op,
    count: u8,
) {
    if count == 0 {
        diagnostics::emit_error(
            stores,
            op.token.location,
            "cannot pack array of length 0",
            [Label::new(op.token.location).with_color(Color::Red)],
            None,
        );
        *had_error = true;
        return;
    }

    let op_data = analyzer.get_op_io(op.id);
    let [first, rest @ ..] = op_data.inputs() else {
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
                    TypeKind::Integer (to),
                    TypeKind::Integer (from)
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
                format!("unable to pack array: expected `{expected_value_name}`, found `{other_value_name}`"),
                labels,
                format!("Expected `{expected_value_name}` because the first value is that type"),
            );

            *had_error = true;
        }
    }

    let array_type = stores.types.get_array(
        &mut stores.strings,
        expected_store_type.id,
        count.to_usize(),
    );
    let output_id = op_data.outputs()[0];
    analyzer.set_value_type(output_id, array_type.id);
}

pub fn pack_struct(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op,
    type_id: TypeId,
) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs = op_data.inputs();

    // Let's see if we can determine the field types from our inputs.
    let type_id = if let TypeKind::GenericStructBase(item_id) =
        stores.types.get_type_info(type_id).kind
    {
        let generic_def = stores.types.get_generic_base_def(type_id);

        // We can't infer generic parameters for a union, as there may be multiple parameters, but we only
        // take a single input.
        // TODO: Handle instance of a union having a single generic parameter.
        if generic_def.is_union && generic_def.generic_params.len() != 1 {
            *had_error = true;
            diagnostics::emit_error(
                    stores,
                    op.token.location,
                    "unable to infer type paramaters of generic unions with more than 1 generic paramater",
                    [Label::new(op.token.location).with_color(Color::Red)],
                    None,
                );

            return;
        }

        // If we are a union, double-check that none of the non-generic fields are our input type.
        if generic_def.is_union {
            let Some([input_type]) = analyzer.value_types([inputs[0]]) else {
                return;
            };
            for field in &generic_def.fields {
                let GenericPartiallyResolvedFieldKind::Fixed(field_type_id) = field.kind else {
                    continue;
                };
                // We've found a fixed field, so we can't infer the generic parameter.
                if field_type_id == input_type {
                    *had_error = true;

                    let type_info = stores.types.get_type_info(input_type);
                    let other_value_type_name = stores.strings.resolve(type_info.name);
                    let mut labels = diagnostics::build_creator_label_chain(
                        analyzer,
                        [(inputs[0], 0, other_value_type_name)],
                        Color::Yellow,
                        Color::Cyan,
                    );
                    labels.push(
                        Label::new(field.name.location)
                            .with_color(Color::Green)
                            .with_message("Input type matches this non-generic field"),
                    );
                    labels.push(Label::new(op.token.location).with_color(Color::Red));

                    diagnostics::emit_error(
                        stores,
                        op.token.location,
                        "unable to infer type paramater of generic union",
                        labels,
                        None,
                    );

                    return;
                }
            }
        }

        let mut param_types = Vec::new();

        for param in &generic_def.generic_params {
            let mut found_field = false;
            for (field, input_id) in generic_def.fields.iter().zip(inputs) {
                let Some([input_type]) = analyzer.value_types([*input_id]) else {
                    continue;
                };
                let input_type_kind = stores.types.get_type_info(input_type).kind;

                let Some(type_id) =
                    field
                        .kind
                        .match_generic_type(param.inner, input_type, input_type_kind)
                else {
                    continue;
                };

                param_types.push(type_id);
                found_field = true;
                break;
            }

            if !found_field {
                *had_error = true;
                diagnostics::emit_error(
                    stores,
                    op.token.location,
                    "Unable to infer type parameter",
                    [
                        Label::new(op.token.location).with_color(Color::Red),
                        Label::new(param.location).with_color(Color::Cyan),
                    ],
                    None,
                );
            }
        }

        stores
            .types
            .instantiate_generic_struct(&mut stores.strings, item_id, type_id, param_types)
            .id
    } else {
        type_id
    };

    let struct_info = stores.types.get_struct_def(type_id);

    if struct_info.is_union {
        let Some([input_type_id]) = analyzer.value_types([inputs[0]]) else {
            return;
        };

        let mut found_field = false;
        for field_def in &struct_info.fields {
            let expected_store_type = stores.types.get_type_info(field_def.kind);
            if input_type_id == expected_store_type.id {
                found_field = true;
                break;
            }
        }

        if !found_field {
            let type_info = stores.types.get_type_info(input_type_id);
            let other_value_type_name = stores.strings.resolve(type_info.name);
            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [(inputs[0], 0, other_value_type_name)],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(
                Label::new(struct_info.name.location)
                    .with_color(Color::Cyan)
                    .with_message("Expected a field type defined in this union"),
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op.token.location,
                "unable to pack union",
                labels,
                None,
            );

            *had_error = true;
        }
    } else {
        for ((field_def, &input_id), val_id) in struct_info.fields.iter().zip(inputs).zip(1..) {
            let Some([input_type_id]) = analyzer.value_types([input_id]) else {
                continue;
            };
            let expected_store_type = stores.types.get_type_info(field_def.kind);
            let value_type_info = stores.types.get_type_info(input_type_id);

            if input_type_id != field_def.kind
                && !matches!(
                    (expected_store_type.kind, value_type_info.kind),
                    (
                        TypeKind::Integer (to),
                        TypeKind::Integer (from)
                    ) if can_promote_int_unidirectional(from, to)
                )
            {
                let type_info = stores.types.get_type_info(input_type_id);
                let other_value_type_name = stores.strings.resolve(type_info.name);
                let expected_value_type_name = stores.strings.resolve(expected_store_type.name);
                let mut labels = diagnostics::build_creator_label_chain(
                    analyzer,
                    [(input_id, val_id, other_value_type_name)],
                    Color::Yellow,
                    Color::Cyan,
                );
                labels.push(
                    Label::new(field_def.name.location)
                        .with_color(Color::Cyan)
                        .with_message("Expected type defined here..."),
                );
                labels.push(
                    Label::new(struct_info.name.location)
                        .with_color(Color::Cyan)
                        .with_message("... in this struct"),
                );

                labels.push(Label::new(op.token.location).with_color(Color::Red));
                let note = format!(
                    "Expected type `{expected_value_type_name}`, found `{other_value_type_name}`"
                );

                diagnostics::emit_error(
                    stores,
                    op.token.location,
                    "unable to pack struct: mismatched input types",
                    labels,
                    note,
                );

                *had_error = true;
            }
        }
    }

    let output_id = op_data.outputs()[0];
    analyzer.set_value_type(output_id, type_id);
}

pub fn unpack(stores: &Stores, analyzer: &mut Analyzer, had_error: &mut bool, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let outputs = op_data.outputs().to_owned();
    let aggr_id = op_data.inputs()[0];
    let Some([aggr_type_id]) = analyzer.value_types([aggr_id]) else {
        return;
    };
    let aggr_info = stores.types.get_type_info(aggr_type_id);

    match aggr_info.kind {
        TypeKind::Array { type_id, .. } => {
            for output_id in outputs {
                analyzer.set_value_type(output_id, type_id);
            }
        }
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            let fields = stores.types.get_struct_def(aggr_type_id);
            for (output_id, field_info) in outputs.iter().zip(&fields.fields) {
                analyzer.set_value_type(*output_id, field_info.kind);
            }
        }
        _ => {
            let input_type_name = stores.strings.resolve(aggr_info.name);

            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [(aggr_id, 0, input_type_name)],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op.token.location,
                format!("expected array or struct, found {input_type_name}"),
                labels,
                None,
            );

            *had_error = true;
        }
    };
}

pub fn extract_array(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op,
    emit_array: bool,
) {
    let op_data = analyzer.get_op_io(op.id).clone();
    let inputs @ [array_value_id, idx_value_id] = *op_data.inputs().as_arr();
    let Some(type_ids) = analyzer.value_types(inputs) else {
        return;
    };
    let [array_type_info, idx_type_info] = type_ids.map(|id| stores.types.get_type_info(id));

    let output_value_id = if emit_array {
        let output_array_id = op_data.outputs()[0];
        analyzer.set_value_type(output_array_id, array_type_info.id);
        op_data.outputs()[1]
    } else {
        op_data.outputs()[0]
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
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                    if let Some(store_type) = is_slice_like_struct(stores, ptr_type_info) {
                        store_type
                    } else {
                        make_error_for_aggr(
                            stores,
                            Some(
                                "Struct must be slice-like (must have a pointer and length field"
                                    .to_owned(),
                            ),
                        );
                        return;
                    }
                }
                _ => {
                    make_error_for_aggr(stores, None);
                    return;
                }
            }
        }

        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            if let Some(store_type) = is_slice_like_struct(stores, array_type_info) {
                store_type
            } else {
                make_error_for_aggr(
                    stores,
                    Some(
                        "Struct must be slice-like (must have a pointer and length field)"
                            .to_owned(),
                    ),
                );
                return;
            }
        }

        TypeKind::Integer { .. } | TypeKind::Bool | TypeKind::GenericStructBase(_) => {
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

pub fn insert_array(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op,
    emit_array: bool,
) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs @ [data_value_id, array_value_id, idx_value_id] = *op_data.inputs().as_arr();
    let Some(type_ids @ [data_type_id, array_type_id, _]) = analyzer.value_types(inputs) else {
        return;
    };
    let [data_type_info, array_type_info, idx_type_info] =
        type_ids.map(|id| stores.types.get_type_info(id));

    if emit_array {
        let output_id = op_data.outputs()[0];
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
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                    if let Some(store_type) = is_slice_like_struct(stores, ptr_type_info) {
                        store_type
                    } else {
                        make_error_for_aggr(
                            stores,
                            Some(
                                "Struct must be slice-like (must have a pointer and length field)"
                                    .to_owned(),
                            ),
                        );
                        return;
                    }
                }
                _ => {
                    make_error_for_aggr(stores, None);
                    return;
                }
            }
        }

        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
            if let Some(store_type) = is_slice_like_struct(stores, array_type_info) {
                store_type
            } else {
                make_error_for_aggr(
                    stores,
                    Some(
                        "Struct must be slice-like (must have a pointer and length field)"
                            .to_owned(),
                    ),
                );
                return;
            }
        }

        TypeKind::Integer { .. } | TypeKind::Bool | TypeKind::GenericStructBase(_) => {
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
            (
                TypeKind::Integer (to),
                TypeKind::Integer (from)
            ) if can_promote_int_unidirectional(from, to)
        )
    {
        let data_type_name = stores.strings.resolve(data_type_info.name);
        let array_type_name = match array_type_info.kind {
            TypeKind::Array { .. } => stores.strings.resolve(array_type_info.name),
            TypeKind::Pointer(subtype_id) => {
                let sub_type_info = stores.types.get_type_info(subtype_id);
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
            None,
        );

        *had_error = true;
    }
}

pub fn insert_struct(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op,
    field_name: Spanned<Spur>,
    emit_struct: bool,
) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs @ [data_value_id, input_struct_value_id] = *op_data.inputs().as_arr();
    let Some(type_ids @ [data_type_id, input_struct_type_id]) = analyzer.value_types(inputs) else {
        return;
    };
    let [data_type_info, input_struct_type_info] =
        type_ids.map(|id| stores.types.get_type_info(id));

    if emit_struct {
        let output_id = op_data.outputs()[0];
        analyzer.set_value_type(output_id, input_struct_type_id);
    }

    let actual_struct_type_id = match input_struct_type_info.kind {
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => input_struct_type_id,
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            if let TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) = ptr_type_info.kind {
                sub_type
            } else {
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
                    format!("cannot insert field into a `{value_type_name}`"),
                    labels,
                    None,
                );

                *had_error = true;
                return;
            }
        }

        TypeKind::Integer { .. }
        | TypeKind::Bool
        | TypeKind::Array { .. }
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
                format!("cannot insert field into a `{value_type_name}`"),
                labels,
                None,
            );

            *had_error = true;
            return;
        }
    };

    let struct_type_info = stores.types.get_struct_def(actual_struct_type_id);
    let Some(field_info) = struct_type_info
        .fields
        .iter()
        .find(|fi| fi.name.inner == field_name.inner)
    else {
        *had_error = true;
        let unknown_field_name = stores.strings.resolve(field_name.inner);
        let struct_name = stores.strings.resolve(struct_type_info.name.inner);

        let value_type_name = stores.strings.resolve(input_struct_type_info.name);
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
                TypeKind::Integer (to),
                TypeKind::Integer (from)
            ) if can_promote_int_unidirectional(from, to)
        )
    {
        let data_type_name = stores.strings.resolve(data_type_info.name);
        let struct_type_name = match input_struct_type_info.kind {
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                stores.strings.resolve(input_struct_type_info.name)
            }
            TypeKind::Pointer(subtype_id) => {
                let sub_type_info = stores.types.get_type_info(subtype_id);
                stores.strings.resolve(sub_type_info.name)
            }
            _ => unreachable!(),
        };
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

pub fn extract_struct(
    stores: &Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op,
    field_name: Spanned<Spur>,
    emit_struct: bool,
) {
    let op_data = analyzer.get_op_io(op.id);
    let [input_struct_value_id] = *op_data.inputs().as_arr();
    let Some([input_struct_type_id]) = analyzer.value_types([input_struct_value_id]) else {
        return;
    };
    let input_struct_type_info = stores.types.get_type_info(input_struct_type_id);

    let output_data_id = if emit_struct {
        let [output_struct_id, output_data_id] = *op_data.outputs().as_arr();
        analyzer.set_value_type(output_struct_id, input_struct_type_id);
        output_data_id
    } else {
        op_data.outputs()[0]
    };

    let actual_struct_type_id = match input_struct_type_info.kind {
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => input_struct_type_id,
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = stores.types.get_type_info(sub_type);
            if let TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) = ptr_type_info.kind {
                sub_type
            } else {
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
            }
        }

        TypeKind::Integer { .. }
        | TypeKind::Bool
        | TypeKind::Array { .. }
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

    let struct_def = stores.types.get_struct_def(actual_struct_type_id);
    let Some(field_info) = struct_def
        .fields
        .iter()
        .find(|fi| fi.name.inner == field_name.inner)
    else {
        *had_error = true;
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
        return;
    };

    analyzer.set_value_type(output_data_id, field_info.kind);
}

pub fn load(stores: &Stores, analyzer: &mut Analyzer, had_error: &mut bool, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let ptr_id = op_data.inputs[0];
    let Some([ptr_type]) = analyzer.value_types([ptr_id]) else {
        return;
    };
    let ptr_info = stores.types.get_type_info(ptr_type);

    let TypeKind::Pointer(kind) = ptr_info.kind else {
        *had_error = true;

        let ptr_type_info = stores.types.get_type_info(ptr_type);
        let ptr_type_name = stores.strings.resolve(ptr_type_info.name);

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
        return;
    };

    analyzer.set_value_type(op_data.outputs[0], kind);
}

pub fn store(
    program: &Program,
    stores: &Stores,
    analyzer: &Analyzer,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let [data_id, ptr_id] = *op_data.inputs.as_arr::<2>();
    let Some([data_type, ptr_type]) = analyzer.value_types([data_id, ptr_id]) else {
        return;
    };
    let ptr_type_info = stores.types.get_type_info(ptr_type);

    let TypeKind::Pointer(pointee_type) = ptr_type_info.kind else {
        *had_error = true;
        let ptr_type_name = stores.strings.resolve(ptr_type_info.name);

        let data_type_info = stores.types.get_type_info(data_type);
        let data_type_name = stores.strings.resolve(data_type_info.name);

        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(ptr_id, 1, ptr_type_name)],
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
        return;
    };

    let data_type_info = stores.types.get_type_info(data_type);
    let pointee_type_info = stores.types.get_type_info(pointee_type);
    let can_promote_int = matches!(
        [data_type_info.kind, pointee_type_info.kind],
        [TypeKind::Integer(from), TypeKind::Integer (to)]
        if can_promote_int_unidirectional(from, to)
    );

    if data_type != pointee_type && !can_promote_int {
        *had_error = true;
        let data_type_info = stores.types.get_type_info(data_type);
        let data_type_name = stores.strings.resolve(data_type_info.name);

        let kind_type_info = stores.types.get_type_info(pointee_type);
        let kind_type_name = stores.strings.resolve(kind_type_info.name);

        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(data_id, 0, data_type_name)],
            Color::Yellow,
            Color::Cyan,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));
        if let Some(
            [ConstVal::Ptr {
                id: PtrId::Mem(mem_id),
                ..
            }],
        ) = analyzer.value_consts([ptr_id])
        {
            let memory_type = program.get_memory_type_unresolved(mem_id);
            labels.push(
                Label::new(memory_type.location)
                    .with_color(Color::Cyan)
                    .with_message("memory type defined here"),
            );
        }

        diagnostics::emit_error(
            stores,
            op.token.location,
            format!("value must be a `{kind_type_name}`"),
            labels,
            None,
        );
    }
}
