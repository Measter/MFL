use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    diagnostics,
    interners::Interners,
    lexer::Token,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{can_promote_int_unidirectional, Analyzer},
    source_file::SourceStorage,
    type_store::{Signedness, TypeId, TypeKind, TypeStore},
};

pub fn pack_array(
    analyzer: &mut Analyzer,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    had_error: &mut bool,
    op: &Op,
    count: u8,
) {
    if count == 0 {
        diagnostics::emit_error(
            op.token.location,
            "cannot pack array of length 0",
            [Label::new(op.token.location).with_color(Color::Red)],
            None,
            source_store,
        );
        *had_error = true;
        return;
    }

    let op_data = analyzer.get_op_io(op.id);
    let [first, rest @ ..] = op_data.inputs() else { unreachable!() };
    let Some([first_value_id]) = analyzer.value_types([*first]) else { return };
    let expected_store_type = type_store.get_type_info(first_value_id);

    for (&other_id, id) in rest.iter().zip(1..) {
        let Some([value_type_id]) = analyzer.value_types([other_id]) else { continue };
        let value_type_info = type_store.get_type_info(value_type_id);
        if value_type_id != expected_store_type.id
            && !matches!(
                (expected_store_type.kind, value_type_info.kind),
                (
                    TypeKind::Integer { width: to_width, signed: to_signed },
                    TypeKind::Integer { width: from_width, signed: from_signed }
                ) if can_promote_int_unidirectional(from_width, from_signed, to_width, to_signed)
            )
        {
            let mut labels = Vec::new();
            let type_info = type_store.get_type_info(value_type_id);
            let other_value_name = interner.resolve_lexeme(type_info.name);
            let expected_value_name = interner.resolve_lexeme(expected_store_type.name);
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                other_id,
                id,
                other_value_name,
            );
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                *first,
                0,
                expected_value_name,
            );

            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                op.token.location,
                "unable to pack array: mismatched input types",
                labels,
                None,
                source_store,
            );

            *had_error = true;
        }
    }

    let array_type = type_store.get_array(interner, expected_store_type.id, count.to_usize());
    let output_id = op_data.outputs()[0];
    analyzer.set_value_type(output_id, array_type.id);
}

pub fn pack_struct(
    analyzer: &mut Analyzer,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
    type_id: TypeId,
) {
    let struct_info = type_store.get_struct_def(type_id);

    let op_data = analyzer.get_op_io(op.id);
    let inputs = op_data.inputs();

    for ((field_def, &input_id), val_id) in struct_info.fields.iter().zip(inputs).zip(1..) {
        let Some([input_type_id]) = analyzer.value_types([input_id]) else { continue };
        let expected_store_type = type_store.get_type_info(field_def.kind);
        let value_type_info = type_store.get_type_info(input_type_id);

        if input_type_id != field_def.kind
            && !matches!(
                (expected_store_type.kind, value_type_info.kind),
                (
                    TypeKind::Integer { width: to_width, signed: to_signed },
                    TypeKind::Integer { width: from_width, signed: from_signed }
                ) if can_promote_int_unidirectional(from_width, from_signed, to_width, to_signed)
            )
        {
            let mut labels = Vec::new();
            let type_info = type_store.get_type_info(input_type_id);
            let other_value_name = interner.resolve_lexeme(type_info.name);
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                input_id,
                val_id,
                other_value_name,
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

            diagnostics::emit_error(
                op.token.location,
                "unable to pack struct: mismatched input types",
                labels,
                None,
                source_store,
            );

            *had_error = true;
        }
    }

    let output_id = op_data.outputs()[0];
    analyzer.set_value_type(output_id, type_id);
}

pub fn unpack(
    analyzer: &mut Analyzer,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let outputs = op_data.outputs().to_owned();
    let aggr_id = op_data.inputs()[0];
    let Some([aggr_type_id]) = analyzer.value_types([aggr_id]) else { return };
    let aggr_info = type_store.get_type_info(aggr_type_id);

    match aggr_info.kind {
        TypeKind::Array { type_id, .. } => {
            for output_id in outputs {
                analyzer.set_value_type(output_id, type_id);
            }
        }
        TypeKind::Struct(_) => {
            let fields = type_store.get_struct_def(aggr_type_id);
            for (output_id, field_info) in outputs.iter().zip(&fields.fields) {
                analyzer.set_value_type(*output_id, field_info.kind);
            }
        }
        _ => {
            let input_type_name = interner.resolve_lexeme(aggr_info.name);

            let mut labels = Vec::new();
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                aggr_id,
                0,
                input_type_name,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                op.token.location,
                format!("expected array or struct, found {input_type_name}"),
                labels,
                None,
                source_store,
            );

            *had_error = true;
        }
    };
}

pub fn extract_array(
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
    emit_array: bool,
) {
    let op_data = analyzer.get_op_io(op.id).clone();
    let inputs @ [array_value_id, idx_value_id] = *op_data.inputs().as_arr();
    let Some(type_ids) = analyzer.value_types(inputs) else { return };
    let [array_type_info, idx_type_info] = type_ids.map(|id| type_store.get_type_info(id));

    let output_value_id = if emit_array {
        let output_array_id = op_data.outputs()[0];
        analyzer.set_value_type(output_array_id, array_type_info.id);
        op_data.outputs()[1]
    } else {
        op_data.outputs()[0]
    };

    let store_type = match array_type_info.kind {
        TypeKind::Array { type_id, .. } => type_id,
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = type_store.get_type_info(sub_type);
            if let TypeKind::Array { type_id, .. } = ptr_type_info.kind {
                type_id
            } else {
                let value_type_name = interner.resolve_lexeme(array_type_info.name);
                let mut labels = Vec::new();
                diagnostics::build_creator_label_chain(
                    &mut labels,
                    analyzer,
                    array_value_id,
                    0,
                    value_type_name,
                );
                labels.push(Label::new(op.token.location).with_color(Color::Red));

                diagnostics::emit_error(
                    op.token.location,
                    format!("cannot extract a `{value_type_name}`"),
                    labels,
                    None,
                    source_store,
                );

                *had_error = true;
                return;
            }
        }

        TypeKind::Integer { .. } | TypeKind::Bool | TypeKind::Struct(_) => {
            let value_type_name = interner.resolve_lexeme(array_type_info.name);
            let mut labels = Vec::new();
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                array_value_id,
                0,
                value_type_name,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                op.token.location,
                format!("cannot extract a `{value_type_name}`"),
                labels,
                None,
                source_store,
            );

            *had_error = true;
            return;
        }
    };

    if !matches!(
        idx_type_info.kind,
        TypeKind::Integer {
            signed: Signedness::Unsigned,
            ..
        }
    ) {
        let idx_type_name = interner.resolve_lexeme(idx_type_info.name);
        let mut labels = Vec::new();
        diagnostics::build_creator_label_chain(
            &mut labels,
            analyzer,
            idx_value_id,
            1,
            idx_type_name,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            op.token.location,
            format!("cannot index an array with `{idx_type_name}`"),
            labels,
            None,
            source_store,
        );

        *had_error = true;
        return;
    }

    analyzer.set_value_type(output_value_id, store_type);
}

pub fn insert_array(
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs @ [data_value_id, array_value_id, idx_value_id] = *op_data.inputs().as_arr();
    let Some(type_ids @ [data_type_id, array_type_id, _]) = analyzer.value_types(inputs) else { return };
    let [data_type_info, array_type_info, idx_type_info] =
        type_ids.map(|id| type_store.get_type_info(id));

    let store_type_id = match array_type_info.kind {
        TypeKind::Array { type_id, .. } => type_id,
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = type_store.get_type_info(sub_type);
            if let TypeKind::Array { type_id, .. } = ptr_type_info.kind {
                type_id
            } else {
                let value_type_name = interner.resolve_lexeme(array_type_info.name);
                let mut labels = Vec::new();
                diagnostics::build_creator_label_chain(
                    &mut labels,
                    analyzer,
                    array_value_id,
                    1,
                    value_type_name,
                );
                labels.push(Label::new(op.token.location).with_color(Color::Red));

                diagnostics::emit_error(
                    op.token.location,
                    format!("cannot insert into a `{value_type_name}`"),
                    labels,
                    None,
                    source_store,
                );

                *had_error = true;
                return;
            }
        }

        TypeKind::Integer { .. } | TypeKind::Bool | TypeKind::Struct(_) => {
            let value_type_name = interner.resolve_lexeme(array_type_info.name);
            let mut labels = Vec::new();
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                array_value_id,
                0,
                value_type_name,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                op.token.location,
                format!("cannot insert into a `{value_type_name}`"),
                labels,
                None,
                source_store,
            );

            *had_error = true;
            return;
        }
    };

    let store_type_info = type_store.get_type_info(store_type_id);

    if !matches!(
        idx_type_info.kind,
        TypeKind::Integer {
            signed: Signedness::Unsigned,
            ..
        }
    ) {
        let idx_type_name = interner.resolve_lexeme(idx_type_info.name);
        let mut labels = Vec::new();
        diagnostics::build_creator_label_chain(
            &mut labels,
            analyzer,
            idx_value_id,
            2,
            idx_type_name,
        );
        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            op.token.location,
            format!("cannot index an array with `{idx_type_name}`"),
            labels,
            None,
            source_store,
        );

        *had_error = true;
    }

    if data_type_id != store_type_id
        && !matches!(
            (store_type_info.kind, data_type_info.kind),
            (
                TypeKind::Integer { width: to_width, signed: to_signed },
                TypeKind::Integer { width: from_width, signed: from_signed }
            ) if can_promote_int_unidirectional(from_width, from_signed, to_width, to_signed)
        )
    {
        let data_type_name = interner.resolve_lexeme(data_type_info.name);
        let array_type_name = match array_type_info.kind {
            TypeKind::Array { .. } => interner.resolve_lexeme(array_type_info.name),
            TypeKind::Pointer(subtype_id) => {
                let sub_type_info = type_store.get_type_info(subtype_id);
                interner.resolve_lexeme(sub_type_info.name)
            }
            _ => unreachable!(),
        };
        let mut labels = Vec::new();
        diagnostics::build_creator_label_chain(
            &mut labels,
            analyzer,
            data_value_id,
            0,
            data_type_name,
        );
        diagnostics::build_creator_label_chain(
            &mut labels,
            analyzer,
            array_value_id,
            1,
            array_type_name,
        );

        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            op.token.location,
            format!("cannot store a value of type `{data_type_name}` in an array of type `{array_type_name}`"),
            labels,
            None,
            source_store,
        );

        *had_error = true;
    }

    let output_id = op_data.outputs()[0];
    analyzer.set_value_type(output_id, array_type_id);
}

pub fn insert_struct(
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
    field_name: Token,
) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs @ [data_value_id, input_struct_value_id] = *op_data.inputs().as_arr();
    let Some(type_ids @ [data_type_id, input_struct_type_id]) = analyzer.value_types(inputs) else { return };
    let [data_type_info, input_struct_type_info] = type_ids.map(|id| type_store.get_type_info(id));

    let output_id = op_data.outputs()[0];
    analyzer.set_value_type(output_id, input_struct_type_id);

    let actual_struct_type_id = match input_struct_type_info.kind {
        TypeKind::Struct(_) => input_struct_type_id,
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = type_store.get_type_info(sub_type);
            if let TypeKind::Struct(_) = ptr_type_info.kind {
                sub_type
            } else {
                let value_type_name = interner.resolve_lexeme(input_struct_type_info.name);
                let mut labels = Vec::new();
                diagnostics::build_creator_label_chain(
                    &mut labels,
                    analyzer,
                    input_struct_value_id,
                    1,
                    value_type_name,
                );
                labels.push(Label::new(op.token.location).with_color(Color::Red));

                diagnostics::emit_error(
                    op.token.location,
                    format!("cannot insert field into a `{value_type_name}`"),
                    labels,
                    None,
                    source_store,
                );

                *had_error = true;
                return;
            }
        }

        TypeKind::Integer { .. } | TypeKind::Bool | TypeKind::Array { .. } => {
            let value_type_name = interner.resolve_lexeme(input_struct_type_info.name);
            let mut labels = Vec::new();
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                input_struct_value_id,
                0,
                value_type_name,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                op.token.location,
                format!("cannot insert field into a `{value_type_name}`"),
                labels,
                None,
                source_store,
            );

            *had_error = true;
            return;
        }
    };

    let struct_type_info = type_store.get_struct_def(actual_struct_type_id);
    let Some(field_info) = struct_type_info
        .fields
        .iter()
        .find(|fi| fi.name.lexeme == field_name.lexeme) else {
        *had_error = true;
        let unknown_field_name = interner.resolve_lexeme(field_name.lexeme);
        let struct_name = interner.resolve_lexeme(struct_type_info.name.lexeme);
        diagnostics::emit_error(
            field_name.location,
            format!("unknown field `{unknown_field_name}` in struct `{struct_name}`"),
            [
                Label::new(field_name.location).with_color(Color::Red),
                Label::new(struct_type_info.name.location).with_color(Color::Cyan).with_message("in this struct"),
            ],
            None,
            source_store,
        );
        return;
    };

    let field_type_info = type_store.get_type_info(field_info.kind);

    if data_type_id != field_info.kind
        && !matches!(
            (field_type_info.kind, data_type_info.kind),
            (
                TypeKind::Integer { width: to_width, signed: to_signed },
                TypeKind::Integer { width: from_width, signed: from_signed }
            ) if can_promote_int_unidirectional(from_width, from_signed, to_width, to_signed)
        )
    {
        let data_type_name = interner.resolve_lexeme(data_type_info.name);
        let struct_type_name = match input_struct_type_info.kind {
            TypeKind::Struct(_) => interner.resolve_lexeme(input_struct_type_info.name),
            TypeKind::Pointer(subtype_id) => {
                let sub_type_info = type_store.get_type_info(subtype_id);
                interner.resolve_lexeme(sub_type_info.name)
            }
            _ => unreachable!(),
        };
        let mut labels = Vec::new();
        diagnostics::build_creator_label_chain(
            &mut labels,
            analyzer,
            data_value_id,
            0,
            data_type_name,
        );
        diagnostics::build_creator_label_chain(
            &mut labels,
            analyzer,
            input_struct_value_id,
            1,
            struct_type_name,
        );

        labels.push(Label::new(op.token.location).with_color(Color::Red));
        labels.push(
            Label::new(field_info.name.location)
                .with_color(Color::Cyan)
                .with_message("field defined here"),
        );

        diagnostics::emit_error(
            op.token.location,
            format!("cannot store a value of type `{data_type_name}` into `{struct_type_name}`"),
            labels,
            None,
            source_store,
        );

        *had_error = true;
    }
}

pub fn extract_struct(
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
    field_name: Token,
    emit_struct: bool,
) {
    let op_data = analyzer.get_op_io(op.id);
    let [input_struct_value_id] = *op_data.inputs().as_arr();
    let Some([ input_struct_type_id]) = analyzer.value_types([input_struct_value_id]) else { return };
    let input_struct_type_info = type_store.get_type_info(input_struct_type_id);

    let output_data_id = if emit_struct {
        let [output_struct_id, output_data_id] = *op_data.outputs().as_arr();
        analyzer.set_value_type(output_struct_id, input_struct_type_id);
        output_data_id
    } else {
        op_data.outputs()[0]
    };

    let actual_struct_type_id = match input_struct_type_info.kind {
        TypeKind::Struct(_) => input_struct_type_id,
        TypeKind::Pointer(sub_type) => {
            let ptr_type_info = type_store.get_type_info(sub_type);
            if let TypeKind::Struct(_) = ptr_type_info.kind {
                sub_type
            } else {
                let value_type_name = interner.resolve_lexeme(input_struct_type_info.name);
                let mut labels = Vec::new();
                diagnostics::build_creator_label_chain(
                    &mut labels,
                    analyzer,
                    input_struct_value_id,
                    1,
                    value_type_name,
                );
                labels.push(Label::new(op.token.location).with_color(Color::Red));

                diagnostics::emit_error(
                    op.token.location,
                    format!("cannot extract field from a `{value_type_name}`"),
                    labels,
                    None,
                    source_store,
                );

                *had_error = true;
                return;
            }
        }

        TypeKind::Integer { .. } | TypeKind::Bool | TypeKind::Array { .. } => {
            let value_type_name = interner.resolve_lexeme(input_struct_type_info.name);
            let mut labels = Vec::new();
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                input_struct_value_id,
                0,
                value_type_name,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                op.token.location,
                format!("cannot extract field from a `{value_type_name}`"),
                labels,
                None,
                source_store,
            );

            *had_error = true;
            return;
        }
    };

    let struct_def = type_store.get_struct_def(actual_struct_type_id);
    let Some(field_info) = struct_def
        .fields
        .iter()
        .find(|fi| fi.name.lexeme == field_name.lexeme) else {
        *had_error = true;
        let unknown_field_name = interner.resolve_lexeme(field_name.lexeme);
        let struct_name = interner.resolve_lexeme(struct_def.name.lexeme);
        diagnostics::emit_error(
            field_name.location,
            format!("unknown field `{unknown_field_name}` in struct `{struct_name}`"),
            [
                Label::new(field_name.location).with_color(Color::Red),
                Label::new(struct_def.name.location).with_color(Color::Cyan).with_message("in this struct"),
            ],
            None,
            source_store,
        );
        return;
    };

    analyzer.set_value_type(output_data_id, field_info.kind);
}

pub fn load(
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let ptr_id = op_data.inputs[0];
    let Some([ptr_type]) = analyzer.value_types([ptr_id]) else { return };
    let ptr_info = type_store.get_type_info(ptr_type);

    let kind = match ptr_info.kind {
        TypeKind::Pointer(kind) => kind,
        _ => {
            *had_error = true;

            let [ptr_value] = analyzer.values([ptr_id]);
            let ptr_type_info = type_store.get_type_info(ptr_type);
            let ptr_type_name = interner.resolve_lexeme(ptr_type_info.name);
            diagnostics::emit_error(
                op.token.location,
                "value must be a pointer",
                [
                    Label::new(op.token.location).with_color(Color::Red),
                    Label::new(ptr_value.creator_token.location)
                        .with_color(Color::Cyan)
                        .with_message(ptr_type_name),
                ],
                None,
                source_store,
            );
            return;
        }
    };

    analyzer.set_value_type(op_data.outputs[0], kind);
}

pub fn store(
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let [data_id, ptr_id] = *op_data.inputs.as_arr::<2>();
    let Some([data_type, ptr_type]) = analyzer.value_types([data_id, ptr_id]) else { return };
    let ptr_type_info = type_store.get_type_info(ptr_type);

    let pointee_type = match ptr_type_info.kind {
        TypeKind::Pointer(kind) => kind,
        _ => {
            *had_error = true;
            let [ptr_value] = analyzer.values([ptr_id]);
            let ptr_type_name = interner.resolve_lexeme(ptr_type_info.name);

            let data_type_info = type_store.get_type_info(data_type);
            let data_type_name = interner.resolve_lexeme(data_type_info.name);

            diagnostics::emit_error(
                op.token.location,
                format!("found {ptr_type_name} expected a ptr({data_type_name})"),
                [
                    Label::new(op.token.location).with_color(Color::Red),
                    Label::new(ptr_value.creator_token.location)
                        .with_color(Color::Cyan)
                        .with_message(ptr_type_name),
                ],
                None,
                source_store,
            );
            return;
        }
    };

    let data_type_info = type_store.get_type_info(data_type);
    let pointee_type_info = type_store.get_type_info(pointee_type);
    let can_promote_int = matches!(
    [data_type_info.kind, pointee_type_info.kind],
    [
        TypeKind::Integer {
            width: from_width,
            signed: from_signed,
        }, TypeKind::Integer {
            width: to_width,
            signed: to_signed,
        }
    ]
    if can_promote_int_unidirectional(from_width, from_signed, to_width, to_signed)
    );

    if data_type != pointee_type && !can_promote_int {
        *had_error = true;
        let [data_value] = analyzer.values([data_id]);
        let data_type_info = type_store.get_type_info(data_type);
        let data_type_name = interner.resolve_lexeme(data_type_info.name);

        let kind_type_info = type_store.get_type_info(pointee_type);
        let kind_type_name = interner.resolve_lexeme(kind_type_info.name);

        diagnostics::emit_error(
            op.token.location,
            format!("value must be a {kind_type_name}"),
            [
                Label::new(op.token.location).with_color(Color::Red),
                Label::new(data_value.creator_token.location)
                    .with_color(Color::Cyan)
                    .with_message(data_type_name),
            ],
            None,
            source_store,
        );
    }
}
