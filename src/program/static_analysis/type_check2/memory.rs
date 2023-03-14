use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{can_promote_int_unidirectional, Analyzer},
    source_file::SourceStorage,
    type_store::{Signedness, TypeKind, TypeStore},
};

pub fn pack(
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
        if value_type_id != expected_store_type.id {
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
    let array_id = op_data.inputs()[0];
    let Some([array_type_id]) = analyzer.value_types([array_id]) else { return };
    let array_info = type_store.get_type_info(array_type_id);

    let kind = match array_info.kind {
        TypeKind::Array { type_id, .. } => type_id,
        _ => {
            let input_type_name = interner.resolve_lexeme(array_info.name);

            let mut labels = Vec::new();
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                array_id,
                0,
                input_type_name,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                op.token.location,
                format!("expected array, found {input_type_name}"),
                labels,
                None,
                source_store,
            );

            *had_error = true;
            return;
        }
    };

    for output_id in outputs {
        analyzer.set_value_type(output_id, kind);
    }
}

pub fn extract_array(
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs @ [array_value_id, idx_value_id] = *op_data.inputs().as_arr();
    let Some(type_ids) = analyzer.value_types(inputs) else { return };
    let [array_type_info, idx_type_info] = type_ids.map(|id| type_store.get_type_info(id));

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

        TypeKind::Integer { .. } | TypeKind::Bool => {
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

    let output_id = op_data.outputs()[0];
    analyzer.set_value_type(output_id, store_type);
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
                    format!("cannot extract a `{value_type_name}`"),
                    labels,
                    None,
                    source_store,
                );

                *had_error = true;
                return;
            }
        }

        TypeKind::Integer { .. } | TypeKind::Bool => {
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

    if data_type_id != store_type_id {
        let data_type_name = interner.resolve_lexeme(data_type_info.name);
        let array_type_name = interner.resolve_lexeme(array_type_info.name);
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

    if matches!(array_type_info.kind, TypeKind::Array { .. }) {
        let output_id = op_data.outputs()[0];
        analyzer.set_value_type(output_id, array_type_id);
    }
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
