use ariadne::{Color, Label};
use intcast::IntCast;
use prettytable::{row, Table};
use smallvec::SmallVec;

use crate::{
    diagnostics::{self, TABLE_FORMAT},
    error_signal::ErrorSignal,
    pass_manager::static_analysis::generate_type_mismatch_diag,
    stores::{
        ops::OpId,
        types::{BuiltinTypes, FloatWidth, IntKind, TypeId, TypeKind},
        values::ValueId,
    },
    Stores,
};

pub(crate) fn dup_over(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let inputs: SmallVec<[ValueId; 20]> = op_data.inputs.as_slice().into();
    let outputs: SmallVec<[ValueId; 20]> = op_data.outputs.as_slice().into();

    for (input, output) in inputs.into_iter().zip(outputs) {
        let Some([input_type]) = stores.values.value_types([input]) else {
            continue;
        };
        stores.values.set_value_type(output, input_type);
    }
}

pub(crate) fn emit_stack(stores: &mut Stores, stack: &[ValueId], op_id: OpId, show_labels: bool) {
    let mut note = Table::new();
    note.set_format(*TABLE_FORMAT);
    note.set_titles(row!["ID", "Type"]);

    let mut value_points = Vec::new();

    for (idx, value_id) in stack.iter().enumerate().rev() {
        let value_type = stores
            .values
            .value_types([*value_id])
            .map_or("Unknown", |[v]| {
                let type_info = stores.types.get_type_info(v);
                stores.strings.resolve(type_info.friendly_name)
            });

        let value_idx = stack.len() - idx - 1;

        if show_labels {
            value_points.push((*value_id, value_idx.to_u64(), value_type));
        }

        note.add_row(row![value_idx.to_string(), value_type]);
    }

    let mut labels =
        diagnostics::build_creator_label_chain(stores, value_points, Color::Green, Color::Cyan);
    let op_loc = stores.ops.get_token(op_id).location;
    labels.push(Label::new(op_loc).with_color(Color::Cyan));

    diagnostics::emit(
        stores,
        ariadne::ReportKind::Advice,
        op_loc,
        "printing stack trace",
        labels,
        note.to_string(),
    );
}

pub(crate) fn push_bool(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    stores.values.set_value_type(
        op_data.outputs[0],
        stores.types.get_builtin(BuiltinTypes::Bool).id,
    );
}

pub(crate) fn push_int(stores: &mut Stores, op_id: OpId, int: IntKind) {
    let op_data = stores.ops.get_op_io(op_id);
    stores
        .values
        .set_value_type(op_data.outputs[0], stores.types.get_builtin(int.into()).id);
}

pub(crate) fn push_float(stores: &mut Stores, op_id: OpId, width: FloatWidth) {
    let op_data = stores.ops.get_op_io(op_id);
    stores.values.set_value_type(
        op_data.outputs[0],
        stores.types.get_builtin(width.into()).id,
    );
}

pub(crate) fn push_str(stores: &mut Stores, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let kind = stores.types.get_builtin(BuiltinTypes::String).id;
    stores.values.set_value_type(op_data.outputs[0], kind);
}

pub(crate) fn cast(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    target_id: TypeId,
) {
    let output_type_info = stores.types.get_type_info(target_id);
    match output_type_info.kind {
        TypeKind::Integer(int) => cast_to_int(stores, had_error, op_id, target_id, int),
        TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) => {
            cast_to_ptr(stores, had_error, op_id, target_id)
        }
        TypeKind::Float(_) => cast_to_float(stores, had_error, op_id, target_id),
        TypeKind::Array { .. }
        | TypeKind::Bool
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_) => {
            let output_type_name = stores.strings.resolve(output_type_info.friendly_name);
            let op_loc = stores.ops.get_token(op_id).location;
            diagnostics::emit_error(
                stores,
                op_loc,
                format!("cannot cast to `{output_type_name}`"),
                [Label::new(op_loc).with_color(Color::Red)],
                None,
            );
            had_error.set();
        }
    }
}

fn cast_to_ptr(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId, to_id: TypeId) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_token = stores.ops.get_token(op_id);
    let input_value_id = op_data.inputs[0];
    let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input_type_id);

    match input_type_info.kind {
        TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) if input_type_id == to_id => {
            let ptr_type_name = stores.strings.resolve(input_type_info.friendly_name);

            let mut labels = diagnostics::build_creator_label_chain(
                stores,
                [(input_value_id, 0, ptr_type_name)],
                Color::Green,
                Color::Cyan,
            );
            labels.push(Label::new(op_token.location).with_color(Color::Yellow));

            diagnostics::emit_warning(stores, op_token.location, "unnecessary cast", labels, None);
        }
        TypeKind::Integer(IntKind::U64)
        | TypeKind::MultiPointer(_)
        | TypeKind::SinglePointer(_) => {}

        TypeKind::Integer(_) => {
            let input_type_name = stores.strings.resolve(input_type_info.friendly_name);
            let ptr_type_info = stores.types.get_type_info(to_id);
            let ptr_type_name = stores.strings.resolve(ptr_type_info.friendly_name);

            let mut labels = diagnostics::build_creator_label_chain(
                stores,
                [(input_value_id, 0, input_type_name)],
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(op_token.location).with_color(Color::Red));

            diagnostics::emit_error(
                stores,
                op_token.location,
                format!("cannot cast `{input_type_name}` to `{ptr_type_name}`"),
                labels,
                "Can only cast U64 to pointers".to_owned(),
            );
            had_error.set();
        }

        TypeKind::Array { .. }
        | TypeKind::Bool
        | TypeKind::Float(_)
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_) => {
            let lexeme = stores.strings.resolve(op_token.inner);
            generate_type_mismatch_diag(stores, lexeme, op_id, &[input_value_id]);
            had_error.set();
            return;
        }
    }

    stores.values.set_value_type(op_data.outputs[0], to_id);
}

fn cast_to_int(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    to_id: TypeId,
    to_int: IntKind,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_token = stores.ops.get_token(op_id);
    let input_value_id = op_data.inputs[0];
    let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input_type_id);

    match input_type_info.kind {
        TypeKind::Bool | TypeKind::Float(_) => {}
        TypeKind::MultiPointer(_) | TypeKind::SinglePointer(_) => {
            if to_int != IntKind::U64 {
                let input_type_name = stores.strings.resolve(input_type_info.friendly_name);
                let output_type_info = stores.types.get_type_info(to_id);
                let output_type_name = stores.strings.resolve(output_type_info.friendly_name);

                let mut labels = diagnostics::build_creator_label_chain(
                    stores,
                    [(input_value_id, 0, input_type_name)],
                    Color::Yellow,
                    Color::Cyan,
                );
                labels.push(Label::new(op_token.location).with_color(Color::Red));

                diagnostics::emit_error(
                    stores,
                    op_token.location,
                    format!("cannot cast `{input_type_name}` to `{output_type_name}`"),
                    labels,
                    None,
                );

                had_error.set();
            }
        }
        TypeKind::Integer(_) => {
            if input_type_id == to_id {
                let input_type_name = stores.strings.resolve(input_type_info.friendly_name);

                let mut labels = diagnostics::build_creator_label_chain(
                    stores,
                    [(input_value_id, 0, input_type_name)],
                    Color::Green,
                    Color::Cyan,
                );
                labels.push(Label::new(op_token.location).with_color(Color::Yellow));

                diagnostics::emit_warning(
                    stores,
                    op_token.location,
                    "unnecessary cast",
                    labels,
                    None,
                );
            }
        }

        TypeKind::Array { .. }
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_) => {
            let lexeme = stores.strings.resolve(op_token.inner);
            generate_type_mismatch_diag(stores, lexeme, op_id, &[input_value_id]);
            had_error.set();
            return;
        }
    }

    stores.values.set_value_type(op_data.outputs[0], to_id);
}

fn cast_to_float(stores: &mut Stores, had_error: &mut ErrorSignal, op_id: OpId, to_id: TypeId) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_token = stores.ops.get_token(op_id);
    let input_value_id = op_data.inputs[0];
    let Some([input_type_id]) = stores.values.value_types([input_value_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input_type_id);

    match input_type_info.kind {
        TypeKind::Integer(_) => {}
        TypeKind::Float(_) => {
            if input_type_id == to_id {
                let input_type_name = stores.strings.resolve(input_type_info.friendly_name);

                let mut labels = diagnostics::build_creator_label_chain(
                    stores,
                    [(input_value_id, 0, input_type_name)],
                    Color::Green,
                    Color::Cyan,
                );
                labels.push(Label::new(op_token.location).with_color(Color::Yellow));

                diagnostics::emit_warning(
                    stores,
                    op_token.location,
                    "unnecessary cast",
                    labels,
                    None,
                );
            }
        }

        TypeKind::Array { .. }
        | TypeKind::MultiPointer(_)
        | TypeKind::SinglePointer(_)
        | TypeKind::Bool
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_) => {
            let lexeme = stores.strings.resolve(op_token.inner);
            generate_type_mismatch_diag(stores, lexeme, op_id, &[input_value_id]);
            had_error.set();
            return;
        }
    }

    stores.values.set_value_type(op_data.outputs[0], to_id);
}
