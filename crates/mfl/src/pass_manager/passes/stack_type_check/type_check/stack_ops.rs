use ariadne::{Color, Label};
use intcast::IntCast;
use prettytable::{row, Table};
use smallvec::SmallVec;

use crate::{
    diagnostics::{self, TABLE_FORMAT},
    error_signal::ErrorSignal,
    pass_manager::static_analysis::{generate_type_mismatch_diag, Analyzer, ValueId},
    stores::{
        ops::OpId,
        types::{BuiltinTypes, Integer, TypeId, TypeKind},
    },
    Stores,
};

pub(crate) fn dup_over(stores: &mut Stores, analyzer: &mut Analyzer, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    let inputs: SmallVec<[ValueId; 20]> = op_data.inputs.as_slice().into();
    let outputs: SmallVec<[ValueId; 20]> = op_data.outputs.as_slice().into();

    for (input, output) in inputs.into_iter().zip(outputs) {
        let Some([input_type]) = analyzer.value_types([input]) else {
            continue;
        };
        analyzer.set_value_type(output, input_type);
    }
}

pub(crate) fn emit_stack(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    stack: &[ValueId],
    op_id: OpId,
    show_labels: bool,
) {
    let mut note = Table::new();
    note.set_format(*TABLE_FORMAT);
    note.set_titles(row!["ID", "Type"]);

    let mut value_points = Vec::new();

    for (idx, value_id) in stack.iter().enumerate().rev() {
        let value_type = analyzer.value_types([*value_id]).map_or("Unknown", |[v]| {
            let type_info = stores.types.get_type_info(v);
            stores.strings.resolve(type_info.name)
        });

        let value_idx = stack.len() - idx - 1;

        if show_labels {
            value_points.push((*value_id, value_idx.to_u64(), value_type));
        }

        note.add_row(row![value_idx.to_string(), value_type]);
    }

    let mut labels =
        diagnostics::build_creator_label_chain(analyzer, value_points, Color::Green, Color::Cyan);
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

pub(crate) fn push_bool(stores: &mut Stores, analyzer: &mut Analyzer, op_id: OpId) {
    let op_data = stores.ops.get_op_io(op_id);
    analyzer.set_value_type(
        op_data.outputs[0],
        stores.types.get_builtin(BuiltinTypes::Bool).id,
    );
}

pub(crate) fn push_int(stores: &mut Stores, analyzer: &mut Analyzer, op_id: OpId, int: Integer) {
    let op_data = stores.ops.get_op_io(op_id);
    analyzer.set_value_type(op_data.outputs[0], stores.types.get_builtin(int.into()).id);
}

pub(crate) fn push_str(stores: &mut Stores, analyzer: &mut Analyzer, op_id: OpId, is_c_str: bool) {
    let op_data = stores.ops.get_op_io(op_id);

    let kind = if is_c_str {
        stores.types.get_builtin_ptr(BuiltinTypes::U8).id
    } else {
        stores.types.get_builtin(BuiltinTypes::String).id
    };

    analyzer.set_value_type(op_data.outputs[0], kind);
}

pub(crate) fn cast(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    target_id: TypeId,
) {
    let output_type_info = stores.types.get_type_info(target_id);
    match output_type_info.kind {
        TypeKind::Integer(int) => cast_to_int(stores, analyzer, had_error, op_id, target_id, int),
        TypeKind::Pointer(_) => cast_to_ptr(stores, analyzer, had_error, op_id, target_id),
        TypeKind::Array { .. }
        | TypeKind::Bool
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_) => {
            let output_type_name = stores.strings.resolve(output_type_info.name);
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

fn cast_to_ptr(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    to_id: TypeId,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_token = stores.ops.get_token(op_id);
    let input_value_id = op_data.inputs[0];
    let Some([input_type_id]) = analyzer.value_types([input_value_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input_type_id);

    match input_type_info.kind {
        TypeKind::Pointer(_) if input_type_id == to_id => {
            let ptr_type_name = stores.strings.resolve(input_type_info.name);

            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
                [(input_value_id, 0, ptr_type_name)],
                Color::Green,
                Color::Cyan,
            );
            labels.push(Label::new(op_token.location).with_color(Color::Yellow));

            diagnostics::emit_warning(stores, op_token.location, "unnecessary cast", labels, None);
        }
        TypeKind::Integer(Integer::U64) | TypeKind::Pointer(_) => {}

        TypeKind::Integer(_) => {
            let input_type_name = stores.strings.resolve(input_type_info.name);
            let ptr_type_info = stores.types.get_type_info(to_id);
            let ptr_type_name = stores.strings.resolve(ptr_type_info.name);

            let mut labels = diagnostics::build_creator_label_chain(
                analyzer,
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
        | TypeKind::Struct(_)
        | TypeKind::GenericStructBase(_)
        | TypeKind::GenericStructInstance(_) => {
            let lexeme = stores.strings.resolve(op_token.inner);
            generate_type_mismatch_diag(stores, analyzer, lexeme, op_id, &[input_value_id]);
            had_error.set();
            return;
        }
    }

    analyzer.set_value_type(op_data.outputs[0], to_id);
}

fn cast_to_int(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut ErrorSignal,
    op_id: OpId,
    to_id: TypeId,
    to_int: Integer,
) {
    let op_data = stores.ops.get_op_io(op_id);
    let op_token = stores.ops.get_token(op_id);
    let input_value_id = op_data.inputs[0];
    let Some([input_type_id]) = analyzer.value_types([input_value_id]) else {
        return;
    };
    let input_type_info = stores.types.get_type_info(input_type_id);

    match input_type_info.kind {
        TypeKind::Bool => {}
        TypeKind::Pointer(_) => {
            if to_int != Integer::U64 {
                let input_type_name = stores.strings.resolve(input_type_info.name);
                let output_type_info = stores.types.get_type_info(to_id);
                let output_type_name = stores.strings.resolve(output_type_info.name);

                let mut labels = diagnostics::build_creator_label_chain(
                    analyzer,
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
                let input_type_name = stores.strings.resolve(input_type_info.name);

                let mut labels = diagnostics::build_creator_label_chain(
                    analyzer,
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
            generate_type_mismatch_diag(stores, analyzer, lexeme, op_id, &[input_value_id]);
            had_error.set();
            return;
        }
    }

    analyzer.set_value_type(op_data.outputs[0], to_id);
}
