use ariadne::{Color, Label};
use intcast::IntCast;
use prettytable::{row, Table};
use smallvec::SmallVec;

use crate::{
    diagnostics::{self, TABLE_FORMAT},
    ir::{Op, TypeResolvedOp},
    pass_manager::static_analysis::{Analyzer, ValueId},
    type_store::{BuiltinTypes, Integer},
    Stores,
};

pub(crate) fn dup_over(analyzer: &mut Analyzer, op: &Op<TypeResolvedOp>) {
    let op_data = analyzer.get_op_io(op.id);
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
    op: &Op<TypeResolvedOp>,
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
    labels.push(Label::new(op.token.location).with_color(Color::Cyan));

    diagnostics::emit(
        stores,
        ariadne::ReportKind::Advice,
        op.token.location,
        "printing stack trace",
        labels,
        note.to_string(),
    );
}

pub(crate) fn push_bool(stores: &mut Stores, analyzer: &mut Analyzer, op: &Op<TypeResolvedOp>) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_type(
        op_data.outputs[0],
        stores.types.get_builtin(BuiltinTypes::Bool).id,
    );
}

pub(crate) fn push_int(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    op: &Op<TypeResolvedOp>,
    int: Integer,
) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_type(op_data.outputs[0], stores.types.get_builtin(int.into()).id);
}

pub(crate) fn push_str(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    op: &Op<TypeResolvedOp>,
    is_c_str: bool,
) {
    let op_data = analyzer.get_op_io(op.id);

    let kind = if is_c_str {
        stores.types.get_builtin_ptr(BuiltinTypes::U8).id
    } else {
        stores.types.get_builtin(BuiltinTypes::String).id
    };

    analyzer.set_value_type(op_data.outputs[0], kind);
}
