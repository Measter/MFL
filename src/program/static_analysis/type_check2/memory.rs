use ariadne::{Color, Label};

use crate::{
    diagnostics,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{Analyzer, PorthTypeKind},
    source_file::SourceStorage,
};

pub(super) fn load(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    kind: PorthTypeKind,
) {
    let op_data = analyzer.get_op_io(op.id);
    let ptr_id = op_data.inputs[0];
    let Some([ptr_type]) = analyzer.value_types([ptr_id]) else { return };

    if ptr_type != PorthTypeKind::Ptr {
        *had_error = true;

        let [ptr_value] = analyzer.values([ptr_id]);
        diagnostics::emit_error(
            op.token.location,
            "value must be a pointer",
            [
                Label::new(op.token.location).with_color(Color::Red),
                Label::new(ptr_value.creator_token.location)
                    .with_color(Color::Cyan)
                    .with_message(ptr_type.name_str().to_owned()),
            ],
            None,
            source_store,
        );
    }

    analyzer.set_value_type(op_data.outputs[0], kind);
}
pub(super) fn store(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    kind: PorthTypeKind,
) {
    let op_data = analyzer.get_op_io(op.id);
    let [data_id, ptr_id] = *op_data.inputs.as_arr::<2>();
    let Some([data_type, ptr_type]) = analyzer.value_types([data_id, ptr_id]) else { return };

    if ptr_type != PorthTypeKind::Ptr {
        *had_error = true;
        let [ptr_value] = analyzer.values([ptr_id]);
        diagnostics::emit_error(
            op.token.location,
            "value must be a pointer",
            [
                Label::new(op.token.location).with_color(Color::Red),
                Label::new(ptr_value.creator_token.location)
                    .with_color(Color::Cyan)
                    .with_message(ptr_type.name_str().to_owned()),
            ],
            None,
            source_store,
        );
    }

    if data_type != kind {
        *had_error = true;
        let [data_value] = analyzer.values([data_id]);
        diagnostics::emit_error(
            op.token.location,
            format!("value must be a {}", kind.name_str()),
            [
                Label::new(op.token.location).with_color(Color::Red),
                Label::new(data_value.creator_token.location)
                    .with_color(Color::Cyan)
                    .with_message(data_type.name_str().to_owned()),
            ],
            None,
            source_store,
        );
    }
}
