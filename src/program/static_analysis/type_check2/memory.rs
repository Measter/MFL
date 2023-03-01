use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::{
        static_analysis::Analyzer,
        type_store::{TypeKind, TypeStore},
    },
    source_file::SourceStorage,
};

pub(super) fn load(
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

pub(super) fn store(
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

    if data_type != pointee_type {
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
