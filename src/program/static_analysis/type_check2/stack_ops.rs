use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::{
        static_analysis::{generate_type_mismatch_diag, Analyzer},
        type_store::{BuiltinTypes, IntWidth, Signedness, TypeKind, TypeStore},
    },
    source_file::SourceStorage,
};

pub(super) fn cast_int(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
    width: IntWidth,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<1>();
    let Some([input_type_id]) = analyzer.value_types(input_ids) else { return };
    let input_type_info = type_store.get_type_info(input_type_id);

    match input_type_info.kind {
        TypeKind::Bool => {}
        TypeKind::Pointer => {
            if width != IntWidth::I64 {
                *had_error = true;
                let [input_value] = analyzer.values(input_ids);

                diagnostics::emit_error(
                    op.token.location,
                    format!("cannot cast to {}", width.name()),
                    [
                        Label::new(op.token.location).with_color(Color::Red),
                        Label::new(input_value.creator_token.location)
                            .with_message(format!("{} cannot hold a ptr", width.name()))
                            .with_color(Color::Cyan),
                    ],
                    None,
                    source_store,
                );
            }
        }
        TypeKind::Integer(from_width) => {
            if from_width == width {
                let [input_value] = analyzer.values(input_ids);

                diagnostics::emit_warning(
                    op.token.location,
                    "unnecessary cast",
                    [
                        Label::new(op.token.location).with_color(Color::Yellow),
                        Label::new(input_value.creator_token.location)
                            .with_message(format!("already an {}", width.name()))
                            .with_color(Color::Cyan),
                    ],
                    None,
                    source_store,
                );
            }
        }

        // No actual failure case at this time, but leaving this here later for if I get
        // round to adding other types where this is invalid.
        #[allow(unreachable_patterns)]
        _ => {
            *had_error = true;
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(
                analyzer,
                interner,
                source_store,
                type_store,
                lexeme,
                op,
                &input_ids,
            );
            return;
        }
    };

    let output_kind = (Signedness::Unsigned, width).into();
    let output_type_id = type_store.get_builtin(output_kind).id;

    analyzer.set_value_type(op_data.outputs[0], output_type_id);
}

pub(super) fn cast_ptr(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<1>();
    let Some([input]) = analyzer.value_types(input_ids) else { return };
    let input_type_info = type_store.get_type_info(input);

    match input_type_info.kind {
        TypeKind::Integer(IntWidth::I64) => {}
        TypeKind::Pointer => {
            let [value] = analyzer.values(input_ids);

            diagnostics::emit_warning(
                op.token.location,
                "unnecessary cast",
                [
                    Label::new(op.token.location).with_color(Color::Yellow),
                    Label::new(value.creator_token.location)
                        .with_message("already a Pointer")
                        .with_color(Color::Cyan),
                ],
                None,
                source_store,
            );
        }

        TypeKind::Integer(width) => {
            *had_error = true;
            let [input_value] = analyzer.values(input_ids);

            diagnostics::emit_error(
                op.token.location,
                "cannot cast to ptr",
                [
                    Label::new(op.token.location).with_color(Color::Red),
                    Label::new(input_value.creator_token.location)
                        .with_message(format!("cannot cast {} to ptr", width.name()))
                        .with_color(Color::Cyan),
                ],
                None,
                source_store,
            );
        }

        _ => {
            // Type mismatch.
            *had_error = true;
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(
                analyzer,
                interner,
                source_store,
                type_store,
                lexeme,
                op,
                &input_ids,
            );
            return;
        }
    };

    analyzer.set_value_type(
        op_data.outputs[0],
        type_store.get_builtin(BuiltinTypes::Pointer).id,
    );
}

pub(super) fn dup(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs = op_data.inputs().to_owned();
    let outputs = op_data.outputs().to_owned();

    for (input, output) in inputs.into_iter().zip(outputs) {
        let Some([input_type]) = analyzer.value_types([input]) else { continue };
        analyzer.set_value_type(output, input_type);
    }
}

pub(super) fn over(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input = op_data.inputs()[0];
    let output = op_data.outputs()[0];

    let Some([input_type])  = analyzer.value_types([input]) else { return };
    analyzer.set_value_type(output, input_type);
}

pub(super) fn push_bool(analyzer: &mut Analyzer, type_store: &TypeStore, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_type(
        op_data.outputs[0],
        type_store.get_builtin(BuiltinTypes::Bool).id,
    );
}

pub(super) fn push_int(analyzer: &mut Analyzer, type_store: &TypeStore, op: &Op, kind: IntWidth) {
    let op_data = analyzer.get_op_io(op.id);
    let builtin = (Signedness::Unsigned, kind).into();
    analyzer.set_value_type(op_data.outputs[0], type_store.get_builtin(builtin).id);
}

pub(super) fn push_str(analyzer: &mut Analyzer, type_store: &TypeStore, op: &Op, is_c_str: bool) {
    let op_data = analyzer.get_op_io(op.id);

    if is_c_str {
        analyzer.set_value_type(
            op_data.outputs[0],
            type_store.get_builtin(BuiltinTypes::Pointer).id,
        );
    } else {
        let [len, ptr] = *op_data.outputs.as_arr::<2>();
        let builtin = (Signedness::Unsigned, IntWidth::I64).into();
        analyzer.set_value_type(len, type_store.get_builtin(builtin).id);
        analyzer.set_value_type(ptr, type_store.get_builtin(BuiltinTypes::Pointer).id);
    }
}
