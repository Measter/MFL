use std::fmt::Write;

use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{generate_type_mismatch_diag, Analyzer, ValueId},
    source_file::SourceStorage,
    type_store::{BuiltinTypes, IntWidth, Signedness, TypeId, TypeKind, TypeStore},
};

pub fn emit_stack(
    stack: &[ValueId],
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &TypeStore,
    op: &Op,
    emit_labels: bool,
) {
    let mut note = "\n\t\tID    |     Type\n\
        \t\t______|__________"
        .to_owned();

    let mut labels = Vec::new();

    for (idx, value_id) in stack.iter().enumerate().rev() {
        let value_type = analyzer.value_types([*value_id]).map_or("Unknown", |[v]| {
            let type_info = type_store.get_type_info(v);
            interner.resolve_lexeme(type_info.name)
        });

        let value_idx = stack.len() - idx - 1;

        if emit_labels {
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                *value_id,
                value_idx.to_u64(),
                value_type,
                Color::Green,
                Color::Cyan,
            );
        }

        write!(&mut note, "\n\t\t{:<5} | {:>8}", value_idx, value_type,).unwrap();
    }

    labels.push(Label::new(op.token.location).with_color(Color::Cyan));

    diagnostics::emit(
        ariadne::ReportKind::Advice,
        op.token.location,
        "printing stack trace",
        labels,
        note,
        source_store,
    );
}

pub fn cast_to_int(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
    width: IntWidth,
    sign: Signedness,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<1>();
    let Some([input_type_id]) = analyzer.value_types(input_ids) else { return };
    let input_type_info = type_store.get_type_info(input_type_id);

    match input_type_info.kind {
        TypeKind::Bool => {}
        TypeKind::Pointer(_) => {
            if (width, sign) != (IntWidth::I64, Signedness::Unsigned) {
                *had_error = true;
                let input_type_name = interner.resolve_lexeme(input_type_info.name);

                let mut labels = Vec::new();
                diagnostics::build_creator_label_chain(
                    &mut labels,
                    analyzer,
                    input_ids[0],
                    0,
                    input_type_name,
                    Color::Yellow,
                    Color::Cyan,
                );
                labels.push(Label::new(op.token.location).with_color(Color::Red));

                diagnostics::emit_error(
                    op.token.location,
                    format!("cannot cast to {}", width.name(sign)),
                    labels,
                    Some(format!("{} cannot hold a ptr", width.name(sign))),
                    source_store,
                );
            }
        }
        TypeKind::Integer {
            width: from_width,
            signed: from_sign,
        } => {
            if (from_width, from_sign) == (width, sign) {
                let input_type_name = interner.resolve_lexeme(input_type_info.name);

                let mut labels = Vec::new();
                diagnostics::build_creator_label_chain(
                    &mut labels,
                    analyzer,
                    input_ids[0],
                    0,
                    input_type_name,
                    Color::Green,
                    Color::Cyan,
                );
                labels.push(Label::new(op.token.location).with_color(Color::Yellow));

                diagnostics::emit_warning(
                    op.token.location,
                    "unnecessary cast",
                    labels,
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

    let output_kind = (sign, width).into();
    let output_type_id = type_store.get_builtin(output_kind).id;

    analyzer.set_value_type(op_data.outputs[0], output_type_id);
}

pub fn cast_to_ptr(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &mut Interners,
    type_store: &mut TypeStore,
    had_error: &mut bool,
    op: &Op,
    to_kind: TypeId,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_ids = *op_data.inputs.as_arr::<1>();
    let Some([input]) = analyzer.value_types(input_ids) else { return };
    let input_type_info = type_store.get_type_info(input);

    match input_type_info.kind {
        TypeKind::Integer {
            width: IntWidth::I64,
            signed: Signedness::Unsigned,
        } => {}
        TypeKind::Pointer(from_kind) if from_kind == to_kind => {
            let ptr_info = type_store.get_pointer(interner, from_kind);
            let ptr_type_name = interner.resolve_lexeme(ptr_info.name);

            let mut labels = Vec::new();
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                input_ids[0],
                0,
                ptr_type_name,
                Color::Green,
                Color::Cyan,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Yellow));

            diagnostics::emit_warning(
                op.token.location,
                "unnecessary cast",
                labels,
                Some(format!("already a {ptr_type_name}")),
                source_store,
            );
        }
        TypeKind::Pointer(_) => {}

        TypeKind::Integer { .. } => {
            *had_error = true;
            let value_type_name = interner.resolve_lexeme(input_type_info.name);

            let mut labels = Vec::new();
            diagnostics::build_creator_label_chain(
                &mut labels,
                analyzer,
                input_ids[0],
                0,
                value_type_name,
                Color::Yellow,
                Color::Cyan,
            );
            labels.push(Label::new(op.token.location).with_color(Color::Red));

            diagnostics::emit_error(
                op.token.location,
                "cannot cast to ptr",
                labels,
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
        type_store.get_pointer(interner, to_kind).id,
    );
}

pub fn dup(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let inputs = op_data.inputs().to_owned();
    let outputs = op_data.outputs().to_owned();

    for (input, output) in inputs.into_iter().zip(outputs) {
        let Some([input_type]) = analyzer.value_types([input]) else { continue };
        analyzer.set_value_type(output, input_type);
    }
}

pub fn over(analyzer: &mut Analyzer, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    let input = op_data.inputs()[0];
    let output = op_data.outputs()[0];

    let Some([input_type])  = analyzer.value_types([input]) else { return };
    analyzer.set_value_type(output, input_type);
}

pub fn push_bool(analyzer: &mut Analyzer, type_store: &TypeStore, op: &Op) {
    let op_data = analyzer.get_op_io(op.id);
    analyzer.set_value_type(
        op_data.outputs[0],
        type_store.get_builtin(BuiltinTypes::Bool).id,
    );
}

pub fn push_int(
    analyzer: &mut Analyzer,
    type_store: &TypeStore,
    op: &Op,
    width: IntWidth,
    sign: Signedness,
) {
    let op_data = analyzer.get_op_io(op.id);
    let builtin = (sign, width).into();
    analyzer.set_value_type(op_data.outputs[0], type_store.get_builtin(builtin).id);
}

pub fn push_str(analyzer: &mut Analyzer, type_store: &TypeStore, op: &Op, is_c_str: bool) {
    let op_data = analyzer.get_op_io(op.id);

    let kind = if is_c_str {
        type_store.get_builtin_ptr(BuiltinTypes::U8).id
    } else {
        type_store.get_builtin(BuiltinTypes::String).id
    };

    analyzer.set_value_type(op_data.outputs[0], kind);
}
