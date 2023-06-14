use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{IntKind, Op},
    program::static_analysis::{Analyzer, ConstVal, PtrId},
    source_file::SourceStorage,
    type_store::{TypeKind, TypeStore},
};

pub fn extract_array(
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_io = analyzer.get_op_io(op.id);
    let [array_id, idx_id] = *op_io.inputs().as_arr();

    let Some([ConstVal::Int(IntKind::Unsigned(idx))]) = analyzer.value_consts([idx_id]) else { return };

    let [array_type_id] = analyzer.value_types([array_id]).unwrap();
    let array_type_info = type_store.get_type_info(array_type_id);

    let array_length = match array_type_info.kind {
        TypeKind::Array { length, .. } => length,
        TypeKind::Pointer(id) => {
            let info = type_store.get_type_info(id);
            match info.kind {
                TypeKind::Array { length, .. } => length,
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
                _ => unreachable!(),
            }
        }
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
        _ => unreachable!(),
    };

    if idx.to_usize() >= array_length {
        *had_error = true;
        let array_type_name = interner.resolve_lexeme(array_type_info.name);

        let idx_value = format!("{idx}");
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(array_id, 1, array_type_name), (idx_id, 2, &idx_value)],
            Color::Yellow,
            Color::Cyan,
        );

        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            op.token.location,
            "index out of bounds",
            labels,
            None,
            source_store,
        );
    }
}

pub fn insert_array(
    analyzer: &mut Analyzer,
    interner: &Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_io = analyzer.get_op_io(op.id);
    let [_, array_id, idx_id] = *op_io.inputs().as_arr();

    let Some([ConstVal::Int(IntKind::Unsigned(idx))]) = analyzer.value_consts([idx_id]) else { return };

    let [array_type_id] = analyzer.value_types([array_id]).unwrap();
    let array_type_info = type_store.get_type_info(array_type_id);

    let array_length = match array_type_info.kind {
        TypeKind::Array { length, .. } => length,
        TypeKind::Pointer(id) => {
            let info = type_store.get_type_info(id);
            match info.kind {
                TypeKind::Array { length, .. } => length,
                TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
                _ => unreachable!(),
            }
        }
        TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => return,
        _ => unreachable!(),
    };

    if idx.to_usize() >= array_length {
        *had_error = true;
        let array_type_name = interner.resolve_lexeme(array_type_info.name);

        let idx_value = format!("{idx}");
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(array_id, 1, array_type_name), (idx_id, 2, &idx_value)],
            Color::Yellow,
            Color::Cyan,
        );

        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            op.token.location,
            "index out of bounds",
            labels,
            None,
            source_store,
        );
    }
}

pub fn load(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs[0];
    let Some([types]) = analyzer.value_consts([input_id]) else { return };

    let new_const_val = match types {
        // We can't do memory allocation checks yet, as we haven't evaluated sizes yet.
        // Maybe move this const evaluation pass after const item evaluation.
        ConstVal::Ptr {
            id: PtrId::Str(spur),
            src_op_loc,
            offset: Some(offset),
        } => {
            let string = interner.resolve_literal(spur);
            // Remember that string literals are always null-terminated.
            let bare_string = string.strip_suffix('\0').unwrap_or(string);

            match bare_string.as_bytes().get(offset.to_usize()) {
                Some(val) => ConstVal::Int(IntKind::Unsigned(val.to_u64())),
                None => {
                    diagnostics::emit_error(
                        op.token.location,
                        "index out of bounds",
                        [
                            Label::new(op.token.location)
                                .with_color(Color::Red)
                                .with_message(format!("index: {offset}")),
                            Label::new(src_op_loc)
                                .with_color(Color::Cyan)
                                .with_message(format!("length: {}", bare_string.len())),
                        ],
                        None,
                        source_store,
                    );
                    *had_error = true;
                    return;
                }
            }
        }
        _ => return,
    };

    analyzer.set_value_const(op_data.outputs[0], new_const_val);
}
