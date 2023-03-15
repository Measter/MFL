use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{IntKind, Op},
    program::static_analysis::{Analyzer, ConstVal, IntWidth, PtrId},
    source_file::{SourceLocation, SourceStorage},
    type_store::{Signedness, TypeId, TypeKind, TypeStore},
};

fn check_memory_bounds(
    source_store: &SourceStorage,
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
    src_op_loc: SourceLocation,
    kind: TypeId,
    offset: u64,
    memory_size: u64,
) -> bool {
    let kind_info = type_store.get_type_info(kind);

    // Let's make sure that the end of our access region doesn't overflow.
    let end_idx = match offset.checked_add(kind_info.width.to_u64()) {
        Some(idx) => idx,
        None => {
            diagnostics::emit_error(
                op.token.location,
                "index + width overflows",
                [Label::new(op.token.location)
                    .with_color(Color::Red)
                    .with_message(format!("index: {offset}, width: {}", kind_info.width))],
                None,
                source_store,
            );

            *had_error = true;
            return false;
        }
    };
    if offset >= memory_size || end_idx >= memory_size {
        diagnostics::emit_error(
            op.token.location,
            "index out of bounds",
            [
                Label::new(op.token.location)
                    .with_color(Color::Red)
                    .with_message(format!("index: {offset}")),
                Label::new(src_op_loc)
                    .with_color(Color::Cyan)
                    .with_message(format!("length: {memory_size}")),
            ],
            None,
            source_store,
        );

        *had_error = true;
        return false;
    }

    true
}

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
            let TypeKind::Array {  length, .. } = info.kind else { unreachable!() };
            length
        }
        _ => unreachable!(),
    };

    if idx.to_usize() >= array_length {
        *had_error = true;
        let array_type_name = interner.resolve_lexeme(array_type_info.name);

        let idx_value = format!("{idx}");
        let mut labels = Vec::new();
        diagnostics::build_creator_label_chain(&mut labels, analyzer, array_id, 1, array_type_name);
        diagnostics::build_creator_label_chain(&mut labels, analyzer, idx_id, 2, &idx_value);

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
            let TypeKind::Array {  length, .. } = info.kind else { unreachable!() };
            length
        }
        _ => unreachable!(),
    };

    if idx.to_usize() >= array_length {
        *had_error = true;
        let array_type_name = interner.resolve_lexeme(array_type_info.name);

        let idx_value = format!("{idx}");
        let mut labels = Vec::new();
        diagnostics::build_creator_label_chain(&mut labels, analyzer, array_id, 1, array_type_name);
        diagnostics::build_creator_label_chain(&mut labels, analyzer, idx_id, 2, &idx_value);

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
    type_store: &TypeStore,
    had_error: &mut bool,
    op: &Op,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs[0];
    let Some([types]) = analyzer.value_consts([input_id]) else { return };
    let [type_id] = analyzer.value_types([input_id]).unwrap();
    let TypeKind::Pointer(pointee_id) = type_store.get_type_info(type_id).kind else {unreachable!()};
    let pointee_info = type_store.get_type_info(pointee_id);

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
            let memory_size = string.len().to_u64() - 1;

            if !check_memory_bounds(
                source_store,
                type_store,
                had_error,
                op,
                src_op_loc,
                pointee_id,
                offset,
                memory_size,
            ) {
                return;
            }

            let range_start = offset.to_usize();
            let range_end = (offset + pointee_info.width.to_u64()).to_usize();
            let bytes = &string.as_bytes()[range_start..range_end];
            match pointee_info.kind {
                TypeKind::Pointer(_) => {
                    // Can't const_load a pointer.
                    return;
                }
                TypeKind::Bool => ConstVal::Bool(bytes[0] != 0),

                TypeKind::Integer {
                    width: IntWidth::I8,
                    signed: Signedness::Unsigned,
                } => ConstVal::Int(IntKind::Unsigned(bytes[0].to_u64())),

                // Don't support const loading non-bytes.
                TypeKind::Integer { .. } => return,
                TypeKind::Array { .. } => return,
            }
        }
        _ => return,
    };

    analyzer.set_value_const(op_data.outputs[0], new_const_val);
}
