use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{Analyzer, ConstVal, PorthTypeKind, PtrId},
    source_file::{SourceLocation, SourceStorage},
    Width,
};

fn check_memory_bounds(
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    src_op_loc: SourceLocation,
    width: Width,
    offset: u64,
    memory_size: u64,
) -> bool {
    // Let's make sure that the end of our access region doesn't overflow.
    let end_idx = match offset.checked_add(width.byte_size()) {
        Some(idx) => idx,
        None => {
            diagnostics::emit_error(
                op.token.location,
                "index + width overflows",
                [Label::new(op.token.location)
                    .with_color(Color::Red)
                    .with_message(format!("index: {}, width: {}", offset, width.byte_size()))],
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
                    .with_message(format!("index: {}", offset)),
                Label::new(src_op_loc)
                    .with_color(Color::Cyan)
                    .with_message(format!("length: {}", memory_size)),
            ],
            None,
            source_store,
        );

        *had_error = true;
        return false;
    }

    true
}

pub(super) fn load(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    width: Width,
    kind: PorthTypeKind,
) {
    let op_data = analyzer.get_op_io(op.id);
    let input_id = op_data.inputs[0];
    let Some([types]) = analyzer.value_consts([input_id]) else { return };

    let new_const_val = match types {
        // We can't do memory allocation checks yet, as we haven't evaluated sizes yet.
        // Maybe move this const evaluation pass after const proc evaluation.
        ConstVal::Ptr {
            id: PtrId::Str(spur),
            src_op_loc,
            offset: Some(offset),
        } => {
            let string = interner.resolve_literal(spur);
            // Remember that string literals are always null-terminated.
            let memory_size = string.len() as u64 - 1;

            if !check_memory_bounds(
                source_store,
                had_error,
                op,
                src_op_loc,
                width,
                offset,
                memory_size,
            ) {
                return;
            }

            let range_start = offset as usize;
            let range_end = (offset + width.byte_size()) as usize;
            let bytes = &string.as_bytes()[range_start..range_end];
            match width {
                Width::Byte => bytes[0] as u64,
                Width::Word => u16::from_le_bytes(*bytes.as_arr()) as u64,
                Width::Dword => u32::from_le_bytes(*bytes.as_arr()) as u64,
                Width::Qword => u64::from_le_bytes(*bytes.as_arr()) as u64,
            }
        }
        _ => return,
    };

    let new_const_val = match kind {
        PorthTypeKind::Int => ConstVal::Int(new_const_val),
        PorthTypeKind::Bool => ConstVal::Bool(new_const_val != 0),
        PorthTypeKind::Ptr => return, // Can't do a const here.
    };
    analyzer.set_value_const(op_data.outputs[0], new_const_val);
}
