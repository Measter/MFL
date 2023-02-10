use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::SliceNOps,
    opcode::Op,
    program::static_analysis::{Analyzer, ConstVal, IntWidth, PorthTypeKind, PtrId},
    source_file::{SourceLocation, SourceStorage},
};

fn check_memory_bounds(
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    src_op_loc: SourceLocation,
    kind: PorthTypeKind,
    offset: u64,
    memory_size: u64,
) -> bool {
    // Let's make sure that the end of our access region doesn't overflow.
    let end_idx = match offset.checked_add(kind.byte_size()) {
        Some(idx) => idx,
        None => {
            diagnostics::emit_error(
                op.token.location,
                "index + width overflows",
                [Label::new(op.token.location)
                    .with_color(Color::Red)
                    .with_message(format!("index: {offset}, width: {}", kind.byte_size()))],
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

pub(super) fn load(
    analyzer: &mut Analyzer,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
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
            let memory_size = string.len().to_u64() - 1;

            if !check_memory_bounds(
                source_store,
                had_error,
                op,
                src_op_loc,
                kind,
                offset,
                memory_size,
            ) {
                return;
            }

            let range_start = offset.to_usize();
            let range_end = (offset + kind.byte_size()).to_usize();
            let bytes = &string.as_bytes()[range_start..range_end];
            match kind {
                PorthTypeKind::Int(IntWidth::I8) | PorthTypeKind::Bool => bytes[0].to_u64(),
                PorthTypeKind::Int(IntWidth::I16) => u16::from_le_bytes(*bytes.as_arr()).to_u64(),
                PorthTypeKind::Int(IntWidth::I32) => u32::from_le_bytes(*bytes.as_arr()).to_u64(),
                PorthTypeKind::Int(IntWidth::I64) => u64::from_le_bytes(*bytes.as_arr()).to_u64(),
                PorthTypeKind::Ptr => {
                    // Can't const_load a pointer.
                    return;
                }
            }
        }
        _ => return,
    };

    let new_const_val = match kind {
        PorthTypeKind::Int(_) => ConstVal::Int(new_const_val),
        PorthTypeKind::Bool => ConstVal::Bool(new_const_val != 0),
        PorthTypeKind::Ptr => return, // Can't do a const here.
    };
    analyzer.set_value_const(op_data.outputs[0], new_const_val);
}
