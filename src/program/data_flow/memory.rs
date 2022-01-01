use ariadne::{Color, Label};

use crate::{
    diagnostics, interners::Interners, opcode::Op, source_file::SourceStorage,
    type_check::PorthTypeKind,
};

use super::{
    generate_stack_exhaustion_diag, generate_type_mismatch_diag, Analyzer, ConstVal, PtrId, ValueId,
};

pub(super) fn load(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op_idx: usize,
    op: &Op,
    width: crate::Width,
    kind: PorthTypeKind,
) {
    let val_id = if let Some(val_id) = stack.pop() {
        val_id
    } else {
        generate_stack_exhaustion_diag(source_store, op, 0, 1);
        *had_error = true;

        let (new_id, _) = analyzer.new_value(kind, op_idx, op.token);
        stack.push(new_id);
        return;
    };

    analyzer.consume(val_id, op_idx);
    let [value] = analyzer.get_values([val_id]);

    // Type mismatch
    if value.porth_type != PorthTypeKind::Ptr {
        *had_error = true;
        // Unknown is the result of a previous error.
        if value.porth_type != PorthTypeKind::Unknown {
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(source_store, lexeme, op, &[value]);
        }

        let (new_id, _) = analyzer.new_value(kind, op_idx, op.token);
        stack.push(new_id);
        return;
    }

    // Look at handling memory at some point?
    if let Some(ConstVal::Ptr {
        id: PtrId::Str(spur),
        src_op_loc: source_op_location,
        offset: Some(offset),
    }) = value.const_val
    {
        let string = interner.resolve_literal(spur);
        let end_idx = offset + width.byte_size();

        // Remember that string literals are always null-terminated.
        if end_idx > string.len() as u64 - 1 {
            diagnostics::emit_error(
                op.token.location,
                "index out of bounds",
                [
                    Label::new(op.token.location)
                        .with_color(Color::Red)
                        .with_message(format!("index: {}", offset,)),
                    Label::new(source_op_location)
                        .with_color(Color::Cyan)
                        .with_message(format!("length: {}", string.len() - 1))
                        .with_order(1),
                ],
                None,
                source_store,
            );

            *had_error = true;
        }
    }

    let (new_id, _) = analyzer.new_value(kind, op_idx, op.token);
    analyzer.set_io(op_idx, op.token, &[val_id], &[new_id]);

    stack.push(new_id);
}
