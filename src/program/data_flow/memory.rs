use ariadne::{Color, Label};

use crate::{
    diagnostics, interners::Interners, opcode::Op, source_file::SourceStorage,
    type_check::PorthTypeKind,
};

use super::{
    generate_stack_exhaustion_diag, generate_type_mismatch_diag, Analyzer, ConstVal, PtrId, Value,
    ValueId,
};

pub(super) fn load(
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    op: &Op,
    had_error: &mut bool,
    analyzer: &mut Analyzer,
    op_idx: usize,
    interner: &Interners,
    width: crate::Width,
    kind: PorthTypeKind,
) {
    match stack.pop() {
        None => {
            generate_stack_exhaustion_diag(source_store, op, 0, 1);
            *had_error = true;
            let (new_id, _) = analyzer.new_value(PorthTypeKind::Int, op_idx, op.token);
            stack.push(new_id);
        }
        Some(val_id) => {
            match analyzer.values.get(&val_id).unwrap() {
                Value {
                    porth_type: PorthTypeKind::Ptr,
                    const_val,
                    ..
                } => {
                    // Look at handling memory at some point?
                    if let Some(ConstVal::Ptr {
                        id: PtrId::Str(spur),
                        source_op_location,
                        offset,
                    }) = *const_val
                    {
                        let string = interner.resolve_literal(spur);
                        let end_idx = offset + width.byte_size();
                        if end_idx > string.len() as u64 - 1 {
                            diagnostics::emit(
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
                }
                val => {
                    // Type mismatch
                    *had_error = true;
                    // Unknown is the result of a previous error.
                    if val.porth_type != PorthTypeKind::Unknown {
                        let lexeme = interner.resolve_lexeme(op.token.lexeme);
                        generate_type_mismatch_diag(source_store, lexeme, op, &[val]);
                    }
                }
            };

            let (new_id, _) = analyzer.new_value(kind, op_idx, op.token);
            stack.push(new_id);
        }
    }
}
