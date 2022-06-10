use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::{NOps, PopN},
    opcode::Op,
    source_file::SourceStorage,
    type_check::PorthTypeKind,
};

use super::{
    generate_stack_length_mismatch_diag, generate_type_mismatch_diag, Analyzer, ConstVal, PtrId,
    Value, ValueId,
};

pub(super) fn load(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    width: crate::Width,
    kind: PorthTypeKind,
) {
    let val_id = if let Some(val_id) = stack.pop() {
        val_id
    } else {
        generate_stack_length_mismatch_diag(source_store, op, op.token.location, 0, 1);
        *had_error = true;

        let (new_id, _) = analyzer.new_value(kind, op.id, op.token);
        stack.push(new_id);
        return;
    };

    analyzer.consume(val_id, op.id);
    let [value] = analyzer.get_values([val_id]);

    // Type mismatch
    if value.porth_type != PorthTypeKind::Ptr {
        *had_error = true;
        // Unknown is the result of a previous error.
        if value.porth_type != PorthTypeKind::Unknown {
            let lexeme = interner.resolve_lexeme(op.token.lexeme);
            generate_type_mismatch_diag(source_store, lexeme, op, &[value]);
        }

        let (new_id, _) = analyzer.new_value(kind, op.id, op.token);
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
        let str_len = string.len() as u64 - 1;
        if end_idx > str_len || offset > str_len {
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

    let (new_id, _) = analyzer.new_value(kind, op.id, op.token);
    analyzer.set_io(op.id, op.token, &[val_id], &[new_id]);

    stack.push(new_id);
}

pub(super) fn store(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    interner: &Interners,
    had_error: &mut bool,
    op: &Op,
    kind: PorthTypeKind,
) {
    for &value_id in stack.lastn(2).unwrap_or(&*stack) {
        analyzer.consume(value_id, op.id);
    }
    let (inputs, const_val) = match stack.popn::<2>() {
        None => {
            generate_stack_length_mismatch_diag(
                source_store,
                op,
                op.token.location,
                stack.len(),
                2,
            );
            *had_error = true;
            stack.clear();

            (None, None)
        }
        Some(vals) => {
            let const_val = match analyzer.get_values(vals) {
                [Value {
                    porth_type: store_kind,
                    ..
                }, Value {
                    porth_type: PorthTypeKind::Ptr,
                    const_val,
                    ..
                }] if *store_kind == kind => *const_val,
                vals => {
                    // Type mismatch
                    *had_error = true;
                    // Don't emit an diagnostic here if any are Unknown, as it's a result of
                    // an earlier error.
                    if vals.iter().all(|v| v.porth_type != PorthTypeKind::Unknown) {
                        let lexeme = interner.resolve_lexeme(op.token.lexeme);
                        generate_type_mismatch_diag(source_store, lexeme, op, &vals);
                    }

                    None
                }
            };

            (Some(vals), const_val)
        }
    };

    if let Some(ConstVal::Ptr {
        id: PtrId::Str(_),
        src_op_loc,
        ..
    }) = const_val
    {
        diagnostics::emit_error(
            op.token.location,
            "storing to static string",
            [
                Label::new(op.token.location)
                    .with_color(Color::Red)
                    .with_message("here"),
                Label::new(src_op_loc)
                    .with_color(Color::Cyan)
                    .with_message("this string")
                    .with_order(1),
            ],
            None,
            source_store,
        );

        *had_error = true;
    }

    let inputs = inputs.as_ref().map(|i| i.as_slice()).unwrap_or(&[]);
    analyzer.set_io(op.id, op.token, inputs, &[]);
}
