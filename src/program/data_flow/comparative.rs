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
    generate_stack_exhaustion_diag, generate_type_mismatch_diag, Analyzer, ConstVal, Value, ValueId,
};

pub(super) fn equal(
    stack: &mut Vec<ValueId>,
    analyzer: &mut Analyzer,
    op_idx: usize,
    source_store: &SourceStorage,
    op: &Op,
    had_error: &mut bool,
    interner: &Interners,
) {
    for &value_id in stack.lastn(2).unwrap_or(&*stack) {
        analyzer.consume(value_id, op_idx);
    }
    let (new_type, const_val) = match stack.popn::<2>() {
        None => {
            generate_stack_exhaustion_diag(source_store, op, stack.len(), 2);
            *had_error = true;
            stack.clear();

            (PorthTypeKind::Unknown, None)
        }
        Some(vals) => {
            let new_tv = match analyzer.get_values(vals) {
                type_pattern!(a @ PorthTypeKind::Bool, b @ PorthTypeKind::Bool)
                | type_pattern!(a @ PorthTypeKind::Ptr, b @ PorthTypeKind::Ptr)
                | type_pattern!(b @ PorthTypeKind::Int, a @ PorthTypeKind::Int) => {
                    (PorthTypeKind::Bool, (*a).zip(*b))
                }
                vals => {
                    // Type mismatch
                    *had_error = true;
                    // Don't emit an diagnostic here if any are Unknown, as it's a result of
                    // an earlier error.
                    if vals.iter().all(|v| v.porth_type != PorthTypeKind::Unknown) {
                        let lexeme = interner.resolve_lexeme(op.token.lexeme);
                        generate_type_mismatch_diag(source_store, lexeme, op, &vals);
                    }
                    (PorthTypeKind::Unknown, None)
                }
            };

            new_tv
        }
    };
    let const_val = const_val.map(|cv| {
        let res = match cv {
            (ConstVal::Int(a), ConstVal::Int(b)) => op.code.get_binary_op()(a, b) != 0,
            (ConstVal::Bool(a), ConstVal::Bool(b)) => op.code.get_binary_op()(a as _, b as _) != 0,
            (
                ConstVal::Ptr {
                    id: a_id,
                    offset: a_offset,
                    source_op_location: a_op,
                },
                ConstVal::Ptr {
                    id: b_id,
                    offset: b_offset,
                    source_op_location: b_op,
                },
            ) => {
                if a_id != b_id {
                    diagnostics::emit_warning(
                        op.token.location,
                        "pointers never equal",
                        [
                            Label::new(op.token.location)
                                .with_color(Color::Yellow)
                                .with_message("here"),
                            Label::new(a_op)
                                .with_color(Color::Cyan)
                                .with_message("...and this")
                                .with_order(2),
                            Label::new(b_op)
                                .with_color(Color::Cyan)
                                .with_message("comparing this...")
                                .with_order(1),
                        ],
                        None,
                        source_store,
                    );
                    op.code.get_binary_op()(0, 1) != 0
                } else {
                    op.code.get_binary_op()(a_offset, b_offset) != 0
                }
                //
            }
            _ => unreachable!(),
        };
        dbg!(res);

        ConstVal::Bool(res)
    });
    let (new_id, new_value) = analyzer.new_value(new_type, op_idx, op.token);
    new_value.const_val = const_val;
    stack.push(new_id);
}
