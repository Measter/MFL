use crate::{
    interners::Interners,
    n_ops::VecNOps,
    opcode::{Op, OpCode},
    program::{ItemId, Program},
    source_file::SourceStorage,
};

use super::{generate_stack_length_mismatch_diag, Analyzer, ValueId};

mod arithmetic;
mod control;
mod memory;
mod stack_ops;

fn ensure_stack_depth(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
    depth: usize,
) {
    if stack.len() < depth {
        generate_stack_length_mismatch_diag(
            source_store,
            op.token.location,
            op.token.location,
            stack.len(),
            depth,
        );
        *had_error = true;

        let num_missing = usize::saturating_sub(depth, stack.len());
        for _ in 0..num_missing {
            let pad_value = analyzer.new_value(op);
            stack.push(pad_value);
        }
    }
}

pub(super) fn eat_one_make_one(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 1);

    let value_id = stack.pop().unwrap();
    analyzer.consume_value(value_id, op.id);
    let new_id = analyzer.new_value(op);

    analyzer.set_op_io(op, &[value_id], &[new_id]);
    stack.push(new_id);
}

pub(super) fn eat_two_make_one(
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    source_store: &SourceStorage,
    had_error: &mut bool,
    op: &Op,
) {
    ensure_stack_depth(analyzer, stack, source_store, had_error, op, 2);

    let inputs = stack.popn::<2>().unwrap();
    for value_id in inputs {
        analyzer.consume_value(value_id, op.id);
    }
    let new_id = analyzer.new_value(op);

    analyzer.set_op_io(op, &inputs, &[new_id]);
    stack.push(new_id);
}

pub(super) fn make_one(analyzer: &mut Analyzer, stack: &mut Vec<ValueId>, op: &Op) {
    let new_id = analyzer.new_value(op);
    stack.push(new_id);
    analyzer.set_op_io(op, &[], &[new_id]);
}

pub(super) fn analyze_block(
    program: &Program,
    item_id: ItemId,
    block: &[Op],
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
) {
    for op in block {
        match op.code {
            OpCode::Add
            | OpCode::Subtract
            | OpCode::BitAnd
            | OpCode::BitOr
            | OpCode::Multiply
            | OpCode::ShiftLeft
            | OpCode::ShiftRight
            | OpCode::Greater
            | OpCode::GreaterEqual
            | OpCode::Less
            | OpCode::LessEqual
            | OpCode::Equal
            | OpCode::NotEq => eat_two_make_one(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
            ),

            OpCode::BitNot
            | OpCode::ResolvedCast { .. }
            | OpCode::ResolvedLoad { .. } => eat_one_make_one(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
            ),
            OpCode::DivMod => arithmetic::divmod(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
            ),

            OpCode::PushBool(_)
            | OpCode::PushInt{ .. }
            | OpCode::ArgC
            | OpCode::ArgV => make_one(
                analyzer,
                stack,
                op
            ),
            OpCode::PushStr { is_c_str, .. } => stack_ops::push_str(
                analyzer,
                stack,
                op,
                is_c_str,
            ),

            OpCode::While(ref while_op) => {
                control::analyze_while(
                    program,
                    item_id,
                    analyzer,
                    stack,
                    had_error,
                    interner,
                    source_store,
                    op,
                    while_op
                )
            },
            OpCode::If(ref if_op) => control::analyze_if(
                program,
                item_id,
                analyzer,
                stack,
                had_error,
                interner,
                source_store,
                op,
                if_op
            ),

            OpCode::Drop{count, count_token} => stack_ops::drop(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                count
                , count_token,
            ),
            OpCode::Dup { count, count_token } => stack_ops::dup(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                count,
                count_token
            ),
            OpCode::Over{ depth, .. } => stack_ops::over(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                depth
            ),

            OpCode::Swap{count, count_token} => stack_ops::swap(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                count,
                count_token,
            ),
            OpCode::Rot{ item_count, direction, shift_count, item_count_token, shift_count_token } => stack_ops::rot(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                item_count,
                direction,
                shift_count,
                item_count_token,
                shift_count_token
            ),

            OpCode::ResolvedStore { .. } => memory::store(
                analyzer,
                stack,
                source_store,
                had_error,
                op
            ),
            OpCode::ResolvedIdent{item_id, ..} => control::resolved_ident(
                program,
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                item_id,
            ),
            OpCode::SysCall{ arg_count, arg_count_token } => control::syscall(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                arg_count,
                arg_count_token
            ),

            OpCode::Prologue => control::prologue(analyzer,  stack, op, program.get_item_signature_resolved(item_id)),
            OpCode::Epilogue | OpCode::Return => control::epilogue_return(
                program,
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                op,
                item_id,
            ),

            OpCode::CallFunction { .. } // These haven't been generated yet.
            | OpCode::Memory { .. } // Nor have these.
            | OpCode::UnresolvedCast { .. } // All types are resolved.
            | OpCode::UnresolvedLoad { .. }
            | OpCode::UnresolvedStore { .. }
            | OpCode::UnresolvedIdent { .. } // All idents should be resolved.
            => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }
    }
}
