use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{Procedure, Program},
    source_file::SourceStorage,
};

use super::{generate_stack_length_mismatch_diag, Analyzer, ValueId};

mod arithmetic;
mod comparative;
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
            op,
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

pub(super) fn analyze_block(
    program: &Program,
    proc: &Procedure,
    block: &[Op],
    analyzer: &mut Analyzer,
    stack: &mut Vec<ValueId>,
    force_non_const_before: Option<ValueId>,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
) {
    for op in block {
        match op.code {
            OpCode::Add | OpCode::Subtract => arithmetic::eat_two_make_one(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                op,
            ),

            OpCode::BitAnd | OpCode::BitOr => arithmetic::bitand_bitor(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::BitNot => arithmetic::bitnot(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::Multiply | OpCode::ShiftLeft | OpCode::ShiftRight => {
                arithmetic::multiply_and_shift(
                    analyzer,
                    stack,
                    source_store,
                    interner,
                    had_error,
                force_non_const_before,
                    op,
                )
            }
            OpCode::DivMod => arithmetic::divmod(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => {
                comparative::compare(
                    analyzer,
                    stack,
                    source_store,
                    interner,
                    had_error,
                    force_non_const_before,
                    op,
                )
            }
            OpCode::Equal | OpCode::NotEq => comparative::equal(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),

            OpCode::PushBool(v) => stack_ops::push_bool(
                analyzer,
                stack,
                op,
                v
            ),
            OpCode::PushInt(v) => stack_ops::push_int(
                analyzer,
                stack,
                op,v
            ),
            OpCode::PushStr { is_c_str, id } => stack_ops::push_str(
                analyzer,
                stack,
                interner,
                op,
                is_c_str,
                id,
            ),

            OpCode::ArgC => stack_ops::push_argc(
                analyzer,
                stack,
                op
            ),
            OpCode::ArgV => stack_ops::push_argv(
                analyzer,
                stack,
                op
            ),

            OpCode::CastInt => stack_ops::cast_int(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op
            ),
            OpCode::CastPtr => stack_ops::cast_ptr(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op
            ),

            OpCode::While { ref body  } => {
                control::analyze_while(
                    program,
                    proc,
                    analyzer,
                    stack,
                    had_error,
                    interner,
                    source_store,
                    op,
                    body,
                )
            },
            OpCode::If {..} => unimplemented!(),

            OpCode::Drop => stack_ops::drop(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
            ),
            OpCode::Dup { depth } => stack_ops::dup(
                analyzer,
                stack,
                source_store,
                had_error,
                force_non_const_before,
                op,
                depth,
            ),
            OpCode::DupPair => stack_ops::dup_pair(
                analyzer,
                stack,
                source_store,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::Swap => stack_ops::swap(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
            ),
            OpCode::Rot => stack_ops::rot(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
            ),

            OpCode::Load { width, kind } => memory::load(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                op,
                width,
                kind,
            ),
            OpCode::Store { kind, .. } => memory::store(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                op,
                kind,
            ),

            OpCode::ResolvedIdent{proc_id, ..} => control::resolved_ident(
                program,
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                proc_id,
            ),
            OpCode::SysCall(num_args @ 0..=6) => control::syscall(
                analyzer,
                stack,
                source_store,
                had_error,
                op,
                num_args,
            ),

            OpCode::Prologue => control::prologue(analyzer,  stack,  op, proc),
            OpCode::Epilogue | OpCode::Return => control::epilogue_return(
                analyzer,
                stack,
                source_store,
                interner,
                had_error,
                op,
                proc,
            ),

            // TODO: Remove this opcode.
            OpCode::CastBool => panic!("Unsupported"),

            OpCode::SysCall(_) // No syscalls with this many args.
            | OpCode::CallProc { .. } // These haven't been generated yet.
            | OpCode::Memory { .. } // Nor have these.
            | OpCode::UnresolvedIdent { .. } // All idents should be resolved.
            => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }
    }
}
