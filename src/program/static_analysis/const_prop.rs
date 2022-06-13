use lasso::Interner;

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{Procedure, Program},
    source_file::SourceStorage,
};

use super::{Analyzer, ValueId};

mod arithmetic;
mod comparative;
mod control;
mod memory;
mod stack_ops;

fn check_allowed_const<const N: usize>(inputs: [ValueId; N], before: Option<ValueId>) -> bool {
    match before {
        // If the inputs are None, it means a stack exhaustion, so there can be no consts to begin with,
        // if before is None then there's no limit to const values.
        Some(before_id) => inputs.iter().all(|&v| v > before_id),
        _ => true,
    }
}

pub(super) fn analyze_block(
    program: &Program,
    proc: &Procedure,
    block: &[Op],
    analyzer: &mut Analyzer,
    force_non_const_before: Option<ValueId>,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
) {
    for op in block {
        match op.code {
            OpCode::Add => arithmetic::add(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::Subtract => arithmetic::subtract(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),

            OpCode::BitAnd | OpCode::BitOr => arithmetic::bitand_bitor(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::BitNot => arithmetic::bitnot(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::Multiply | OpCode::ShiftLeft | OpCode::ShiftRight => arithmetic::multiply_and_shift(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::DivMod => arithmetic::divmod(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => comparative::compare(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),
            OpCode::Equal | OpCode::NotEq => comparative::equal(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
            ),

            OpCode::PushBool(v) => stack_ops::push_bool(analyzer, op, v),
            OpCode::PushInt(v) => stack_ops::push_int(analyzer, op, v),
            OpCode::PushStr{ id, is_c_str } => stack_ops::push_str(analyzer, interner, op, id, is_c_str),

            OpCode::CastInt => stack_ops::cast_int(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op
            ),
            OpCode::CastPtr => stack_ops::cast_ptr(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op
            ),

            OpCode::Dup {depth} => stack_ops::dup(
                analyzer,
                source_store,
                had_error,
                force_non_const_before,
                op,
                depth
            ),
            OpCode::DupPair => stack_ops::dup_pair( 
                analyzer,
                source_store,
                had_error,
                force_non_const_before,
                op
             ),

            OpCode::While { ref body  } => control::analyze_while(
                program,
                proc,
                analyzer,
                had_error,
                interner,
                source_store,
                op,
                body,
            ),
            OpCode::If {..} => unimplemented!(),

            // These only manipulate the order of the stack, so there's nothing to do here.
            OpCode::Drop |
            OpCode::Swap |
            OpCode::Rot => {},

            OpCode::Load { width, kind } => memory::load(
                analyzer,
                source_store,
                interner,
                had_error,
                force_non_const_before,
                op,
                width,
                kind,
            ),

            // Store doesn't produce a value, so there's nothing for const-propagation to do.
            OpCode::Store { kind, .. } => {},

            OpCode::ResolvedIdent{proc_id, ..} => control::resolved_ident(
                program,
                analyzer,
                source_store,
                had_error,
                op,
                proc_id,
            ),

            // There's nothing to do with these, as they're always non-const.
            OpCode::ArgC |
            OpCode::ArgV |
            OpCode::SysCall(0..=6) |
            OpCode::Epilogue | OpCode::Return |
            OpCode::Prologue => {},

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
