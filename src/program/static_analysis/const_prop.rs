use lasso::Interner;

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{Procedure, Program},
    source_file::SourceStorage,
};

use super::{Analyzer, ValueId};

macro_rules! const_pattern {
    ($( $p:pat_param ),+) => {
        [
            $( Value {const_val: Some($p), ..}),+
        ]
    }
}

mod arithmetic;
mod comparative;
mod control;
mod memory;
mod stack_ops;

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
                op,
            ),

            OpCode::BitAnd | OpCode::BitOr => arithmetic::bitand_bitor(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
            ),
            OpCode::BitNot => arithmetic::bitnot(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
            ),
            OpCode::Multiply | OpCode::ShiftLeft | OpCode::ShiftRight => {
                arithmetic::multiply_and_shift(
                    analyzer,
                    source_store,
                    interner,
                    had_error,
                    op,
                )
            }
            OpCode::DivMod => arithmetic::divmod(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
            ),

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => {
                comparative::compare(
                    analyzer,
                    source_store,
                    interner,
                    had_error,
                    op,
                )
            }
            OpCode::Equal | OpCode::NotEq => comparative::equal(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
            ),

            OpCode::CastInt => stack_ops::cast_int(
                analyzer,
                source_store,
                interner,
                had_error,
                op
            ),
            OpCode::CastPtr => stack_ops::cast_ptr(
                analyzer,
                source_store,
                interner,
                had_error,
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

            OpCode::While { ref body  } => {
                control::analyze_while(
                    program,
                    proc,
                    analyzer,
                    had_error,
                    interner,
                    source_store,
                    op,
                    body,
                )
            },
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
                op,
                width,
                kind,
            ),
            OpCode::Store { kind, .. } => memory::store(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
                kind,
            ),

            OpCode::ResolvedIdent{proc_id, ..} => control::resolved_ident(
                program,
                analyzer,
                source_store,
                had_error,
                op,
                proc_id,
            ),

            // These are simple consts, and have known values during data flow.
            // The const values are set there.
            OpCode::PushBool(_) |
            OpCode::PushInt(_) |
            OpCode::PushStr{..} => {}
            
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
