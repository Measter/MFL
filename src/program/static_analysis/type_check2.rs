use lasso::Interner;

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{Procedure, Program},
    source_file::SourceStorage,
};

use super::Analyzer;

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


            OpCode::Dup { depth, } => stack_ops::dup(
                analyzer,
                source_store,
                had_error,
                op,
                depth
            ),
            OpCode::DupPair => stack_ops::dup_pair(
                analyzer, 
                source_store, 
                had_error,
                op
            ),

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
            OpCode::SysCall(num_args @ 0..=6) => control::syscall(
                analyzer,
                source_store,
                had_error,
                op,
                num_args,
            ),

            OpCode::Epilogue | OpCode::Return => control::epilogue_return(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
                proc,
            ),

            // Nothing to check here, as all value types are known at creation, so it's set at that point.
            OpCode::PushBool(_) |
            OpCode::PushInt(_) |
            OpCode::PushStr{..} |
            OpCode::ArgC |
            OpCode::ArgV |
            OpCode::Prologue => {}, 
            
            // These only manipulate the stack order, so there's nothing to do here.
            OpCode::Drop |
            OpCode::Swap |
            OpCode::Rot => {},

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
