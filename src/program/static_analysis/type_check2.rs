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
            OpCode::Multiply | OpCode::ShiftLeft | OpCode::ShiftRight => arithmetic::multiply_and_shift(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
            ),
            
            OpCode::DivMod => arithmetic::divmod(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
            ),

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => comparative::compare(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
            ),
            OpCode::Equal | OpCode::NotEq => comparative::equal(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
            ),
            
            OpCode::PushBool(_) => stack_ops::push_bool(
                analyzer,
                op,
            ),
            OpCode::PushInt(_) => stack_ops::push_int(
                analyzer,
                op,
            ),
            OpCode::PushStr{  is_c_str, .. } => stack_ops::push_str(
                analyzer,
                op,
                is_c_str,
            ),

            OpCode::ArgC => stack_ops::push_int(
                analyzer,
                op,
            ),
            OpCode::ArgV => stack_ops::push_str(
                analyzer,
                op,
                true,
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
            OpCode::If {ref main, ref elif_blocks, ref else_block, ..} => control::analyze_if(
                program,
                proc,
                analyzer,
                had_error,
                interner,
                source_store,
                op,
                main,
                elif_blocks,
                else_block.as_deref()
            ),


            OpCode::Dup { .. } => stack_ops::dup(analyzer, op),
            OpCode::DupPair => stack_ops::dup_pair(analyzer, op),

            OpCode::Load {  kind, .. } => memory::load(
                analyzer,
                source_store,
                interner,
                had_error,
                op,
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
            OpCode::SysCall(0..=6) => control::syscall(analyzer, op),

            OpCode::Epilogue | OpCode::Return => control::epilogue_return(
                analyzer,
                source_store,
                had_error,
                op,
                proc,
            ),

            OpCode::Prologue => control::prologue(analyzer, op, proc),
            
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
