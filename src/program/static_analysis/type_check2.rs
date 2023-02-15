use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{Program, ProcedureId},
    source_file::SourceStorage,
};

use super::{Analyzer, IntWidth};

mod arithmetic;
mod comparative;
mod control;
mod memory;
mod stack_ops;

pub(super) fn analyze_block(
    program: &Program,
    proc_id: ProcedureId,
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
            OpCode::PushInt{ width, .. } => stack_ops::push_int(
                analyzer,
                op,
                width,
            ),
            OpCode::PushStr{  is_c_str, .. } => stack_ops::push_str(
                analyzer,
                op,
                is_c_str,
            ),

            OpCode::ArgC => stack_ops::push_int(
                analyzer,
                op,
                IntWidth::I64,
            ),
            OpCode::ArgV => stack_ops::push_str(
                analyzer,
                op,
                true,
            ),

            // OpCode::Cast{kind: PorthTypeKind::Int(width), ..} => stack_ops::cast_int(
            //     analyzer,
            //     source_store,
            //     interner,
            //     had_error,
            //     op,
            //     width,
            // ),
            // OpCode::Cast{kind: PorthTypeKind::Ptr, ..} => stack_ops::cast_ptr(
            //     analyzer,
            //     source_store,
            //     interner,
            //     had_error,
            //     op
            // ),
            // OpCode::Cast{kind: PorthTypeKind::Bool, ..} => unreachable!(),

            OpCode::While(ref while_op) => control::analyze_while(
                program,
                proc_id,
                analyzer,
                had_error,
                interner,
                source_store,
                op,
                while_op,
            ),
            OpCode::If(ref if_op) => control::analyze_if(
                program,
                proc_id,
                analyzer,
                had_error,
                interner,
                source_store,
                op,
                if_op,
            ),


            OpCode::Dup { .. } => stack_ops::dup(analyzer, op),
            OpCode::Over{ .. } => stack_ops::over(analyzer, op),

            OpCode::Load {  kind, .. } => memory::load(
                analyzer,
                source_store,
                had_error,
                op,
                kind,
            ),
            OpCode::Store { kind, .. } => memory::store(
                analyzer,
                source_store,
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
            OpCode::SysCall{..} => control::syscall(analyzer, op, ),

            OpCode::Epilogue | OpCode::Return => control::epilogue_return(
                program,
                analyzer,
                source_store,
                had_error,
                op,
                proc_id,
            ),

            OpCode::Prologue => control::prologue(analyzer, op, program.get_proc_signature_resolved(proc_id)),
            
            // These only manipulate the stack order, so there's nothing to do here.
            OpCode::Drop{..} |
            OpCode::Swap{..} |
            OpCode::Rot{..} => {},

            OpCode::CallProc { .. } // These haven't been generated yet.
            | OpCode::Memory { .. } // Nor have these.
            | OpCode::UnresolvedCast { .. } // All casts should be resolved.
            | OpCode::UnresolvedIdent { .. } // All idents should be resolved.
            => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }
    }
}
