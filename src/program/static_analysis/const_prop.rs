use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{ProcedureId, Program},
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
    proc_id: ProcedureId,
    block: &[Op],
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
) {
    for op in block {
        match op.code {
            OpCode::Add => arithmetic::add(analyzer, op),
            OpCode::Subtract => arithmetic::subtract(
                analyzer,
                source_store,
                had_error,
                op,
            ),

            OpCode::BitAnd | OpCode::BitOr => arithmetic::bitand_bitor(analyzer, op),
            OpCode::BitNot => arithmetic::bitnot(analyzer, op),
            OpCode::Multiply | OpCode::ShiftLeft | OpCode::ShiftRight => arithmetic::multiply_and_shift(
                analyzer,
                source_store,
                op,
            ),
            OpCode::DivMod => arithmetic::divmod(
                analyzer,
                source_store,
                op,
            ),

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => comparative::compare(
                analyzer,
                source_store,
                had_error,
                op,
            ),
            OpCode::Equal | OpCode::NotEq => comparative::equal(
                analyzer,
                source_store,
                had_error,
                op,
            ),

            OpCode::PushBool(v) => stack_ops::push_bool(analyzer, op, v),
            OpCode::PushInt {  value,.. }=> stack_ops::push_int(analyzer, op, value),
            OpCode::PushStr{ id, is_c_str } => stack_ops::push_str(analyzer, interner, op, id, is_c_str),

            // OpCode::Cast{kind: PorthTypeKind::Int(width), ..} => stack_ops::cast_int(analyzer, op, width),
            // // Nothing to do if we cast to a pointer.
            // OpCode::Cast{kind: PorthTypeKind::Ptr, ..} => {},
            // OpCode::Cast{kind: PorthTypeKind::Bool, ..} => unreachable!(),

            OpCode::Dup { .. } => stack_ops::dup(analyzer, op),
            OpCode::Over { .. } => stack_ops::over(analyzer, op),

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
                if_op,
            ),

            // These only manipulate the order of the stack, so there's nothing to do here.
            OpCode::Drop{..} |
            OpCode::Swap{..} |
            OpCode::Rot{..} => {},

            OpCode::ResolvedIdent{proc_id, ..} => control::resolved_ident(
                program,
                analyzer,
                op,
                proc_id,
            ),

            // There's nothing to do with these, as they're always non-const.
            OpCode::ArgC |
            OpCode::ArgV |
            OpCode::SysCall{..} |
            OpCode::Epilogue | OpCode::Return |
            OpCode::Prologue => {},

            OpCode::CallProc { .. } // These haven't been generated yet.
            | OpCode::Memory { .. } // Nor have these.
            | OpCode::UnresolvedCast { .. } // All types should be resolved.
            | OpCode::UnresolvedLoad { .. }
            | OpCode::UnresolvedStore { .. }
            | OpCode::UnresolvedIdent { .. } // All idents should be resolved.
            => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }
    }
}
