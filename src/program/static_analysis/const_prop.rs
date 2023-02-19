use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{type_store::TypeKind, ItemId, Program},
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
    item_id: ItemId,
    block: &[Op],
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &Interners,
    source_store: &SourceStorage,
) {
    for op in block {
        match op.code {
            OpCode::Add => arithmetic::add(analyzer, &program.type_store, op),
            OpCode::Subtract => arithmetic::subtract(
                analyzer,
                source_store,
                &program.type_store,
                had_error,
                op,
            ),

            OpCode::BitAnd | OpCode::BitOr => arithmetic::bitand_bitor(analyzer, &program.type_store, op),
            OpCode::BitNot => arithmetic::bitnot(analyzer, &program.type_store, op),
            OpCode::Multiply | OpCode::ShiftLeft | OpCode::ShiftRight => arithmetic::multiply_and_shift(
                analyzer,
                source_store,
                &program.type_store,
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
            OpCode::ResolvedCast { id } => {
                let type_info = program.type_store.get_type_info(id);
                match type_info.kind {
                    TypeKind::Integer(width) => stack_ops::cast_int(analyzer, op, width),
                    TypeKind::Pointer => {},
                    TypeKind::Bool => {},
                }
            }
            OpCode::ResolvedLoad { id } => memory::load(analyzer,
                source_store,
                interner,
                &program.type_store,
                had_error,
                op,
                id
            ),
            OpCode::ResolvedStore { .. } => {} // Nothing to do for store.

            OpCode::Dup { .. } => stack_ops::dup(analyzer, op),
            OpCode::Over { .. } => stack_ops::over(analyzer, op),

            OpCode::While(ref while_op) => control::analyze_while(
                program,
                item_id,
                analyzer,
                had_error,
                interner,
                source_store,
                op,
                while_op,
            ),
            OpCode::If(ref if_op) => control::analyze_if(
                program,
                item_id,
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

            OpCode::ResolvedIdent{item_id, ..} => control::resolved_ident(
                program,
                analyzer,
                op,
                item_id,
            ),

            // There's nothing to do with these, as they're always non-const.
            OpCode::ArgC |
            OpCode::ArgV |
            OpCode::SysCall{..} |
            OpCode::Epilogue | OpCode::Return |
            OpCode::Prologue => {},

            OpCode::CallFunction { .. } // These haven't been generated yet.
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
