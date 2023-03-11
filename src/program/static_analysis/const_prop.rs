use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{ItemId, Program},
    source_file::SourceStorage,
    type_store::{TypeKind, TypeStore},
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
    type_store: &mut TypeStore,
) {
    for op in block {
        match op.code {
            OpCode::Add => arithmetic::add(analyzer, type_store, op),
            OpCode::Subtract => arithmetic::subtract(
                analyzer,
                source_store,
                type_store,
                had_error,
                op,
            ),

            OpCode::BitAnd | OpCode::BitOr => arithmetic::bitand_bitor(analyzer, type_store, op),
            OpCode::BitNot => arithmetic::bitnot(analyzer, type_store, op),
            OpCode::Div | OpCode::Multiply | OpCode::Rem | OpCode::ShiftLeft | OpCode::ShiftRight => arithmetic::multiply_div_rem_shift(
                analyzer,
                source_store,
                type_store,
                op,
            ),

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => comparative::compare(
                analyzer,
                source_store,
                type_store,
                had_error,
                op,
            ),
            OpCode::Equal | OpCode::NotEq => comparative::equal(
                analyzer,
                source_store,
                type_store,
                had_error,
                op,
            ),

            OpCode::PushBool(v) => stack_ops::push_bool(analyzer, op, v),
            OpCode::PushInt {  value, .. }=> stack_ops::push_int(analyzer, op,  value),
            OpCode::PushStr{ id, is_c_str } => stack_ops::push_str(analyzer, interner, op, id, is_c_str),

            OpCode::ResolvedCast { id } => {
                let type_info = type_store.get_type_info(id);
                match type_info.kind {
                    TypeKind::Integer{ width, signed } => stack_ops::cast_to_int(analyzer, op, width, signed),
                    TypeKind::Pointer(kind) => stack_ops::cast_to_ptr(analyzer, op, kind),
                    TypeKind::Bool | TypeKind::Array {..}=> {},
                }
            }
            OpCode::Load => memory::load(analyzer,
                source_store,
                interner,
                type_store,
                had_error,
                op,
            ),
            OpCode::Store => {} // Nothing to do for store.

            OpCode::Dup { .. } => stack_ops::dup(analyzer, op),
            OpCode::Over { .. } => stack_ops::over(analyzer, op),

            OpCode::While(ref while_op) => control::analyze_while(
                program,
                item_id,
                analyzer,
                had_error,
                interner,
                source_store,
                type_store,
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
                type_store,
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

            OpCode::Epilogue | OpCode::Return => control::epilogue_return(
                program,
                analyzer,
                source_store,
                had_error,
                op
            ),

            // There's nothing to do with these, as they're always non-const.
            OpCode::ArgC |
            OpCode::ArgV |
            OpCode::SysCall{..} |
            OpCode::Prologue => {},

            OpCode::CallFunction { .. } // These haven't been generated yet.
            | OpCode::Memory { .. } // Nor have these.
            | OpCode::UnresolvedCast { .. } // All types should be resolved.
            | OpCode::UnresolvedIdent { .. } // All idents should be resolved.
            => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }
    }
}
