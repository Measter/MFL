use ariadne::{Label, Color};

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{Program, ItemId},
    source_file::SourceStorage, diagnostics,
    type_store::{TypeKind, Signedness, TypeStore}
};

use self::stack_ops::{cast_to_int, cast_to_ptr};

use super::{Analyzer, IntWidth};

mod arithmetic;
mod comparative;
mod control;
mod memory;
mod stack_ops;

pub(super) fn analyze_block(
    program: &Program,
    item: ItemId,
    block: &[Op],
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    interner: &mut Interners,
    source_store: &SourceStorage,
    type_store: &mut TypeStore,
) {
    for op in block {
        match op.code {
            OpCode::Add => arithmetic::add(
                analyzer,
                source_store,
                interner,
                type_store,
                had_error,
                op,
            ),
            OpCode::Subtract => arithmetic::subtract(
                analyzer,
                source_store,
                interner,
                type_store,
                had_error,
                op,
            ),

            OpCode::BitAnd | OpCode::BitOr => arithmetic::bitand_bitor(
                analyzer,
                source_store,
                interner,
                type_store,
                had_error,
                op,
            ),
            OpCode::BitNot => arithmetic::bitnot(
                analyzer,
                source_store,
                interner,
                type_store,
                had_error,
                op,
            ),
            OpCode::Div | OpCode::Multiply | OpCode::Rem | OpCode::ShiftLeft | OpCode::ShiftRight => arithmetic::multiply_div_rem_shift(
                analyzer,
                source_store,
                interner,
                type_store,
                had_error,
                op,
            ),
            
            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => comparative::compare(
                analyzer,
                source_store,
                interner,
                type_store,
                had_error,
                op,
            ),
            OpCode::Equal | OpCode::NotEq => comparative::equal(
                analyzer,
                source_store,
                interner,
                type_store,
                had_error,
                op,
            ),
            
            OpCode::PushBool(_) => stack_ops::push_bool(
                analyzer,
                type_store,
                op,
            ),
            OpCode::PushInt{ width, value } => stack_ops::push_int(
                analyzer,
                type_store,
                op,
                width,
                value.to_signedness(),
            ),
            OpCode::PushStr{  is_c_str, .. } => stack_ops::push_str(
                analyzer,
                type_store,
                op,
                is_c_str,
            ),

            OpCode::ArgC => stack_ops::push_int(
                analyzer,
                type_store,
                op,
                IntWidth::I64,
                Signedness::Unsigned,
            ),
            OpCode::ArgV => stack_ops::push_str(
                analyzer,
                type_store,
                op,
                true,
            ),

            OpCode::ResolvedCast { id } => {
                let info = type_store.get_type_info(id);
                match info.kind {
                    TypeKind::Integer{ width, signed  } => cast_to_int(
                        analyzer, 
                        source_store, 
                        interner, 
                        type_store, 
                        had_error, 
                        op, 
                        width, 
                        signed
                    ),
                    TypeKind::Pointer(kind) => cast_to_ptr(
                        analyzer, 
                        source_store, 
                        interner, 
                        type_store, 
                        had_error, 
                        op, 
                        kind
                    ),
                    TypeKind::Bool => {
                        diagnostics::emit_error(
                            op.token.location,
                            "cannot cast to bool",
                            [Label::new(op.token.location).with_color(Color::Red)],
                            None,
                            source_store,
                        );
                    }
                }
            }
            OpCode::Load => memory::load(
                analyzer,
                interner,
                source_store, 
                type_store,
                had_error, 
                op,
            ),
            OpCode::Store => memory::store(
                analyzer,
                interner,
                source_store,
                type_store,
                had_error,
                op,
            ),

            OpCode::While(ref while_op) => control::analyze_while(
                program,
                item,
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
                item,
                analyzer,
                had_error,
                interner,
                source_store,
                type_store,
                op,
                if_op,
            ),


            OpCode::Dup { .. } => stack_ops::dup(analyzer, op),
            OpCode::Over{ .. } => stack_ops::over(analyzer, op),

            OpCode::ResolvedIdent{item_id, ..} => control::resolved_ident(
                program,
                analyzer,
                interner,
                source_store,
                type_store,
                had_error,
                op,
                item_id,
            ),
            OpCode::SysCall{..} => control::syscall(analyzer, type_store, op),

            OpCode::Epilogue | OpCode::Return => control::epilogue_return(
                program,
                analyzer,
                interner,
                source_store,
                type_store,
                had_error,
                op,
                item,
            ),

            OpCode::Prologue => control::prologue(analyzer, op, program.get_item_signature_resolved(item)),
            
            // These only manipulate the stack order, so there's nothing to do here.
            OpCode::Drop{..} |
            OpCode::Swap{..} |
            OpCode::Rot{..} => {},

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
