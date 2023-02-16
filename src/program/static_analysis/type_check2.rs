use ariadne::{Label, Color};

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    program::{Program, ProcedureId, type_store::{TypeKind}},
    source_file::SourceStorage, diagnostics,
};

use self::stack_ops::{cast_int, cast_ptr};

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
                &program.type_store,
                had_error,
                op,
            ),
            OpCode::Subtract => arithmetic::subtract(
                analyzer,
                source_store,
                interner,
                &program.type_store,
                had_error,
                op,
            ),

            OpCode::BitAnd | OpCode::BitOr => arithmetic::bitand_bitor(
                analyzer,
                source_store,
                interner,
                &program.type_store,
                had_error,
                op,
            ),
            OpCode::BitNot => arithmetic::bitnot(
                analyzer,
                source_store,
                interner,
                &program.type_store,
                had_error,
                op,
            ),
            OpCode::Multiply | OpCode::ShiftLeft | OpCode::ShiftRight => arithmetic::multiply_and_shift(
                analyzer,
                source_store,
                interner,
                &program.type_store,
                had_error,
                op,
            ),
            
            OpCode::DivMod => arithmetic::divmod(
                analyzer,
                source_store,
                interner,
                &program.type_store,
                had_error,
                op,
            ),

            OpCode::Greater | OpCode::GreaterEqual | OpCode::Less | OpCode::LessEqual => comparative::compare(
                analyzer,
                source_store,
                interner,
                &program.type_store,
                had_error,
                op,
            ),
            OpCode::Equal | OpCode::NotEq => comparative::equal(
                analyzer,
                source_store,
                interner,
                &program.type_store,
                had_error,
                op,
            ),
            
            OpCode::PushBool(_) => stack_ops::push_bool(
                analyzer,
                &program.type_store,
                op,
            ),
            OpCode::PushInt{ width, .. } => stack_ops::push_int(
                analyzer,
                &program.type_store,
                op,
                width,
            ),
            OpCode::PushStr{  is_c_str, .. } => stack_ops::push_str(
                analyzer,
                &program.type_store,
                op,
                is_c_str,
            ),

            OpCode::ArgC => stack_ops::push_int(
                analyzer,
                &program.type_store,
                op,
                IntWidth::I64,
            ),
            OpCode::ArgV => stack_ops::push_str(
                analyzer,
                &program.type_store,
                op,
                true,
            ),

            OpCode::ResolvedCast { id } => {
                let info = &program.type_store.get_type_info(id);
                match info.kind {
                    TypeKind::Integer(width) => cast_int(analyzer, source_store, interner, &program.type_store, had_error, op, width),
                    TypeKind::Pointer => cast_ptr(analyzer, source_store, interner, &program.type_store, had_error, op),
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
            OpCode::ResolvedLoad { id } => memory::load(
                analyzer,
                interner,
                source_store, 
                &program.type_store,
                had_error, 
                op,
                id
            ),
            OpCode::ResolvedStore { id } => memory::store(
                analyzer,
                interner,
                source_store,
                &program.type_store,
                had_error,
                op,
                id
            ),

            OpCode::While(ref while_op) => control::analyze_while(
                program,
                proc_id,
                analyzer,
                had_error,
                interner,
                source_store,
                &program.type_store,
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
                &program.type_store,
                op,
                if_op,
            ),


            OpCode::Dup { .. } => stack_ops::dup(analyzer, op),
            OpCode::Over{ .. } => stack_ops::over(analyzer, op),

            OpCode::ResolvedIdent{proc_id, ..} => control::resolved_ident(
                program,
                analyzer,
                interner,
                source_store,
                &program.type_store,
                had_error,
                op,
                proc_id,
            ),
            OpCode::SysCall{..} => control::syscall(analyzer, &program.type_store, op),

            OpCode::Epilogue | OpCode::Return => control::epilogue_return(
                program,
                analyzer,
                interner,
                source_store,
                &program.type_store,
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
