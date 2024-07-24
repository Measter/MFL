use crate::{
    context::{Context, ItemId},
    error_signal::ErrorSignal,
    ir::{Arithmetic, Basic, Compare, Control, Memory, OpCode, Stack, TypeResolvedOp},
    pass_manager::{static_analysis::Analyzer, PassContext},
    stores::ops::OpId,
    Stores,
};

mod arithmetic;
mod comparative;
mod control;
mod memory;
mod stack_ops;

fn analyze_block(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    block: &[OpId],
) {
    for &op_id in block {
        let op_code = stores.ops.get_type_resolved(op_id).clone();
        match op_code {
            OpCode::Basic(bo) => match bo {
                Basic::Arithmetic(ao) => match ao {
                    Arithmetic::Add => arithmetic::add(stores, analyzer, op_id, ao),
                    Arithmetic::BitAnd | Arithmetic::BitOr | Arithmetic::BitXor => {
                        arithmetic::bitand_bitor_bitxor(stores, analyzer, op_id, ao)
                    }
                    Arithmetic::BitNot => arithmetic::bitnot(stores, analyzer, op_id),
                    Arithmetic::Div
                    | Arithmetic::Multiply
                    | Arithmetic::Rem
                    | Arithmetic::ShiftLeft
                    | Arithmetic::ShiftRight => {
                        arithmetic::multiply_div_rem_shift(stores, analyzer, had_error, op_id, ao)
                    }
                    Arithmetic::Subtract => {
                        arithmetic::subtract(stores, analyzer, had_error, op_id, ao)
                    }
                },
                Basic::Compare(co) => match co {
                    Compare::Equal | Compare::NotEq => {
                        comparative::equal(stores, analyzer, had_error, op_id, co)
                    }
                    Compare::Less
                    | Compare::LessEqual
                    | Compare::Greater
                    | Compare::GreaterEqual => {
                        comparative::compare(stores, analyzer, had_error, op_id, co)
                    }
                    Compare::IsNull => comparative::is_null(analyzer, op_id),
                },
                Basic::Stack(so) => match so {
                    Stack::Dup { .. } | Stack::Over { .. } => stack_ops::dup_over(analyzer, op_id),

                    // These just change the order of the virtual stack, so there's no work to do here.
                    Stack::Drop { .. }
                    | Stack::Emit { .. }
                    | Stack::Reverse { .. }
                    | Stack::Rotate { .. }
                    | Stack::Swap { .. } => {}
                },
                Basic::Control(co) => match co {
                    Control::Epilogue | Control::Return => {
                        control::epilogue_return(ctx, stores, analyzer, had_error, op_id);

                        // We're terminated the current block, so don't process any remaining ops.
                        break;
                    }

                    // Nothing to do here.
                    Control::Exit | Control::Prologue | Control::SysCall { .. } => {}
                },
                Basic::Memory(mo) => match mo {
                    Memory::ExtractArray { .. } | Memory::InsertArray { .. } => {
                        memory::insert_extract_array(stores, analyzer, had_error, op_id)
                    }
                    // Nothing to do here.
                    Memory::ExtractStruct { .. }
                    | Memory::InsertStruct { .. }
                    | Memory::Load
                    | Memory::PackArray { .. }
                    | Memory::Store
                    | Memory::Unpack => {}
                },
                Basic::PushBool(value) => stack_ops::push_bool(analyzer, op_id, value),
                Basic::PushInt { value, .. } => stack_ops::push_int(analyzer, op_id, value),
                Basic::PushStr { .. } => {}
            },
            OpCode::Complex(co) => match co {
                TypeResolvedOp::Cast { id } => stack_ops::cast(stores, analyzer, op_id, id),
                TypeResolvedOp::Const { id } => {
                    control::cp_const(ctx, stores, analyzer, pass_ctx, op_id, id)
                }
                TypeResolvedOp::If(if_op) => {
                    if if_op.else_block.is_terminal && if_op.then_block.is_terminal {
                        break;
                    }
                }
                TypeResolvedOp::Memory { id, .. } => control::memory(stores, analyzer, op_id, id),
                TypeResolvedOp::SizeOf { id } => {
                    stack_ops::size_of(ctx, stores, analyzer, pass_ctx, op_id, id)
                }
                TypeResolvedOp::While(_) => control::analyze_while(analyzer, op_id),

                // Nothing to do here.
                TypeResolvedOp::CallFunction { .. } | TypeResolvedOp::PackStruct { .. } => {}
            },
        }
    }
}

pub fn analyze_item(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
) {
    let mut analyzer = ctx.take_analyzer(item_id);

    analyze_block(
        ctx,
        stores,
        &mut analyzer,
        pass_ctx,
        had_error,
        // TODO: Fix this shit
        #[allow(clippy::unnecessary_to_owned)]
        &ctx.get_item_body(item_id).to_owned(),
    );

    ctx.set_analyzer(item_id, analyzer);
}
