use crate::{
    context::{Context, ItemId},
    error_signal::ErrorSignal,
    ir::{Arithmetic, Basic, Compare, Control, Memory, Op, OpCode, Stack, TypeResolvedOp},
    pass_manager::{static_analysis::Analyzer, PassContext},
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
    block: &[Op<TypeResolvedOp>],
) {
    for op in block {
        match &op.code {
            OpCode::Basic(bo) => match bo {
                Basic::Arithmetic(ao) => match ao {
                    Arithmetic::Add => arithmetic::add(stores, analyzer, op, *ao),
                    Arithmetic::BitAnd | Arithmetic::BitOr | Arithmetic::BitXor => {
                        arithmetic::bitand_bitor_bitxor(stores, analyzer, op, *ao)
                    }
                    Arithmetic::BitNot => arithmetic::bitnot(stores, analyzer, op),
                    Arithmetic::Div
                    | Arithmetic::Multiply
                    | Arithmetic::Rem
                    | Arithmetic::ShiftLeft
                    | Arithmetic::ShiftRight => {
                        arithmetic::multiply_div_rem_shift(stores, analyzer, had_error, op, *ao)
                    }
                    Arithmetic::Subtract => {
                        arithmetic::subtract(stores, analyzer, had_error, op, *ao)
                    }
                },
                Basic::Compare(co) => match co {
                    Compare::Equal | Compare::NotEq => {
                        comparative::equal(stores, analyzer, had_error, op, *co)
                    }
                    Compare::Less
                    | Compare::LessEqual
                    | Compare::Greater
                    | Compare::GreaterEqual => {
                        comparative::compare(stores, analyzer, had_error, op, *co)
                    }
                    Compare::IsNull => comparative::is_null(analyzer, op),
                },
                Basic::Stack(so) => match so {
                    Stack::Dup { .. } | Stack::Over { .. } => stack_ops::dup_over(analyzer, op),

                    // These just change the order of the virtual stack, so there's no work to do here.
                    Stack::Drop { .. }
                    | Stack::Emit { .. }
                    | Stack::Reverse { .. }
                    | Stack::Rotate { .. }
                    | Stack::Swap { .. } => {}
                },
                Basic::Control(co) => match co {
                    Control::Epilogue | Control::Return => {
                        control::epilogue_return(ctx, stores, analyzer, had_error, op);

                        // We're terminated the current block, so don't process any remaining ops.
                        break;
                    }

                    // Nothing to do here.
                    Control::Exit | Control::Prologue | Control::SysCall { .. } => {}
                },
                Basic::Memory(mo) => match mo {
                    Memory::ExtractArray { .. } | Memory::InsertArray { .. } => {
                        memory::insert_extract_array(stores, analyzer, had_error, op)
                    }
                    // Nothing to do here.
                    Memory::ExtractStruct { .. }
                    | Memory::InsertStruct { .. }
                    | Memory::Load
                    | Memory::PackArray { .. }
                    | Memory::Store
                    | Memory::Unpack => {}
                },
                Basic::PushBool(value) => stack_ops::push_bool(analyzer, op, *value),
                Basic::PushInt { value, .. } => stack_ops::push_int(analyzer, op, *value),
                Basic::PushStr { .. } => {}
            },
            OpCode::Complex(co) => match co {
                TypeResolvedOp::Cast { id } => stack_ops::cast(stores, analyzer, op, *id),
                TypeResolvedOp::Const { id } => {
                    control::cp_const(ctx, stores, analyzer, pass_ctx, op, *id)
                }
                TypeResolvedOp::If(if_op) => {
                    if if_op.else_block.is_terminal && if_op.then_block.is_terminal {
                        break;
                    }
                }
                TypeResolvedOp::Memory { id, .. } => control::memory(analyzer, op, *id),
                TypeResolvedOp::SizeOf { id } => {
                    stack_ops::size_of(ctx, stores, analyzer, pass_ctx, op, *id)
                }
                TypeResolvedOp::While(_) => control::analyze_while(analyzer, op),

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
        &ctx.trir().get_item_body(item_id).to_owned(),
    );

    ctx.set_analyzer(item_id, analyzer);
}
