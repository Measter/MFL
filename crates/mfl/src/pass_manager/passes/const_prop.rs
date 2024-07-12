use crate::{
    context::{Context, ItemId},
    error_signal::ErrorSignal,
    ir::{Arithmetic, Basic, Op, OpCode, TypeResolvedOp},
    pass_manager::{static_analysis::Analyzer, PassContext},
    Stores,
};

mod arithmetic;
mod comparative;

fn analyze_block(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    block: &[Op<TypeResolvedOp>],
    emit_traces: bool,
) {
    let mut op_iter = block.iter();
    for op in op_iter.by_ref() {
        match &op.code {
            OpCode::Basic(bo) => match bo {
                Basic::Arithmetic(ao) => match ao {
                    Arithmetic::Add => arithmetic::add(stores, analyzer, op, *ao),
                    Arithmetic::BitAnd => todo!(),
                    Arithmetic::BitNot => todo!(),
                    Arithmetic::BitOr => todo!(),
                    Arithmetic::BitXor => todo!(),
                    Arithmetic::Div => todo!(),
                    Arithmetic::Multiply => todo!(),
                    Arithmetic::Rem => todo!(),
                    Arithmetic::ShiftLeft => todo!(),
                    Arithmetic::ShiftRight => todo!(),
                    Arithmetic::Subtract => todo!(),
                },
                Basic::Compare(_) => todo!(),
                Basic::Stack(_) => todo!(),
                Basic::Control(_) => todo!(),
                Basic::Memory(_) => todo!(),
                Basic::PushBool(_) => todo!(),
                Basic::PushInt { width, value } => todo!(),
                Basic::PushStr { id, is_c_str } => todo!(),
            },
            OpCode::Complex(_) => todo!(),
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
        item_id,
        // TODO: Fix this shit
        #[allow(clippy::unnecessary_to_owned)]
        &ctx.trir().get_item_body(item_id).to_owned(),
        true,
    );

    ctx.set_analyzer(item_id, analyzer);
}
