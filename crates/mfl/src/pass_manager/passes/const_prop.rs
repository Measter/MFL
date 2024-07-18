use crate::{
    context::{Context, ItemId},
    error_signal::ErrorSignal,
    ir::{Arithmetic, Basic, Compare, Op, OpCode, TypeResolvedOp},
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
