use ariadne::{Color, Label};
use stack_check::{eat_one_make_one, eat_two_make_one};

use crate::{
    context::{Context, ItemId},
    diagnostics,
    ir::{Arithmetic, Basic, Compare, Control, Memory, Op, OpCode, Stack, TypeResolvedOp},
    pass_manager::{
        static_analysis::{Analyzer, ValueId},
        PassContext,
    },
    Stores,
};

mod stack_check;
mod type_check;

fn analyze_block(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
    item_id: ItemId,
    block: &[Op<TypeResolvedOp>],
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
    emit_traces: bool,
) {
    let mut op_iter = block.iter();
    for op in op_iter.by_ref() {
        match &op.code {
            OpCode::Basic(bo) => match bo {
                Basic::Arithmetic(ao) => match ao {
                    Arithmetic::Add => {
                        let mut local_had_error = false;
                        eat_two_make_one(stores, analyzer, had_error, stack, op);
                        if !local_had_error {
                            type_check::arithmetic::add(stores, analyzer, &mut local_had_error, op);
                        }

                        *had_error |= local_had_error;
                    }

                    Arithmetic::BitAnd | Arithmetic::BitOr | Arithmetic::BitXor => {
                        let mut local_had_error = false;
                        eat_two_make_one(stores, analyzer, had_error, stack, op);
                        if !local_had_error {
                            type_check::arithmetic::bitand_bitor_bitxor(
                                stores,
                                analyzer,
                                &mut local_had_error,
                                op,
                            );
                        }

                        *had_error |= local_had_error;
                    }

                    Arithmetic::BitNot => {
                        let mut local_had_error = false;
                        eat_one_make_one(stores, analyzer, had_error, stack, op);
                        if !local_had_error {
                            type_check::arithmetic::bitnot(
                                stores,
                                analyzer,
                                &mut local_had_error,
                                op,
                            );
                        }
                        *had_error |= local_had_error;
                    }

                    Arithmetic::Div
                    | Arithmetic::Multiply
                    | Arithmetic::Rem
                    | Arithmetic::ShiftLeft
                    | Arithmetic::ShiftRight => {
                        let mut local_had_error = false;
                        eat_two_make_one(stores, analyzer, had_error, stack, op);
                        if !local_had_error {
                            type_check::arithmetic::multiply_div_rem_shift(
                                stores,
                                analyzer,
                                &mut local_had_error,
                                op,
                            );
                        }

                        *had_error |= local_had_error;
                    }

                    Arithmetic::Subtract => {
                        let mut local_had_error = false;
                        eat_two_make_one(stores, analyzer, had_error, stack, op);
                        if !local_had_error {
                            type_check::arithmetic::subtract(
                                stores,
                                analyzer,
                                &mut local_had_error,
                                op,
                            );
                        }

                        *had_error |= local_had_error;
                    }
                },
                Basic::Compare(co) => match co {
                    Compare::Equal => todo!(),
                    Compare::Less => todo!(),
                    Compare::LessEqual => todo!(),
                    Compare::Greater => todo!(),
                    Compare::GreaterEqual => todo!(),
                    Compare::NotEq => todo!(),
                    Compare::IsNull => todo!(),
                },
                Basic::Stack(so) => match so {
                    Stack::Dup { count } => todo!(),
                    Stack::Drop { count } => todo!(),
                    Stack::Emit { show_labels } => todo!(),
                    Stack::Over { depth } => todo!(),
                    Stack::Reverse { count } => todo!(),
                    Stack::Rotate {
                        item_count,
                        direction,
                        shift_count,
                    } => todo!(),
                    Stack::Swap { count } => todo!(),
                },
                Basic::Control(co) => match co {
                    Control::Epilogue => todo!(),
                    Control::Exit => todo!(),
                    Control::Prologue => todo!(),
                    Control::Return => todo!(),
                    Control::SysCall { arg_count } => todo!(),
                },
                Basic::Memory(mo) => match mo {
                    Memory::ExtractArray { emit_array } => todo!(),
                    Memory::ExtractStruct {
                        emit_struct,
                        field_name,
                    } => todo!(),
                    Memory::InsertArray { emit_array } => todo!(),
                    Memory::InsertStruct {
                        emit_struct,
                        field_name,
                    } => todo!(),
                    Memory::Load => todo!(),
                    Memory::PackArray { count } => todo!(),
                    Memory::Store => todo!(),
                    Memory::Unpack => todo!(),
                },
                Basic::PushBool(value) => todo!(),
                Basic::PushInt { width, value } => todo!(),
                Basic::PushStr { id, is_c_str } => todo!(),
            },
            OpCode::Complex(co) => match co {
                TypeResolvedOp::Cast { id } => todo!(),
                TypeResolvedOp::CallFunction { id } => todo!(),
                TypeResolvedOp::Const { id } => todo!(),
                TypeResolvedOp::If(_) => todo!(),
                TypeResolvedOp::PackStruct { id } => todo!(),
                TypeResolvedOp::Memory { id, is_global } => todo!(),
                TypeResolvedOp::SizeOf { id } => todo!(),
                TypeResolvedOp::While(_) => todo!(),
            },
        }
    }

    for op in op_iter {
        if matches!(&op.code, OpCode::Basic(Basic::Control(Control::Epilogue))) {
            // Implicitely added to procs, so we don't want to diagnose these.
            continue;
        }

        diagnostics::emit_warning(
            stores,
            op.token.location,
            "unreachable op",
            [Label::new(op.token.location).with_color(Color::Yellow)],
            None,
        )
    }
}

pub struct AnalyzerStats {
    pub max_stack_depth: usize,
    pub unique_item_count: usize,
}

pub fn analyze_item(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
    item_id: ItemId,
) -> AnalyzerStats {
    let mut analyzer = Analyzer::default();
    let mut stack: Vec<ValueId> = Vec::new();
    let mut max_stack_depth = 0;

    analyze_block(
        ctx,
        stores,
        &mut analyzer,
        pass_ctx,
        had_error,
        item_id,
        // TODO: Fix this shit
        &ctx.trir().get_item_body(item_id).to_owned(),
        &mut stack,
        &mut max_stack_depth,
        true,
    );

    let analyzer_stats = AnalyzerStats {
        max_stack_depth,
        unique_item_count: analyzer.value_count(),
    };

    ctx.set_analyzer(item_id, analyzer);

    analyzer_stats
}
