use ariadne::{Color, Label};
use stack_check::{eat_one_make_one, eat_two_make_one, make_one};

use crate::{
    context::{Context, ItemId},
    diagnostics,
    error_signal::ErrorSignal,
    ir::{Arithmetic, Basic, Compare, Control, Memory, Op, OpCode, Stack, TypeResolvedOp},
    pass_manager::{
        static_analysis::{Analyzer, ValueId},
        PassContext,
    },
    type_store::Integer,
    Stores,
};

mod stack_check;
mod type_check;

type StackCheckFn =
    fn(&Stores, &mut Analyzer, &mut ErrorSignal, &mut Vec<ValueId>, &Op<TypeResolvedOp>);
type TypeCheckFn = fn(&mut Stores, &mut Analyzer, &mut ErrorSignal, &Op<TypeResolvedOp>);

fn get_arith_cmp_fns(bo: &Basic) -> (StackCheckFn, TypeCheckFn) {
    let (Basic::Arithmetic(_) | Basic::Compare(_)) = bo else {
        unreachable!()
    };

    let eat_fn = match bo {
        Basic::Arithmetic(Arithmetic::BitNot) | Basic::Compare(Compare::IsNull) => eat_one_make_one,
        _ => eat_two_make_one,
    };

    let op_fn = match bo {
        Basic::Arithmetic(ao) => match ao {
            Arithmetic::Add => type_check::arithmetic::add,
            Arithmetic::BitAnd | Arithmetic::BitOr | Arithmetic::BitXor => {
                type_check::arithmetic::bitand_bitor_bitxor
            }
            Arithmetic::BitNot => type_check::arithmetic::bitnot,
            Arithmetic::Div
            | Arithmetic::Multiply
            | Arithmetic::Rem
            | Arithmetic::ShiftLeft
            | Arithmetic::ShiftRight => type_check::arithmetic::multiply_div_rem_shift,
            Arithmetic::Subtract => type_check::arithmetic::subtract,
        },
        Basic::Compare(co) => match co {
            Compare::Equal | Compare::NotEq => type_check::comparative::equal,
            Compare::Less | Compare::LessEqual | Compare::Greater | Compare::GreaterEqual => {
                type_check::comparative::compare
            }
            Compare::IsNull => type_check::comparative::is_null,
        },
        _ => unreachable!(),
    };

    (eat_fn, op_fn)
}

fn analyze_block(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    pass_ctx: &mut PassContext,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    block: &[Op<TypeResolvedOp>],
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
) {
    let mut op_iter = block.iter();
    for op in op_iter.by_ref() {
        match &op.code {
            OpCode::Basic(bo) => match bo {
                Basic::Arithmetic(_) | Basic::Compare(_) => {
                    let (stack_check_fn, type_check_fn) = get_arith_cmp_fns(bo);
                    let mut local_had_error = ErrorSignal::new();
                    stack_check_fn(stores, analyzer, &mut local_had_error, stack, op);
                    if local_had_error.is_ok() {
                        type_check_fn(stores, analyzer, &mut local_had_error, op);
                    }
                    had_error.merge_with(local_had_error);
                }
                Basic::Stack(so) => match so {
                    Stack::Dup { count } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::stack_ops::dup(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            stack,
                            op,
                            *count,
                        );
                        if local_had_error.is_ok() {
                            type_check::stack_ops::dup_over(analyzer, op);
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Stack::Drop { count } => {
                        stack_check::stack_ops::drop(
                            stores, analyzer, had_error, stack, op, *count,
                        );
                    }
                    Stack::Emit { show_labels } => {
                        type_check::stack_ops::emit_stack(
                            stores,
                            analyzer,
                            stack,
                            op,
                            *show_labels,
                        );
                    }
                    Stack::Over { depth } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::stack_ops::over(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            stack,
                            op,
                            *depth,
                        );
                        if local_had_error.is_ok() {
                            type_check::stack_ops::dup_over(analyzer, op);
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Stack::Reverse { count } => {
                        stack_check::stack_ops::reverse(
                            stores, analyzer, had_error, stack, op, *count,
                        );
                    }
                    Stack::Rotate {
                        item_count,
                        direction,
                        shift_count,
                    } => {
                        stack_check::stack_ops::rotate(
                            stores,
                            analyzer,
                            had_error,
                            stack,
                            op,
                            *item_count,
                            *direction,
                            *shift_count,
                        );
                    }
                    Stack::Swap { count } => {
                        stack_check::stack_ops::swap(
                            stores, analyzer, had_error, stack, op, *count,
                        );
                    }
                },
                Basic::Control(co) => match co {
                    Control::Epilogue | Control::Return => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::control::epilogue_return(
                            ctx,
                            stores,
                            analyzer,
                            &mut local_had_error,
                            stack,
                            op,
                            item_id,
                        );
                        if local_had_error.is_ok() {
                            type_check::control::epilogue_return(
                                ctx,
                                stores,
                                analyzer,
                                &mut local_had_error,
                                op,
                                item_id,
                            );
                        }

                        had_error.merge_with(local_had_error);
                        // We're terminated the current block, so don't process any remaining ops.
                        break;
                    }
                    Control::Exit => {
                        analyzer.set_op_io(op, &[], &[]);
                        break;
                    }
                    Control::Prologue => {
                        stack_check::control::prologue(ctx, analyzer, stack, op, item_id);
                        type_check::control::prologue(ctx, analyzer, op, item_id);
                    }
                    Control::SysCall { arg_count } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::control::syscall(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            stack,
                            op,
                            *arg_count,
                        );
                        if local_had_error.is_ok() {
                            type_check::control::syscall(
                                stores,
                                analyzer,
                                &mut local_had_error,
                                op,
                            );
                        }

                        had_error.merge_with(local_had_error);
                    }
                },
                Basic::Memory(mo) => match mo {
                    Memory::ExtractArray { emit_array } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::extract_array(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            stack,
                            op,
                            *emit_array,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::extract_array(
                                ctx,
                                stores,
                                analyzer,
                                pass_ctx,
                                &mut local_had_error,
                                op,
                                *emit_array,
                            );
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Memory::ExtractStruct {
                        emit_struct,
                        field_name,
                    } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::extract_struct(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            stack,
                            op,
                            *emit_struct,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::extract_struct(
                                ctx,
                                stores,
                                analyzer,
                                pass_ctx,
                                &mut local_had_error,
                                op,
                                *field_name,
                                *emit_struct,
                            );
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Memory::InsertArray { emit_array } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::insert_array(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            stack,
                            op,
                            *emit_array,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::insert_array(
                                ctx,
                                stores,
                                analyzer,
                                pass_ctx,
                                &mut local_had_error,
                                op,
                                *emit_array,
                            );
                        };
                        had_error.merge_with(local_had_error);
                    }
                    Memory::InsertStruct {
                        emit_struct,
                        field_name,
                    } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::insert_struct(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            stack,
                            op,
                            *emit_struct,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::insert_struct(
                                ctx,
                                stores,
                                analyzer,
                                pass_ctx,
                                &mut local_had_error,
                                op,
                                *field_name,
                                *emit_struct,
                            );
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Memory::Load => {
                        let mut local_had_error = ErrorSignal::new();
                        eat_one_make_one(stores, analyzer, &mut local_had_error, stack, op);
                        if local_had_error.is_ok() {
                            type_check::memory::load(stores, analyzer, &mut local_had_error, op);
                        }
                        had_error.merge_with(local_had_error);
                    }
                    Memory::PackArray { count } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::pack_array(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            stack,
                            op,
                            *count,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::pack_array(
                                stores,
                                analyzer,
                                &mut local_had_error,
                                op,
                                *count,
                            );
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Memory::Store => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::store(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            stack,
                            op,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::store(stores, analyzer, &mut local_had_error, op);
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Memory::Unpack => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::unpack(
                            ctx,
                            stores,
                            analyzer,
                            pass_ctx,
                            &mut local_had_error,
                            stack,
                            op,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::unpack(stores, analyzer, &mut local_had_error, op);
                        }

                        had_error.merge_with(local_had_error);
                    }
                },
                Basic::PushBool(_) => {
                    make_one(analyzer, stack, op);
                    type_check::stack_ops::push_bool(stores, analyzer, op);
                }
                Basic::PushInt { width, value } => {
                    make_one(analyzer, stack, op);
                    type_check::stack_ops::push_int(
                        stores,
                        analyzer,
                        op,
                        (*width, value.to_signedness()).into(),
                    );
                }
                Basic::PushStr { is_c_str, .. } => {
                    make_one(analyzer, stack, op);
                    type_check::stack_ops::push_str(stores, analyzer, op, *is_c_str);
                }
            },
            OpCode::Complex(co) => match co {
                TypeResolvedOp::Cast { id } => {
                    let mut local_had_error = ErrorSignal::new();
                    eat_one_make_one(stores, analyzer, &mut local_had_error, stack, op);
                    if local_had_error.is_ok() {
                        type_check::stack_ops::cast(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            op,
                            *id,
                        );
                    }

                    had_error.merge_with(local_had_error);
                }
                TypeResolvedOp::CallFunction { id } | TypeResolvedOp::Const { id } => {
                    let mut local_had_error = ErrorSignal::new();
                    stack_check::control::call_function_const(
                        ctx,
                        stores,
                        analyzer,
                        &mut local_had_error,
                        stack,
                        op,
                        *id,
                    );
                    if local_had_error.is_ok() {
                        type_check::control::call_function_const(
                            ctx,
                            stores,
                            analyzer,
                            pass_ctx,
                            &mut local_had_error,
                            op,
                            *id,
                        );
                    }

                    had_error.merge_with(local_had_error);
                }
                TypeResolvedOp::If(if_op) => {
                    let mut local_had_error = ErrorSignal::new();
                    stack_check::control::analyze_if(
                        ctx,
                        stores,
                        analyzer,
                        pass_ctx,
                        &mut local_had_error,
                        item_id,
                        stack,
                        max_stack_depth,
                        op,
                        if_op,
                    );
                    if local_had_error.is_ok() {
                        type_check::control::analyze_if(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            op,
                            if_op,
                        );
                    }

                    had_error.merge_with(local_had_error);

                    if if_op.else_block.is_terminal && if_op.then_block.is_terminal {
                        break;
                    }
                }
                TypeResolvedOp::PackStruct { id } => {
                    let mut local_had_error = ErrorSignal::new();
                    stack_check::memory::pack_struct(
                        ctx,
                        stores,
                        analyzer,
                        pass_ctx,
                        &mut local_had_error,
                        stack,
                        op,
                        *id,
                    );
                    if local_had_error.is_ok() {
                        type_check::memory::pack_struct(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            op,
                            *id,
                        );
                        had_error.merge_with(local_had_error);
                    }
                }
                TypeResolvedOp::Memory { id, .. } => {
                    make_one(analyzer, stack, op);
                    type_check::control::memory(
                        ctx, stores, analyzer, pass_ctx, had_error, op, *id,
                    );
                }
                TypeResolvedOp::SizeOf { .. } => {
                    make_one(analyzer, stack, op);
                    type_check::stack_ops::push_int(stores, analyzer, op, Integer::U64);
                }
                TypeResolvedOp::While(while_op) => {
                    let mut local_had_error = ErrorSignal::new();
                    stack_check::control::analyze_while(
                        ctx,
                        stores,
                        analyzer,
                        pass_ctx,
                        &mut local_had_error,
                        item_id,
                        stack,
                        max_stack_depth,
                        op,
                        while_op,
                    );

                    if local_had_error.is_ok() {
                        type_check::control::analyze_while(
                            stores,
                            analyzer,
                            &mut local_had_error,
                            op,
                            while_op,
                        );
                    }

                    had_error.merge_with(local_had_error);
                }
            },
        }

        *max_stack_depth = stack.len().max(*max_stack_depth);
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
    had_error: &mut ErrorSignal,
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
        #[allow(clippy::unnecessary_to_owned)]
        &ctx.trir().get_item_body(item_id).to_owned(),
        &mut stack,
        &mut max_stack_depth,
    );

    let analyzer_stats = AnalyzerStats {
        max_stack_depth,
        unique_item_count: analyzer.value_count(),
    };

    ctx.set_analyzer(item_id, analyzer);

    analyzer_stats
}
