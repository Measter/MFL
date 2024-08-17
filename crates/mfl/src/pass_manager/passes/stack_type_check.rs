use ariadne::{Color, Label};
use stack_check::{eat_one_make_one, eat_two_make_one, make_one};
use stores::items::ItemId;

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{Arithmetic, Basic, Compare, Control, Memory, OpCode, Stack, TypeResolvedOp},
    pass_manager::PassManager,
    stores::{block::BlockId, ops::OpId, types::IntKind, values::ValueId},
    Stores,
};

mod stack_check;
mod type_check;

type StackCheckFn = fn(&mut Stores, &mut ErrorSignal, &mut Vec<ValueId>, OpId);
type TypeCheckFn = fn(&mut Stores, &mut ErrorSignal, OpId);

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
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    block_id: BlockId,
    stack: &mut Vec<ValueId>,
    max_stack_depth: &mut usize,
) {
    let block = stores.blocks.get_block(block_id).clone();
    let mut op_iter = block.ops.iter();
    for &op_id in op_iter.by_ref() {
        let op_code = stores.ops.get_type_resolved(op_id).clone();
        match op_code {
            OpCode::Basic(bo) => match bo {
                Basic::Arithmetic(_) | Basic::Compare(_) => {
                    let (stack_check_fn, type_check_fn) = get_arith_cmp_fns(&bo);
                    let mut local_had_error = ErrorSignal::new();
                    stack_check_fn(stores, &mut local_had_error, stack, op_id);
                    if local_had_error.is_ok() {
                        type_check_fn(stores, &mut local_had_error, op_id);
                    }
                    had_error.merge_with(local_had_error);
                }
                Basic::Stack(so) => match so {
                    Stack::Dup { count } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::stack_ops::dup(
                            stores,
                            &mut local_had_error,
                            stack,
                            op_id,
                            count,
                        );
                        if local_had_error.is_ok() {
                            type_check::stack_ops::dup_over(stores, op_id);
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Stack::Drop { count } => {
                        stack_check::stack_ops::drop(stores, had_error, stack, op_id, count);
                    }
                    Stack::Emit { show_labels } => {
                        stores.ops.set_op_io(op_id, &[], &[]);
                        type_check::stack_ops::emit_stack(stores, stack, op_id, show_labels);
                    }
                    Stack::Over { depth } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::stack_ops::over(
                            stores,
                            &mut local_had_error,
                            stack,
                            op_id,
                            depth,
                        );
                        if local_had_error.is_ok() {
                            type_check::stack_ops::dup_over(stores, op_id);
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Stack::Reverse { count } => {
                        stack_check::stack_ops::reverse(stores, had_error, stack, op_id, count);
                    }
                    Stack::Rotate {
                        item_count,
                        direction,
                        shift_count,
                    } => {
                        stack_check::stack_ops::rotate(
                            stores,
                            had_error,
                            stack,
                            op_id,
                            item_count,
                            direction,
                            shift_count,
                        );
                    }
                    Stack::Swap { count } => {
                        stack_check::stack_ops::swap(stores, had_error, stack, op_id, count);
                    }
                },
                Basic::Control(co) => match co {
                    Control::Epilogue | Control::Return => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::control::epilogue_return(
                            stores,
                            &mut local_had_error,
                            stack,
                            op_id,
                            item_id,
                        );
                        if local_had_error.is_ok() {
                            type_check::control::epilogue_return(
                                stores,
                                &mut local_had_error,
                                op_id,
                                item_id,
                            );
                        }

                        had_error.merge_with(local_had_error);
                        // We're terminated the current block, so don't process any remaining ops.
                        break;
                    }
                    Control::Exit => {
                        stores.ops.set_op_io(op_id, &[], &[]);
                        break;
                    }
                    Control::Prologue => {
                        stack_check::control::prologue(stores, stack, op_id, item_id);
                        type_check::control::prologue(stores, op_id, item_id);
                    }
                    Control::SysCall { arg_count } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::control::syscall(
                            stores,
                            &mut local_had_error,
                            stack,
                            op_id,
                            arg_count,
                        );
                        if local_had_error.is_ok() {
                            type_check::control::syscall(stores, &mut local_had_error, op_id);
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Control::If(if_op) => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::control::analyze_if(
                            stores,
                            pass_manager,
                            &mut local_had_error,
                            item_id,
                            stack,
                            max_stack_depth,
                            op_id,
                            &if_op,
                        );
                        if local_had_error.is_ok() {
                            type_check::control::analyze_if(
                                stores,
                                &mut local_had_error,
                                op_id,
                                &if_op,
                            );
                        }

                        had_error.merge_with(local_had_error);

                        if stores.blocks.is_terminal(if_op.else_block)
                            && stores.blocks.is_terminal(if_op.then_block)
                        {
                            break;
                        }
                    }
                    Control::While(while_op) => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::control::analyze_while(
                            stores,
                            pass_manager,
                            &mut local_had_error,
                            item_id,
                            stack,
                            max_stack_depth,
                            op_id,
                            &while_op,
                        );

                        if local_had_error.is_ok() {
                            type_check::control::analyze_while(
                                stores,
                                &mut local_had_error,
                                op_id,
                                &while_op,
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
                            &mut local_had_error,
                            stack,
                            op_id,
                            emit_array,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::extract_array(
                                stores,
                                pass_manager,
                                &mut local_had_error,
                                op_id,
                                emit_array,
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
                            &mut local_had_error,
                            stack,
                            op_id,
                            emit_struct,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::extract_struct(
                                stores,
                                pass_manager,
                                &mut local_had_error,
                                op_id,
                                field_name,
                                emit_struct,
                            );
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Memory::FieldAccess { field_name } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::eat_one_make_one(stores, &mut local_had_error, stack, op_id);
                        if local_had_error.is_ok() {
                            type_check::memory::field_access(
                                stores,
                                pass_manager,
                                &mut local_had_error,
                                op_id,
                                field_name,
                            );
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Memory::InsertArray { emit_array } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::insert_array(
                            stores,
                            &mut local_had_error,
                            stack,
                            op_id,
                            emit_array,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::insert_array(
                                stores,
                                pass_manager,
                                &mut local_had_error,
                                op_id,
                                emit_array,
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
                            &mut local_had_error,
                            stack,
                            op_id,
                            emit_struct,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::insert_struct(
                                stores,
                                pass_manager,
                                &mut local_had_error,
                                op_id,
                                field_name,
                                emit_struct,
                            );
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Memory::Load => {
                        let mut local_had_error = ErrorSignal::new();
                        eat_one_make_one(stores, &mut local_had_error, stack, op_id);
                        if local_had_error.is_ok() {
                            type_check::memory::load(stores, &mut local_had_error, op_id);
                        }
                        had_error.merge_with(local_had_error);
                    }
                    Memory::PackArray { count } => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::pack_array(
                            stores,
                            &mut local_had_error,
                            stack,
                            op_id,
                            count,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::pack_array(
                                stores,
                                &mut local_had_error,
                                op_id,
                                count,
                            );
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Memory::Store => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::store(stores, &mut local_had_error, stack, op_id);
                        if local_had_error.is_ok() {
                            type_check::memory::store(stores, &mut local_had_error, op_id);
                        }

                        had_error.merge_with(local_had_error);
                    }
                    Memory::Unpack => {
                        let mut local_had_error = ErrorSignal::new();
                        stack_check::memory::unpack(
                            stores,
                            pass_manager,
                            &mut local_had_error,
                            stack,
                            op_id,
                        );
                        if local_had_error.is_ok() {
                            type_check::memory::unpack(stores, &mut local_had_error, op_id);
                        }

                        had_error.merge_with(local_had_error);
                    }
                },
                Basic::PushBool(_) => {
                    make_one(stores, stack, op_id);
                    type_check::stack_ops::push_bool(stores, op_id);
                }
                Basic::PushInt { width, value } => {
                    make_one(stores, stack, op_id);
                    type_check::stack_ops::push_int(
                        stores,
                        op_id,
                        (width, value.to_signedness()).into(),
                    );
                }
                Basic::PushFloat { width, .. } => {
                    make_one(stores, stack, op_id);
                    type_check::stack_ops::push_float(stores, op_id, width)
                }
                Basic::PushStr { .. } => {
                    make_one(stores, stack, op_id);
                    type_check::stack_ops::push_str(stores, op_id);
                }
            },
            OpCode::Complex(co) => match co {
                TypeResolvedOp::Cast { id } => {
                    let mut local_had_error = ErrorSignal::new();
                    eat_one_make_one(stores, &mut local_had_error, stack, op_id);
                    if local_had_error.is_ok() {
                        type_check::stack_ops::cast(stores, &mut local_had_error, op_id, id);
                    }

                    had_error.merge_with(local_had_error);
                }
                TypeResolvedOp::CallFunction { id, .. } | TypeResolvedOp::Const { id } => {
                    let mut local_had_error = ErrorSignal::new();
                    stack_check::control::call_function_const(
                        stores,
                        &mut local_had_error,
                        stack,
                        op_id,
                        id,
                    );
                    if local_had_error.is_ok() {
                        type_check::control::call_function_const(
                            stores,
                            pass_manager,
                            &mut local_had_error,
                            op_id,
                            id,
                        );
                    }

                    had_error.merge_with(local_had_error);
                }
                TypeResolvedOp::PackStruct { id } => {
                    let mut local_had_error = ErrorSignal::new();
                    stack_check::memory::pack_struct(
                        stores,
                        pass_manager,
                        &mut local_had_error,
                        stack,
                        op_id,
                        id,
                    );
                    if local_had_error.is_ok() {
                        type_check::memory::pack_struct(stores, &mut local_had_error, op_id, id);
                    }
                    had_error.merge_with(local_had_error);
                }
                TypeResolvedOp::Variable { id, .. } => {
                    make_one(stores, stack, op_id);
                    type_check::control::variable(stores, pass_manager, had_error, op_id, id);
                }
                TypeResolvedOp::SizeOf { .. } => {
                    make_one(stores, stack, op_id);
                    type_check::stack_ops::push_int(stores, op_id, IntKind::U64);
                }
                // Only applies during const-prop
                TypeResolvedOp::AssumeInit { .. } => {}
            },
        }

        *max_stack_depth = stack.len().max(*max_stack_depth);
    }

    for &op_id in op_iter {
        let op_code = stores.ops.get_type_resolved(op_id);
        if matches!(op_code, OpCode::Basic(Basic::Control(Control::Epilogue))) {
            // Implicitely added to procs, so we don't want to diagnose these.
            continue;
        }

        let op_loc = stores.ops.get_token(op_id).location;
        diagnostics::emit_warning(
            stores,
            op_loc,
            "unreachable op",
            [Label::new(op_loc).with_color(Color::Yellow)],
            None,
        );
    }
}

pub struct AnalyzerStats {
    pub max_stack_depth: usize,
    pub unique_item_count: usize,
}

pub fn analyze_item(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
) -> AnalyzerStats {
    let mut stack: Vec<ValueId> = Vec::new();
    let mut max_stack_depth = 0;
    let pre_value_count = stores.values.value_count();

    let block_id = stores.items.get_item_body(item_id);
    analyze_block(
        stores,
        pass_manager,
        had_error,
        item_id,
        block_id,
        &mut stack,
        &mut max_stack_depth,
    );

    let unique_item_count = stores.values.value_count() - pre_value_count;

    AnalyzerStats {
        max_stack_depth,
        unique_item_count,
    }
}
