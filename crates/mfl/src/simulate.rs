use intcast::IntCast;
use stores::items::ItemId;
use tracing::info;

use crate::{
    ir::{Arithmetic, Basic, Compare, Control, Direction, OpCode, Stack, TypeResolvedOp},
    n_ops::{SliceNOps, VecNOps},
    pass_manager::{static_analysis::promote_int_type_bidirectional, PassManager},
    stores::{
        block::BlockId,
        diagnostics::Diagnostic,
        types::{IntWidth, Integer},
    },
    Stores,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimulationError {
    UnsupportedOp,
    UnavailableConst,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimulatorValue {
    Int { width: IntWidth, kind: Integer },
    Bool(bool),
}

fn apply_int_op(
    a: SimulatorValue,
    b: SimulatorValue,
    u_op: fn(u64, u64) -> u64,
    s_op: fn(i64, i64) -> i64,
) -> SimulatorValue {
    match (a, b) {
        (
            SimulatorValue::Int {
                width: a_width,
                kind: a_kind,
            },
            SimulatorValue::Int {
                width: b_width,
                kind: b_kind,
            },
        ) => {
            let to_int = promote_int_type_bidirectional(
                (a_width, a_kind.to_signedness()).into(),
                (b_width, b_kind.to_signedness()).into(),
            )
            .unwrap();
            let a_kind = a_kind.cast(to_int);
            let b_kind = b_kind.cast(to_int);

            let out_kind = match (a_kind, b_kind) {
                (Integer::Signed(a), Integer::Signed(b)) => Integer::Signed(s_op(a, b)),
                (Integer::Unsigned(a), Integer::Unsigned(b)) => Integer::Unsigned(u_op(a, b)),
                _ => unreachable!(),
            };

            SimulatorValue::Int {
                width: to_int.width,
                kind: out_kind,
            }
        }
        _ => unreachable!(),
    }
}

fn apply_bool_op(
    a: SimulatorValue,
    b: SimulatorValue,
    u_op: fn(u64, u64) -> u64,
    s_op: fn(i64, i64) -> i64,
    b_op: fn(bool, bool) -> bool,
) -> SimulatorValue {
    match (a, b) {
        (
            SimulatorValue::Int {
                width: a_width,
                kind: a_kind,
            },
            SimulatorValue::Int {
                width: b_width,
                kind: b_kind,
            },
        ) => {
            let to_int = promote_int_type_bidirectional(
                (a_width, a_kind.to_signedness()).into(),
                (b_width, b_kind.to_signedness()).into(),
            )
            .unwrap();
            let a_kind = a_kind.cast(to_int);
            let b_kind = b_kind.cast(to_int);

            let res = match (a_kind, b_kind) {
                (Integer::Signed(a), Integer::Signed(b)) => s_op(a, b) != 0,
                (Integer::Unsigned(a), Integer::Unsigned(b)) => u_op(a, b) != 0,
                _ => unreachable!(),
            };

            SimulatorValue::Bool(res)
        }
        (SimulatorValue::Bool(a), SimulatorValue::Bool(b)) => SimulatorValue::Bool(b_op(a, b)),
        _ => unreachable!(),
    }
}

fn simulate_execute_program_block(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    item_id: ItemId,
    block_id: BlockId,
    value_stack: &mut Vec<SimulatorValue>,
) -> Result<(), SimulationError> {
    let mut ip = 0;
    let block = stores.blocks.get_block(block_id).clone();
    while let Some(&op_id) = block.ops.get(ip) {
        match stores.ops.get_type_resolved(op_id).clone() {
            OpCode::Basic(Basic::Arithmetic(ar_op)) => match ar_op {
                Arithmetic::Add
                | Arithmetic::BitAnd
                | Arithmetic::BitOr
                | Arithmetic::BitXor
                | Arithmetic::Div
                | Arithmetic::Multiply
                | Arithmetic::Rem
                | Arithmetic::ShiftLeft
                | Arithmetic::ShiftRight
                | Arithmetic::Subtract => {
                    let [a, b] = value_stack.popn().unwrap();
                    value_stack.push(apply_int_op(
                        a,
                        b,
                        ar_op.get_unsigned_binary_op(),
                        ar_op.get_signed_binary_op(),
                    ));
                }
                Arithmetic::BitNot => {
                    let a = value_stack.last_mut().unwrap();
                    match a {
                        SimulatorValue::Int {
                            width,
                            kind: Integer::Signed(v),
                        } => *v = !*v & width.mask() as i64,
                        SimulatorValue::Int {
                            width,
                            kind: Integer::Unsigned(v),
                        } => *v = !*v & width.mask(),
                        SimulatorValue::Bool(v) => *v = !*v,
                    }
                }
            },
            OpCode::Basic(Basic::Compare(co_op)) => {
                if co_op == Compare::IsNull {
                    Diagnostic::unsupported_sim_op(stores, item_id, op_id);
                    return Err(SimulationError::UnsupportedOp);
                }

                let [a, b] = value_stack.popn().unwrap();
                value_stack.push(apply_bool_op(
                    a,
                    b,
                    co_op.get_unsigned_binary_op(),
                    co_op.get_signed_binary_op(),
                    co_op.get_bool_binary_op(),
                ));
            }
            OpCode::Basic(Basic::Control(con_op)) => match con_op {
                // These are no-ops here.
                Control::Epilogue | Control::Prologue => {}
                Control::Return => break,
                Control::Exit(_) | Control::SysCall { .. } => {
                    Diagnostic::unsupported_sim_op(stores, item_id, op_id);
                    return Err(SimulationError::UnsupportedOp);
                }
                Control::Cond(_) => {
                    todo!();
                }
                Control::While(while_op) => loop {
                    simulate_execute_program_block(
                        stores,
                        pass_manager,
                        item_id,
                        while_op.condition,
                        value_stack,
                    )?;
                    let a = value_stack.pop().unwrap();
                    if a == SimulatorValue::Bool(false) {
                        break;
                    }
                    simulate_execute_program_block(
                        stores,
                        pass_manager,
                        item_id,
                        while_op.body_block,
                        value_stack,
                    )?;
                },
            },
            OpCode::Basic(Basic::Memory(_) | Basic::PushStr { .. })
            | OpCode::Complex(
                TypeResolvedOp::CallFunction { .. }
                | TypeResolvedOp::Cast { .. }
                | TypeResolvedOp::Variable { .. }
                | TypeResolvedOp::PackStruct { .. },
            ) => {
                Diagnostic::unsupported_sim_op(stores, item_id, op_id);
                return Err(SimulationError::UnsupportedOp);
            }
            OpCode::Basic(Basic::PushBool(val)) => value_stack.push(SimulatorValue::Bool(val)),
            OpCode::Basic(Basic::PushInt { width, value }) => {
                value_stack.push(SimulatorValue::Int { width, kind: value })
            }
            OpCode::Basic(Basic::PushFloat { .. }) => todo!(),
            OpCode::Basic(Basic::Stack(stack_op)) => match stack_op {
                Stack::Dup { count } => {
                    let range = (value_stack.len() - count.inner.to_usize())..value_stack.len();
                    for i in range {
                        let a = value_stack[i];
                        value_stack.push(a);
                    }
                }
                Stack::Drop { count } => {
                    value_stack.truncate(value_stack.len() - count.inner.to_usize())
                }
                // Only emits a display of the stack.
                Stack::Emit { .. } => {}
                Stack::Over { depth } => {
                    let value = value_stack[value_stack.len() - 1 - depth.inner.to_usize()];
                    value_stack.push(value);
                }
                Stack::Reverse { count } => {
                    value_stack
                        .lastn_mut(count.inner.to_usize())
                        .unwrap()
                        .reverse();
                }
                Stack::Rotate {
                    item_count,
                    direction,
                    shift_count,
                } => {
                    let shift_count = shift_count.inner % item_count.inner;
                    let start = value_stack.len() - item_count.inner.to_usize();
                    match direction {
                        Direction::Left => value_stack[start..].rotate_left(shift_count.to_usize()),
                        Direction::Right => {
                            value_stack[start..].rotate_right(shift_count.to_usize())
                        }
                    }
                }
                Stack::Swap { count } => {
                    let slice_start = value_stack.len() - count.inner.to_usize();
                    let (rest, a_slice) = value_stack.split_at_mut(slice_start);
                    let (_, b_slice) = rest.split_at_mut(rest.len() - count.inner.to_usize());

                    a_slice.swap_with_slice(b_slice);
                }
            },

            OpCode::Complex(TypeResolvedOp::SizeOf { id }) => {
                let size = stores.types.get_size_info(id);
                value_stack.push(SimulatorValue::Int {
                    width: IntWidth::I64,
                    kind: Integer::Unsigned(size.byte_width),
                });
            }
            OpCode::Complex(TypeResolvedOp::Const { id }) => {
                if pass_manager
                    .ensure_evaluated_consts_asserts(stores, id)
                    .is_err()
                {
                    return Err(SimulationError::UnavailableConst);
                }

                let Some(vals) = stores.items.get_consts(id) else {
                    unreachable!();
                };
                value_stack.extend(vals.iter().copied());
            }
            OpCode::Complex(TypeResolvedOp::AssumeInit { .. }) => {}
        }

        ip += 1;
    }

    Ok(())
}

pub(crate) fn simulate_execute_program(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    item_id: ItemId,
) -> Result<Vec<SimulatorValue>, SimulationError> {
    info!("Make simulator type representation better.");
    let mut value_stack: Vec<SimulatorValue> = Vec::new();

    let block = stores.items.get_item_body(item_id);
    simulate_execute_program_block(stores, pass_manager, item_id, block, &mut value_stack)?;

    Ok(value_stack)
}
