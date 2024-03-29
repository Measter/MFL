use ariadne::{Color, Label};
use intcast::IntCast;
use tracing::info;

use crate::{
    context::{Context, ItemId},
    diagnostics,
    ir::{
        Arithmetic, Basic, Compare, Control, Direction, IntKind, Op, OpCode, Stack, TypeResolvedOp,
    },
    n_ops::{SliceNOps, VecNOps},
    pass_manager::static_analysis::promote_int_type_bidirectional,
    type_store::IntWidth,
    Stores,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimulationError {
    UnsupportedOp,
    UnreadyConst,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimulatorValue {
    Int { width: IntWidth, kind: IntKind },
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
                (IntKind::Signed(a), IntKind::Signed(b)) => IntKind::Signed(s_op(a, b)),
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => IntKind::Unsigned(u_op(a, b)),
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
                (IntKind::Signed(a), IntKind::Signed(b)) => s_op(a, b) != 0,
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => u_op(a, b) != 0,
                _ => unreachable!(),
            };

            SimulatorValue::Bool(res)
        }
        (SimulatorValue::Bool(a), SimulatorValue::Bool(b)) => SimulatorValue::Bool(b_op(a, b)),
        _ => unreachable!(),
    }
}

fn simulate_execute_program_block(
    program: &Context,
    stores: &mut Stores,
    block: &[Op<TypeResolvedOp>],
    value_stack: &mut Vec<SimulatorValue>,
) -> Result<(), SimulationError> {
    let mut ip = 0;
    while let Some(op) = block.get(ip) {
        match &op.code {
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
                            kind: IntKind::Signed(v),
                        } => *v = !*v & width.mask() as i64,
                        SimulatorValue::Int {
                            width,
                            kind: IntKind::Unsigned(v),
                        } => *v = !*v & width.mask(),
                        SimulatorValue::Bool(v) => *v = !*v,
                    }
                }
            },
            OpCode::Basic(Basic::Compare(co_op)) => {
                if *co_op == Compare::IsNull {
                    emit_unsupported_diag(stores, op);
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
                Control::Exit | Control::SysCall { .. } => {
                    emit_unsupported_diag(stores, op);
                    return Err(SimulationError::UnsupportedOp);
                }
            },
            OpCode::Basic(Basic::Memory(_)) => {
                emit_unsupported_diag(stores, op);
                return Err(SimulationError::UnsupportedOp);
            }
            OpCode::Basic(Basic::PushBool(val)) => value_stack.push(SimulatorValue::Bool(*val)),
            OpCode::Basic(Basic::PushInt { width, value }) => {
                value_stack.push(SimulatorValue::Int {
                    width: *width,
                    kind: *value,
                })
            }
            OpCode::Basic(Basic::PushStr { .. }) => {
                emit_unsupported_diag(stores, op);
                return Err(SimulationError::UnsupportedOp);
            }
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

            OpCode::Complex(
                TypeResolvedOp::CallFunction { .. }
                | TypeResolvedOp::Cast { .. }
                | TypeResolvedOp::Memory { .. }
                | TypeResolvedOp::PackStruct { .. },
            ) => {
                emit_unsupported_diag(stores, op);
                return Err(SimulationError::UnsupportedOp);
            }

            OpCode::Complex(TypeResolvedOp::If(if_op)) => {
                simulate_execute_program_block(
                    program,
                    stores,
                    &if_op.condition.block,
                    value_stack,
                )?;

                let a = value_stack.pop().unwrap();
                if a == SimulatorValue::Bool(true) {
                    simulate_execute_program_block(
                        program,
                        stores,
                        &if_op.then_block.block,
                        value_stack,
                    )?;
                } else {
                    simulate_execute_program_block(
                        program,
                        stores,
                        &if_op.else_block.block,
                        value_stack,
                    )?;
                }
            }
            OpCode::Complex(TypeResolvedOp::SizeOf { id }) => {
                let size = stores.types.get_size_info(*id);
                value_stack.push(SimulatorValue::Int {
                    width: IntWidth::I64,
                    kind: IntKind::Unsigned(size.byte_width),
                });
            }
            OpCode::Complex(TypeResolvedOp::While(while_op)) => loop {
                simulate_execute_program_block(
                    program,
                    stores,
                    &while_op.condition.block,
                    value_stack,
                )?;
                let a = value_stack.pop().unwrap();
                if a == SimulatorValue::Bool(false) {
                    break;
                }
                simulate_execute_program_block(
                    program,
                    stores,
                    &while_op.body_block.block,
                    value_stack,
                )?;
            },
            OpCode::Complex(TypeResolvedOp::Const { id }) => {
                let Some(vals) = program.get_consts(*id) else {
                    return Err(SimulationError::UnreadyConst);
                };
                value_stack.extend(vals.iter().map(|(_, v)| *v));
            }
        }

        ip += 1;
    }

    Ok(())
}

fn emit_unsupported_diag(stores: &mut Stores, op: &Op<TypeResolvedOp>) {
    diagnostics::emit_error(
        stores,
        op.token.location,
        "operation not supported during const evaluation",
        [Label::new(op.token.location).with_color(Color::Red)],
        None,
    );
}

pub(crate) fn simulate_execute_program(
    program: &Context,
    stores: &mut Stores,
    item_id: ItemId,
) -> Result<Vec<SimulatorValue>, SimulationError> {
    info!("Make simulator type representation better.");
    let mut value_stack: Vec<SimulatorValue> = Vec::new();

    simulate_execute_program_block(
        program,
        stores,
        program.trir().get_item_body(item_id),
        &mut value_stack,
    )?;

    Ok(value_stack)
}
