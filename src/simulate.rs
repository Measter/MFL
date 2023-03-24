use ariadne::{Color, Label};
use intcast::IntCast;
use tracing::error;

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::{SliceNOps, VecNOps},
    opcode::{Direction, IntKind, Op, OpCode},
    program::{static_analysis::promote_int_type_bidirectional, ItemId, ItemKind, Program},
    source_file::SourceStorage,
    type_store::IntWidth,
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
            let (to_signed, to_width) = promote_int_type_bidirectional(
                a_width,
                a_kind.to_signedness(),
                b_width,
                b_kind.to_signedness(),
            )
            .unwrap();
            let a_kind = a_kind.cast(to_width, to_signed);
            let b_kind = b_kind.cast(to_width, to_signed);

            let out_kind = match (a_kind, b_kind) {
                (IntKind::Signed(a), IntKind::Signed(b)) => IntKind::Signed(s_op(a, b)),
                (IntKind::Unsigned(a), IntKind::Unsigned(b)) => IntKind::Unsigned(u_op(a, b)),
                _ => unreachable!(),
            };

            SimulatorValue::Int {
                width: to_width,
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
            let (to_signed, to_width) = promote_int_type_bidirectional(
                a_width,
                a_kind.to_signedness(),
                b_width,
                b_kind.to_signedness(),
            )
            .unwrap();
            let a_kind = a_kind.cast(to_width, to_signed);
            let b_kind = b_kind.cast(to_width, to_signed);

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

fn generate_error(msg: impl ToString, op: &Op, source_store: &SourceStorage) {
    let mut labels = vec![Label::new(op.token.location).with_color(Color::Red)];

    for source in &op.expansions {
        labels.push(
            Label::new(*source)
                .with_color(Color::Blue)
                .with_message("expanded from here"),
        );
    }

    diagnostics::emit_error(op.token.location, msg, labels, None, source_store);
}

fn simulate_execute_program_block(
    program: &Program,
    block: &[Op],
    value_stack: &mut Vec<SimulatorValue>,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), SimulationError> {
    let mut ip = 0;
    while let Some(op) = block.get(ip) {
        match &op.code {
            OpCode::Add
            | OpCode::Subtract
            | OpCode::Multiply
            | OpCode::Div
            | OpCode::Rem
            | OpCode::BitOr
            | OpCode::BitAnd
            | OpCode::BitXor
            | OpCode::ShiftLeft
            | OpCode::ShiftRight => {
                let [a, b] = value_stack.popn().unwrap();
                value_stack.push(apply_int_op(
                    a,
                    b,
                    op.code.get_unsigned_binary_op(),
                    op.code.get_signed_binary_op(),
                ));
            }

            OpCode::BitNot => {
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

            OpCode::PushBool(val) => value_stack.push(SimulatorValue::Bool(*val)),
            OpCode::PushInt { value, width } => value_stack.push(SimulatorValue::Int {
                width: *width,
                kind: *value,
            }),
            // It's a bit weird, given you can't do much with a string, but
            // you could just drop the address that gets pushed leaving the length
            // which can be used in a const context.
            OpCode::PushStr { id, is_c_str } => {
                let literal = interner.resolve_literal(*id);
                if !is_c_str {
                    // Strings are null-terminated during parsing, but the MFL-style strings shouldn't
                    // include that character.
                    value_stack.push(SimulatorValue::Int {
                        width: IntWidth::I64,
                        kind: IntKind::Unsigned(literal.len() as u64 - 1),
                    });
                }
                // A garbage value is fine, because you can't read/write memory in a const-context anyway.
                value_stack.push(SimulatorValue::Int {
                    width: IntWidth::I64,
                    kind: IntKind::Unsigned(0),
                });
            }
            OpCode::Drop { count, .. } => {
                value_stack.truncate(value_stack.len() - count.to_usize())
            }

            OpCode::While(while_op) => loop {
                simulate_execute_program_block(
                    program,
                    &while_op.condition,
                    value_stack,
                    interner,
                    source_store,
                )?;
                let a = value_stack.pop().unwrap();
                if a == SimulatorValue::Bool(false) {
                    break;
                }
                simulate_execute_program_block(
                    program,
                    &while_op.body_block,
                    value_stack,
                    interner,
                    source_store,
                )?;
            },

            OpCode::If(if_op) => {
                simulate_execute_program_block(
                    program,
                    &if_op.condition,
                    value_stack,
                    interner,
                    source_store,
                )?;

                let a = value_stack.pop().unwrap();
                if a == SimulatorValue::Bool(true) {
                    simulate_execute_program_block(
                        program,
                        &if_op.then_block,
                        value_stack,
                        interner,
                        source_store,
                    )?
                } else {
                    simulate_execute_program_block(
                        program,
                        &if_op.else_block,
                        value_stack,
                        interner,
                        source_store,
                    )?;
                }
            }

            OpCode::Greater
            | OpCode::GreaterEqual
            | OpCode::Less
            | OpCode::LessEqual
            | OpCode::Equal
            | OpCode::NotEq => {
                let [a, b] = value_stack.popn().unwrap();
                value_stack.push(apply_bool_op(
                    a,
                    b,
                    op.code.get_unsigned_binary_op(),
                    op.code.get_signed_binary_op(),
                    op.code.get_bool_binary_op(),
                ));
            }
            OpCode::Dup { count, .. } => {
                let range = (value_stack.len() - count.to_usize())..value_stack.len();
                for i in range {
                    let a = value_stack[i];
                    value_stack.push(a);
                }
            }
            OpCode::Over { depth, .. } => {
                let value = value_stack[value_stack.len() - 1 - depth.to_usize()];
                value_stack.push(value);
            }
            OpCode::Rot {
                item_count,
                direction,
                shift_count,
                ..
            } => {
                let shift_count = shift_count % item_count;
                let start = value_stack.len() - item_count.to_usize();
                match direction {
                    Direction::Left => value_stack[start..].rotate_left(shift_count.to_usize()),
                    Direction::Right => value_stack[start..].rotate_right(shift_count.to_usize()),
                }
            }
            OpCode::Swap { count, .. } => {
                let slice_start = value_stack.len() - count.to_usize();
                let (rest, a_slice) = value_stack.split_at_mut(slice_start);
                let (_, b_slice) = rest.split_at_mut(rest.len() - count.to_usize());

                a_slice.swap_with_slice(b_slice);
            }
            OpCode::Reverse { count, .. } => {
                value_stack.lastn_mut(count.to_usize()).unwrap().reverse();
            }

            // These are no-ops for the simulator, only there to help the compiler.
            OpCode::Epilogue | OpCode::Prologue | OpCode::EmitStack(_) => {}
            OpCode::Return { .. } => break,

            OpCode::ResolvedIdent { item_id, .. } => {
                let referenced_item = program.get_item_header(*item_id);

                match referenced_item.kind() {
                    ItemKind::Const => {
                        let Some(vals) = program.get_consts(*item_id) else {
                            return Err(SimulationError::UnreadyConst);
                        };
                        value_stack.extend(vals.iter().map(|(_, v)| *v));
                    }
                    _ => {
                        generate_error("non-const cannot be refenced in a const", op, source_store);
                        return Err(SimulationError::UnsupportedOp);
                    }
                }
            }

            OpCode::ArgC
            | OpCode::ArgV
            | OpCode::CallFunction { .. }
            | OpCode::Memory { .. }
            | OpCode::ResolvedCast { .. }
            | OpCode::PackArray { .. }
            | OpCode::PackStruct { .. }
            | OpCode::Unpack { .. }
            | OpCode::InsertArray { .. }
            | OpCode::ExtractArray { .. }
            | OpCode::InsertStruct { .. }
            | OpCode::ExtractStruct { .. }
            | OpCode::Load
            | OpCode::Store
            | OpCode::SysCall { .. } => {
                generate_error(
                    "operation not supported during const evaluation",
                    op,
                    source_store,
                );
                return Err(SimulationError::UnsupportedOp);
            }

            OpCode::UnresolvedCast { .. }
            | OpCode::UnresolvedIdent(_)
            | OpCode::UnresolvedPackStruct { .. } => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }

        ip += 1;
    }

    Ok(())
}

pub(crate) fn simulate_execute_program(
    program: &Program,
    item_id: ItemId,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<Vec<SimulatorValue>, SimulationError> {
    error!("Make simulator type representation better.");
    let mut value_stack: Vec<SimulatorValue> = Vec::new();

    simulate_execute_program_block(
        program,
        program.get_item_body(item_id),
        &mut value_stack,
        interner,
        source_store,
    )?;

    Ok(value_stack)
}
