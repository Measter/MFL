use ariadne::{Color, Label};
use tracing::error;

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::VecNOps,
    opcode::{Direction, Op, OpCode},
    program::{Procedure, ProcedureKind, Program},
    source_file::SourceStorage,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimulationError {
    UnsupportedOp,
    UnreadyConst,
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
    value_stack: &mut Vec<u64>,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<(), SimulationError> {
    let mut ip = 0;
    while let Some(op) = block.get(ip) {
        match &op.code {
            OpCode::Add => {
                let ([b], a) = value_stack.popn_last_mut().unwrap();
                *a += b;
            }
            OpCode::Subtract => {
                let ([b], a) = value_stack.popn_last_mut().unwrap();
                *a -= b;
            }
            OpCode::Multiply => {
                let ([b], a) = value_stack.popn_last_mut().unwrap();
                *a *= b;
            }
            OpCode::DivMod => {
                let [a, b] = value_stack.popn().unwrap();
                let (rem, quot) = (a % b, a / b);
                value_stack.push(quot);
                value_stack.push(rem);
            }

            OpCode::BitOr => {
                let ([b], a) = value_stack.popn_last_mut().unwrap();
                *a |= b;
            }
            OpCode::BitNot => {
                let a = value_stack.last_mut().unwrap();
                *a = !*a;
            }
            OpCode::BitAnd => {
                let ([b], a) = value_stack.popn_last_mut().unwrap();
                *a &= b;
            }
            OpCode::ShiftLeft => {
                let ([b], a) = value_stack.popn_last_mut().unwrap();
                *a <<= b;
            }
            OpCode::ShiftRight => {
                let ([b], a) = value_stack.popn_last_mut().unwrap();
                *a >>= b;
            }

            OpCode::PushBool(val) => value_stack.push(*val as _),
            OpCode::PushInt { value, .. } => value_stack.push(*value),
            // It's a bit weird, given you can't do much with a string, but
            // you could just drop the address that gets pushed leaving the length
            // which can be used in a const context.
            OpCode::PushStr { id, is_c_str } => {
                let literal = interner.resolve_literal(*id);
                if !is_c_str {
                    // Strings are null-terminated during parsing, but the Porth-style strings shouldn't
                    // include that character.
                    value_stack.push(literal.len() as u64 - 1);
                }
                // Nullptr is fine, because you can't read/write memory in a const-context anyway.
                value_stack.push(0);
            }
            OpCode::Drop { count, .. } => value_stack.truncate(value_stack.len() - count),

            OpCode::While { body, .. } => loop {
                simulate_execute_program_block(
                    program,
                    &body.condition,
                    value_stack,
                    interner,
                    source_store,
                )?;
                let a = value_stack.pop().unwrap();
                if a == 0 {
                    break;
                }
                simulate_execute_program_block(
                    program,
                    &body.block,
                    value_stack,
                    interner,
                    source_store,
                )?;
            },

            OpCode::If {
                condition,
                else_block,
                ..
            } => {
                simulate_execute_program_block(
                    program,
                    &condition.condition,
                    value_stack,
                    interner,
                    source_store,
                )?;

                let a = value_stack.pop().unwrap();
                if a == 0 {
                    simulate_execute_program_block(
                        program,
                        &condition.block,
                        value_stack,
                        interner,
                        source_store,
                    )?
                } else {
                    simulate_execute_program_block(
                        program,
                        else_block,
                        value_stack,
                        interner,
                        source_store,
                    )?;
                }
            }
            // OpCode::DoIf { end_ip, .. } => {
            //     let a = value_stack.pop().unwrap();

            //     if a == 0 {
            //         ip = end_ip + 1;
            //         continue;
            //     }
            // }
            // OpCode::Elif { end_ip, .. } | OpCode::Else { end_ip, .. } => ip = *end_ip,
            // OpCode::EndIf { .. } => {}
            OpCode::Greater => {
                let [a, b] = value_stack.popn().unwrap();
                value_stack.push((a > b) as u64);
            }
            OpCode::GreaterEqual => {
                let [a, b] = value_stack.popn().unwrap();
                value_stack.push((a >= b) as u64);
            }
            OpCode::Less => {
                let [a, b] = value_stack.popn().unwrap();
                value_stack.push((a < b) as u64);
            }
            OpCode::LessEqual => {
                let [a, b] = value_stack.popn().unwrap();
                value_stack.push((a <= b) as u64);
            }
            OpCode::Equal => {
                let [a, b] = value_stack.popn().unwrap();
                value_stack.push((a == b) as u64);
            }
            OpCode::NotEq => {
                let [a, b] = value_stack.popn().unwrap();
                value_stack.push((a != b) as u64);
            }

            OpCode::Dup { count, .. } => {
                let range = (value_stack.len() - count)..value_stack.len();
                for i in range {
                    let a = value_stack[i];
                    value_stack.push(a);
                }
            }
            OpCode::Over { depth, .. } => {
                let value = value_stack[value_stack.len() - 1 - depth];
                value_stack.push(value);
            }
            OpCode::Rot {
                item_count,
                direction,
                shift_count,
                ..
            } => {
                let shift_count = shift_count % item_count;
                let start = value_stack.len() - item_count;
                match direction {
                    Direction::Left => value_stack[start..].rotate_left(shift_count),
                    Direction::Right => value_stack[start..].rotate_right(shift_count),
                }
            }
            OpCode::Swap { count, .. } => {
                let slice_start = value_stack.len() - count;
                let (rest, a_slice) = value_stack.split_at_mut(slice_start);
                let (_, b_slice) = rest.split_at_mut(rest.len() - count);

                a_slice.swap_with_slice(b_slice);
            }

            OpCode::Cast { .. } => {}

            // These are no-ops for the simulator, only there to help the compiler.
            OpCode::Epilogue | OpCode::Prologue => {}
            OpCode::Return { .. } => break,

            OpCode::ResolvedIdent { proc_id, .. } => {
                let referenced_proc = program.get_proc_header(*proc_id);

                match referenced_proc.kind() {
                    ProcedureKind::Const => {
                        let Some(vals) = program.get_consts(*proc_id) else {
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
            | OpCode::CallProc { .. }
            | OpCode::Load { .. }
            | OpCode::Memory { .. }
            | OpCode::Store { .. }
            | OpCode::SysCall { .. } => {
                generate_error(
                    "operation not supported during const evaluation",
                    op,
                    source_store,
                );
                return Err(SimulationError::UnsupportedOp);
            }

            OpCode::UnresolvedIdent { .. } => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }

        ip += 1;
    }

    Ok(())
}

pub(crate) fn simulate_execute_program(
    program: &Program,
    procedure: &Procedure,
    interner: &Interners,
    source_store: &SourceStorage,
) -> Result<Vec<u64>, SimulationError> {
    error!("Make simulator type representation better.");
    let mut value_stack: Vec<u64> = Vec::new();

    simulate_execute_program_block(
        program,
        program.get_proc_body(procedure.id()),
        &mut value_stack,
        interner,
        source_store,
    )?;

    Ok(value_stack)
}
