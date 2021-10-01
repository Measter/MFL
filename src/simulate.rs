use std::io::Write;

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::{
    opcode::{Op, OpCode},
    source_file::{FileId, SourceLocation},
    MEMORY_CAPACITY,
};

fn generate_error(msg: &str, location: SourceLocation) -> Diagnostic<FileId> {
    Diagnostic::error()
        .with_message(msg)
        .with_labels(vec![Label::primary(location.file_id, location.range())])
}

fn make_syscall3(
    id: u64,
    arg1: u64,
    arg2: u64,
    arg3: u64,
    memory: &mut [u8],
    op: Op,
) -> Result<(), Diagnostic<FileId>> {
    match id {
        // Write
        1 => {
            let start = arg2 as usize;
            let end = start + arg3 as usize;
            let buffer = memory
                .get(start..end)
                .ok_or_else(|| generate_error("invalid memory range", op.location))?;

            // Not my problem if this isn't valid output data.
            let _ = match arg1 {
                1 => std::io::stdout().write_all(buffer),
                2 => std::io::stderr().write_all(buffer),
                _ => return Err(generate_error("unsupported file descriptor", op.location)),
            };
        }
        _ => return Err(generate_error("unsupported syscall ID", op.location)),
    }

    Ok(())
}

pub(crate) fn simulate_program(program: &[Op]) -> Result<(), Diagnostic<FileId>> {
    let mut ip = 0;
    let mut stack = Vec::new();
    let mut memory: Vec<u8> = vec![0; MEMORY_CAPACITY];

    while let Some(&op) = program.get(ip) {
        match op.code {
            OpCode::Add => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.last_mut())
                    .ok_or_else(|| generate_error("`+` expects 2 operands", op.location))?;
                *a += b;
            }
            OpCode::Subtract => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.last_mut())
                    .ok_or_else(|| generate_error("`-` expects 2 operands", op.location))?;
                *a -= b;
            }

            OpCode::BitOr => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.last_mut())
                    .ok_or_else(|| generate_error("`bor` expects 2 operands", op.location))?;
                *a |= b;
            }
            OpCode::BitAnd => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.last_mut())
                    .ok_or_else(|| generate_error("`band` expects 2 operands", op.location))?;
                *a &= b;
            }
            OpCode::ShiftLeft => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.last_mut())
                    .ok_or_else(|| generate_error("`shl` expects 2 operands", op.location))?;
                *a <<= b;
            }
            OpCode::ShiftRight => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.last_mut())
                    .ok_or_else(|| generate_error("`shr` expects 2 operands", op.location))?;
                *a >>= b;
            }

            OpCode::Push(val) => stack.push(val),
            OpCode::Drop => {
                stack
                    .pop()
                    .ok_or_else(|| generate_error("`drop` expects an operand", op.location))?;
            }

            OpCode::While { .. } => {}
            OpCode::Do { end_ip, .. } => {
                let a = stack
                    .pop()
                    .ok_or_else(|| generate_error("`while-do` expects a condition", op.location))?;

                if a == 0 {
                    ip = end_ip + 1;
                    continue;
                }
            }
            OpCode::EndWhile { condition_ip, .. } => {
                ip = condition_ip;
            }
            OpCode::If { end_ip, had_else } => {
                let a = stack
                    .pop()
                    .ok_or_else(|| generate_error("`if` expects a condition", op.location))?;

                if a == 0 {
                    ip = end_ip + had_else as usize;
                    continue;
                }
            }
            OpCode::Else { end_ip, .. } => {
                ip = end_ip;
            }
            OpCode::EndIf { .. } => {}

            OpCode::Greater => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.pop())
                    .ok_or_else(|| generate_error("`>` expects 2 operands", op.location))?;
                stack.push((a > b) as u64);
            }
            OpCode::Less => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.pop())
                    .ok_or_else(|| generate_error("`<` expects 2 operands", op.location))?;
                stack.push((a < b) as u64);
            }
            OpCode::Equal => {
                let (a, b) = stack
                    .pop()
                    .zip(stack.pop())
                    .ok_or_else(|| generate_error("`=` expects 2 operands", op.location))?;
                stack.push((a == b) as u64);
            }

            OpCode::Dump => {
                let val = stack
                    .pop()
                    .ok_or_else(|| generate_error("`dump` requires an operand", op.location))?;
                println!("{}", val);
            }
            OpCode::Dup => {
                let a = stack
                    .last()
                    .copied()
                    .ok_or_else(|| generate_error("`dup` requires an operand", op.location))?;
                stack.push(a);
            }
            OpCode::DupPair => match &*stack {
                [.., a, b] => {
                    let a = *a;
                    let b = *b;
                    stack.push(a);
                    stack.push(b);
                }
                _ => return Err(generate_error("`2dup` requires 2 operands", op.location)),
            },
            OpCode::Over => match &*stack {
                [.., a, _] => {
                    let a = *a;
                    stack.push(a);
                }
                _ => return Err(generate_error("`over` requires 2 operands", op.location)),
            },
            OpCode::Swap => match &mut *stack {
                [.., a, b] => std::mem::swap(a, b),
                _ => return Err(generate_error("`swap` requires 2 operands", op.location)),
            },

            OpCode::Mem => stack.push(0),
            OpCode::Load => {
                let address = stack
                    .pop()
                    .ok_or_else(|| generate_error("`,` expects an operand", op.location))?;

                let value = *memory
                    .get(address as usize)
                    .ok_or_else(|| generate_error("invalid memory address", op.location))?;
                stack.push(value as u64);
            }
            OpCode::Store => {
                let (value, address) = stack
                    .pop()
                    .zip(stack.pop())
                    .ok_or_else(|| generate_error("'.' expects 2 operands", op.location))?;

                let dest = memory
                    .get_mut(address as usize)
                    .ok_or_else(|| generate_error("invalid memory address", op.location))?;
                *dest = value as u8;
            }
            OpCode::SysCall(3) => {
                let (((syscall_id, arg1), arg2), arg3) = stack
                    .pop()
                    .zip(stack.pop())
                    .zip(stack.pop())
                    .zip(stack.pop())
                    .ok_or_else(|| generate_error("`syscall3` expects 4 operands", op.location))?;
                make_syscall3(syscall_id, arg1, arg2, arg3, &mut memory, op)?;
            }
            OpCode::SysCall(0..=6) => {}
            OpCode::SysCall(_) => {
                return Err(generate_error(
                    "invalid number of syscall args",
                    op.location,
                ));
            }
        }

        ip += 1;
    }

    Ok(())
}
