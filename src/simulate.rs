use std::{convert::TryInto, io::Write};

use codespan_reporting::diagnostic::Diagnostic;

use crate::{
    generate_error,
    interners::Interners,
    opcode::{Op, OpCode},
    popn::PopN,
    source_file::FileId,
    MEMORY_CAPACITY,
};

fn make_syscall3(
    id: u64,
    arg1: u64,
    arg2: u64,
    arg3: u64,
    memory: &mut [u8],
    stack: &mut Vec<u64>,
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

            stack.push(arg3);
        }
        _ => return Err(generate_error("unsupported syscall ID", op.location)),
    }

    Ok(())
}

fn make_syscall1(id: u64, arg1: u64, _: &mut [u8], op: Op) -> Result<(), Diagnostic<FileId>> {
    match id {
        // Exit
        60 => std::process::exit(arg1 as _),

        _ => Err(generate_error("unsupported syscall ID", op.location)),
    }
}

fn allocate_string_literals(interner: &Interners, memory: &mut Vec<u8>) -> Vec<u64> {
    let mut indices = Vec::new();

    for (id, literal) in interner.iter_literals() {
        let idx = id.into_inner().get() as usize;
        let new_len = indices.len().max(idx + 1);
        indices.resize(new_len, 0);
        indices[idx] = memory.len() as u64;

        memory.extend_from_slice(literal.as_bytes());
    }

    indices
}

pub(crate) fn simulate_program(
    program: &[Op],
    interner: &Interners,
) -> Result<(), Diagnostic<FileId>> {
    let mut ip = 0;
    let mut stack = Vec::new();

    let mut memory: Vec<u8> = Vec::new();
    let literal_addresses = allocate_string_literals(interner, &mut memory);
    let mem_base = memory.len() as u64;

    let new_memory_len = memory.len() + MEMORY_CAPACITY;
    memory.resize(new_memory_len, 0);

    while let Some(&op) = program.get(ip) {
        match op.code {
            OpCode::Add => {
                let ([b], a) = stack.popn_last_mut().unwrap();
                *a += b;
            }
            OpCode::Subtract => {
                let ([b], a) = stack.popn_last_mut().unwrap();
                *a -= b;
            }
            OpCode::Multiply => {
                let ([b], a) = stack.popn_last_mut().unwrap();
                *a *= b;
            }
            OpCode::DivMod => {
                let [b, a] = stack.popn().unwrap();
                let (rem, quot) = (a % b, a / b);
                stack.push(quot);
                stack.push(rem);
            }

            OpCode::BitOr => {
                let ([b], a) = stack.popn_last_mut().unwrap();
                *a |= b;
            }
            OpCode::BitAnd => {
                let ([b], a) = stack.popn_last_mut().unwrap();
                *a &= b;
            }
            OpCode::ShiftLeft => {
                let ([b], a) = stack.popn_last_mut().unwrap();
                *a <<= b;
            }
            OpCode::ShiftRight => {
                let ([b], a) = stack.popn_last_mut().unwrap();
                *a >>= b;
            }

            OpCode::PushInt(val) => stack.push(val),
            OpCode::PushStr(id) => {
                let literal = interner.resolve_literal(id);
                stack.push(literal.len() as u64);
                stack.push(literal_addresses[id.into_inner().get() as usize]);
            }
            OpCode::Drop => {
                stack.pop().unwrap();
            }

            OpCode::While { .. } => {}
            OpCode::Do { end_ip, .. } => {
                let a = stack.pop().unwrap();

                if a == 0 {
                    ip = end_ip + 1;
                    continue;
                }
            }
            OpCode::EndWhile { condition_ip, .. } => {
                ip = condition_ip;
            }
            OpCode::If { end_ip, .. } => {
                let a = stack.pop().unwrap();

                if a == 0 {
                    ip = end_ip + 1;
                    continue;
                }
            }
            OpCode::Else { end_ip, .. } => {
                ip = end_ip;
            }
            OpCode::EndIf { .. } => {}

            OpCode::Greater => {
                let [b, a] = stack.popn().unwrap();
                stack.push((a > b) as u64);
            }
            OpCode::GreaterEqual => {
                let [b, a] = stack.popn().unwrap();
                stack.push((a >= b) as u64);
            }
            OpCode::Less => {
                let [b, a] = stack.popn().unwrap();
                stack.push((a < b) as u64);
            }
            OpCode::LessEqual => {
                let [b, a] = stack.popn().unwrap();
                stack.push((a <= b) as u64);
            }
            OpCode::Equal => {
                let [a, b] = stack.popn().unwrap();
                stack.push((a == b) as u64);
            }
            OpCode::NotEq => {
                let [a, b] = stack.popn().unwrap();
                stack.push((a != b) as u64);
            }

            OpCode::Print => {
                let val = stack.pop().unwrap();
                println!("{}", val);
            }
            OpCode::Dup { depth } => {
                let a = stack[stack.len() - 1 - depth];
                stack.push(a);
            }
            OpCode::DupPair => {
                if let [.., _, _] = &*stack {
                    stack.extend_from_within(stack.len() - 2..);
                }
            }

            OpCode::Swap => {
                if let [.., a, b] = &mut *stack {
                    std::mem::swap(a, b);
                }
            }

            OpCode::Mem { offset } => stack.push(mem_base + offset as u64),
            OpCode::Load => {
                let address = stack.pop().unwrap();

                let value = *memory
                    .get(address as usize)
                    .ok_or_else(|| generate_error("invalid memory address", op.location))?;
                stack.push(value as u64);
            }
            OpCode::Load64 => {
                let address = stack.pop().unwrap() as usize;
                let value_bytes = memory
                    .get(address..address + 8)
                    .ok_or_else(|| generate_error("invalid memory address", op.location))?;

                let value = u64::from_le_bytes(value_bytes.try_into().unwrap());
                stack.push(value);
            }
            OpCode::Store => {
                let [value, address] = stack.popn().unwrap();

                let dest = memory
                    .get_mut(address as usize)
                    .ok_or_else(|| generate_error("invalid memory address", op.location))?;
                *dest = value as u8;
            }
            OpCode::Store64 => {
                let [value, address] = stack.popn().unwrap();
                let address = address as usize;
                let value_bytes = value.to_le_bytes();
                let dst_bytes = memory
                    .get_mut(address..address + 8)
                    .ok_or_else(|| generate_error("invalid memory address", op.location))?;
                dst_bytes.copy_from_slice(&value_bytes);
            }

            OpCode::SysCall(3) => {
                let [syscall_id, arg1, arg2, arg3] = stack.popn().unwrap();
                make_syscall3(syscall_id, arg1, arg2, arg3, &mut memory, &mut stack, op)?;
            }
            OpCode::SysCall(1) => {
                let [syscall_id, arg1] = stack.popn().unwrap();
                make_syscall1(syscall_id, arg1, &mut memory, op)?;
            }
            OpCode::SysCall(_) => {
                return Err(generate_error("unsupported syscall", op.location));
            }
            OpCode::End { .. } => panic!("ICE: Encountered OpCode::End"),
            OpCode::Ident(_) => panic!("ICE: Encountered OpCode::Ident"),
            OpCode::Include(_) => panic!("ICE: Encountered OpCode::Include"),
        }

        ip += 1;
    }

    Ok(())
}
