use std::io::Write;

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
                let (b, a) = stack.pop().zip(stack.last_mut()).unwrap();
                *a += b;
            }
            OpCode::Subtract => {
                let (b, a) = stack.pop().zip(stack.last_mut()).unwrap();
                *a -= b;
            }

            OpCode::BitOr => {
                let (b, a) = stack.pop().zip(stack.last_mut()).unwrap();
                *a |= b;
            }
            OpCode::BitAnd => {
                let (b, a) = stack.pop().zip(stack.last_mut()).unwrap();
                *a &= b;
            }
            OpCode::ShiftLeft => {
                let (b, a) = stack.pop().zip(stack.last_mut()).unwrap();
                *a <<= b;
            }
            OpCode::ShiftRight => {
                let (b, a) = stack.pop().zip(stack.last_mut()).unwrap();
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
            OpCode::Less => {
                let [b, a] = stack.popn().unwrap();
                stack.push((a < b) as u64);
            }
            OpCode::Equal => {
                let [a, b] = stack.popn().unwrap();
                stack.push((a == b) as u64);
            }

            OpCode::Dump => {
                let val = stack.pop().unwrap();
                println!("{}", val);
            }
            OpCode::Dup => {
                let a = stack.last().copied().unwrap();
                stack.push(a);
            }
            OpCode::DupPair => {
                if let [.., _, _] = &*stack {
                    stack.extend_from_within(stack.len() - 2..);
                }
            }

            OpCode::Over => {
                if let [.., _, _] = &*stack {
                    stack.extend_from_within(stack.len() - 2..stack.len() - 1);
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
            OpCode::Store => {
                let [value, address] = stack.popn().unwrap();

                let dest = memory
                    .get_mut(address as usize)
                    .ok_or_else(|| generate_error("invalid memory address", op.location))?;
                *dest = value as u8;
            }
            OpCode::SysCall(3) => {
                let [syscall_id, arg1, arg2, arg3] = stack.popn().unwrap();
                make_syscall3(syscall_id, arg1, arg2, arg3, &mut memory, op)?;
            }
            OpCode::SysCall(_) => {}
            OpCode::End { .. } => panic!("ICE: Encountered OpCode::End"),
            OpCode::Ident(_) => panic!("ICE: Encountered OpCode::Ident"),
        }

        ip += 1;
    }

    Ok(())
}
