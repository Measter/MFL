use std::{io::Write, iter::repeat, ops::Range};

use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::PopN,
    opcode::{Op, OpCode},
    program::Procedure,
    source_file::SourceStorage,
    Program, Width,
};

impl Width {
    fn addr_range(self, start: usize) -> Range<usize> {
        match self {
            Width::Byte => start..start + 1,
            Width::Word => start..start + 2,
            Width::Dword => start..start + 4,
            Width::Qword => start..start + 8,
        }
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

    diagnostics::emit(op.token.location, msg, labels, None, source_store);
}

fn make_syscall3(
    id: u64,
    arg1: u64,
    arg2: u64,
    arg3: u64,
    memory: &mut [u8],
    stack: &mut Vec<u64>,
    op: &Op,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    match id {
        // Write
        1 => {
            let start = arg2 as usize;
            let end = start + arg3 as usize;
            let buffer = memory.get(start..end).ok_or_else(|| {
                generate_error(
                    format!("invalid memory range {:?}", start..end),
                    op,
                    source_store,
                )
            })?;

            // Not my problem if this isn't valid output data.
            let _ = match arg1 {
                1 => std::io::stdout().write_all(buffer),
                2 => std::io::stderr().write_all(buffer),
                _ => {
                    generate_error("unsupported file descriptor", op, source_store);
                    return Err(());
                }
            };

            stack.push(arg3);
        }
        _ => {
            generate_error("unsupported syscall ID", op, source_store);
            return Err(());
        }
    }

    Ok(())
}

fn make_syscall1(
    id: u64,
    arg1: u64,
    _: &mut [u8],
    op: &Op,
    source_store: &SourceStorage,
) -> Result<(), ()> {
    match id {
        // Exit
        60 => std::process::exit(arg1 as _),

        _ => {
            generate_error("unsupported syscall ID", op, source_store);
            Err(())
        }
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

fn allocate_program_args(memory: &mut Vec<u8>, args: &[String]) -> (u64, u64) {
    let argc = memory.len();
    // Space for ARGC
    memory.extend_from_slice(&args.len().to_le_bytes());
    // Allocate space for the ARGV array. +1 for the nullptr marker.
    let argv = memory.len();
    memory.extend(repeat(0).take((args.len() + 1) * 8));

    for (mut idx, arg) in args.iter().enumerate() {
        let addr = memory.len();
        memory.extend_from_slice(arg.as_bytes());
        memory.push(0); // Gotta be null-terminated.
        idx *= 8;
        let argv_addr = argv + idx;
        memory[argv_addr..argv_addr + 8].copy_from_slice(&addr.to_le_bytes());
    }

    (argc as u64, argv as u64)
}

pub(crate) fn simulate_execute_program(
    program: &Program,
    procedure: &Procedure,
    interner: &Interners,
    program_args: &[String],
    source_store: &SourceStorage,
) -> Result<Vec<u64>, ()> {
    let mut ip = 0;
    let mut value_stack: Vec<u64> = Vec::new();
    let mut call_stack: Vec<(&Procedure, usize)> = Vec::new();

    let global_proc_data = program
        .get_proc(program.top_level_proc_id())
        .kind()
        .get_proc_data();

    let mut current_procedure = procedure;

    let mut memory: Vec<u8> = vec![0; global_proc_data.total_alloc_size];
    let literal_addresses = allocate_string_literals(interner, &mut memory);
    let (_, argv_ptr) = allocate_program_args(&mut memory, program_args);
    let mut local_memory_base = memory.len();

    while let Some(op) = current_procedure.body().get(ip) {
        // eprintln!("{:?}", op.code);
        // Note: We should still check main_proc for const, as it may call non-const procs.
        if (current_procedure.kind().is_const() || current_procedure.kind().is_memory())
            && !op.code.is_const()
        {
            generate_error(
                "Operation not supported during const evaluation",
                op,
                source_store,
            );
            return Err(());
        }

        match op.code {
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

            OpCode::PushBool(val) => value_stack.push(val as _),
            OpCode::PushInt(val) => value_stack.push(val),
            OpCode::PushStr { id, is_c_str } => {
                let literal = interner.resolve_literal(id);
                if !is_c_str {
                    // Strings are null-terminated during parsing, but the Porth-style strings shouldn't
                    // include that character.
                    value_stack.push(literal.len() as u64 - 1);
                }
                value_stack.push(literal_addresses[id.into_inner().get() as usize]);
            }
            OpCode::Drop => {
                value_stack.pop().unwrap();
            }

            OpCode::While { .. } => {}
            OpCode::DoWhile { end_ip, .. } => {
                let a = value_stack.pop().unwrap();

                if a == 0 {
                    ip = end_ip + 1;
                    continue;
                }
            }
            OpCode::EndWhile { condition_ip, .. } => {
                ip = condition_ip;
            }
            OpCode::If => {}
            OpCode::DoIf { end_ip, .. } => {
                let a = value_stack.pop().unwrap();

                if a == 0 {
                    ip = end_ip + 1;
                    continue;
                }
            }
            OpCode::Elif { end_ip, .. } | OpCode::Else { end_ip, .. } => ip = end_ip,
            OpCode::EndIf { .. } => {}

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

            OpCode::Print => {
                let val = value_stack.pop().unwrap();
                println!("{}", val);
            }
            OpCode::Dup { depth } => {
                let a = value_stack[value_stack.len() - 1 - depth];
                value_stack.push(a);
            }
            OpCode::DupPair => {
                if let [.., _, _] = &*value_stack {
                    value_stack.extend_from_within(value_stack.len() - 2..);
                }
            }
            OpCode::Rot => {
                let start = value_stack.len() - 3;
                value_stack[start..].rotate_left(1);
            }
            OpCode::Swap => {
                if let [.., a, b] = &mut *value_stack {
                    std::mem::swap(a, b);
                }
            }

            OpCode::Memory {
                name,
                offset,
                global: false,
            } => {
                let proc_data = current_procedure.kind().get_proc_data();
                let base = local_memory_base + proc_data.alloc_size_and_offsets[&name].offset;
                value_stack.push((base + offset) as u64)
            }
            OpCode::Memory {
                name,
                offset,
                global: true,
            } => {
                let base = global_proc_data.alloc_size_and_offsets[&name].offset;
                value_stack.push((base + offset) as u64)
            }
            OpCode::Load(width) => {
                let address = value_stack.pop().unwrap() as usize;

                let bytes = memory
                    .get(width.addr_range(address))
                    .ok_or_else(|| generate_error("invalid memory address", op, source_store))?;

                let value = match width {
                    Width::Byte => bytes[0] as u64,
                    Width::Word => u16::from_le_bytes(bytes.try_into().unwrap()) as u64,
                    Width::Dword => u32::from_le_bytes(bytes.try_into().unwrap()) as u64,
                    Width::Qword => u64::from_le_bytes(bytes.try_into().unwrap()) as u64,
                };
                value_stack.push(value);
            }
            OpCode::Store(width) => {
                let [value, address] = value_stack.popn().unwrap();
                let dest = memory
                    .get_mut(width.addr_range(address as usize))
                    .ok_or_else(|| {
                        generate_error(
                            format!("invalid memory address {:?}", address),
                            op,
                            source_store,
                        )
                    })?;
                match width {
                    Width::Byte => dest[0] = value as u8,
                    Width::Word => dest.copy_from_slice(&u16::to_le_bytes(value as _)),
                    Width::Dword => dest.copy_from_slice(&u32::to_le_bytes(value as _)),
                    Width::Qword => dest.copy_from_slice(&u64::to_le_bytes(value)),
                }
            }

            OpCode::ArgC => value_stack.push(program_args.len() as _),
            OpCode::ArgV => value_stack.push(argv_ptr),

            OpCode::CastBool | OpCode::CastInt | OpCode::CastPtr => {}

            // These are no-ops for the simulator, only there to help the compiler.
            OpCode::Epilogue | OpCode::Prologue => {}
            OpCode::CallProc(id) => {
                let return_address = ip + 1; // The instruction after.
                call_stack.push((current_procedure, return_address));
                current_procedure = program.get_proc(id);
                ip = 0;

                local_memory_base = memory.len();
                let proc_data = current_procedure.kind().get_proc_data();
                memory.resize(memory.len() + proc_data.total_alloc_size, 0);

                continue;
            }
            OpCode::Return => match call_stack.pop() {
                None => break,
                Some((proc, return_ip)) => {
                    let proc_data = current_procedure.kind().get_proc_data();
                    local_memory_base -= proc_data.total_alloc_size;
                    memory.truncate(memory.len() - proc_data.total_alloc_size);

                    current_procedure = proc;
                    ip = return_ip;

                    continue;
                }
            },

            OpCode::SysCall(3) => {
                let [arg3, arg2, arg1, syscall_id] = value_stack.popn().unwrap();
                make_syscall3(
                    syscall_id,
                    arg1,
                    arg2,
                    arg3,
                    &mut memory,
                    &mut value_stack,
                    op,
                    source_store,
                )?;
            }
            OpCode::SysCall(1) => {
                let [arg1, syscall_id] = value_stack.popn().unwrap();
                make_syscall1(syscall_id, arg1, &mut memory, op, source_store)?;
            }
            OpCode::SysCall(_) => {
                generate_error("unsupported syscall", op, source_store);
                return Err(());
            }
            OpCode::Do | OpCode::End | OpCode::Ident(_) | OpCode::Include(_) => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }

        ip += 1;
    }

    Ok(value_stack)
}
