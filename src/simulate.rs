use std::{io::Write, iter::repeat, ops::Range};

use ariadne::{Color, Label};

use crate::{
    diagnostics,
    interners::Interners,
    n_ops::PopN,
    opcode::{Op, OpCode},
    program::{Procedure, ProcedureKind, Program},
    source_file::SourceStorage,
    Width,
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
    source_store: &SourceStorage,
) -> Result<Vec<u64>, SimulationError> {
    let mut ip = 0;
    let mut value_stack: Vec<u64> = Vec::new();

    while let Some(op) = procedure.body().get(ip) {
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
            // It's a bit weird, given you can't do much with a string, but
            // you could just drop the address that gets pushed leaving the length
            // which can be used in a const context.
            OpCode::PushStr { id, is_c_str } => {
                let literal = interner.resolve_literal(id);
                if !is_c_str {
                    // Strings are null-terminated during parsing, but the Porth-style strings shouldn't
                    // include that character.
                    value_stack.push(literal.len() as u64 - 1);
                }
                // Nullptr is fine, because you can't read/write memory in a const-context anyway.
                value_stack.push(0);
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

            OpCode::CastBool | OpCode::CastInt | OpCode::CastPtr => {}

            // These are no-ops for the simulator, only there to help the compiler.
            OpCode::Epilogue | OpCode::Prologue => {}
            OpCode::Return => break,

            OpCode::ResolvedIdent { proc_id, .. } => {
                let referenced_proc = program.get_proc(proc_id);

                match referenced_proc.kind() {
                    ProcedureKind::Const {
                        const_val: Some(vals),
                    } => {
                        value_stack.extend(vals.iter().map(|(t, v)| *v));
                    }
                    ProcedureKind::Const { .. } => {
                        return Err(SimulationError::UnreadyConst);
                    }
                    _ => {
                        generate_error("non-const cannot be refenced in a const", op, source_store);
                        return Err(SimulationError::UnsupportedOp);
                    }
                }
            }

            OpCode::ArgC
            | OpCode::ArgV
            | OpCode::CallProc(_)
            | OpCode::Load(_)
            | OpCode::Memory { .. }
            | OpCode::Store(_)
            | OpCode::SysCall(_) => {
                generate_error(
                    "operation not supported during const evaluation",
                    op,
                    source_store,
                );
                return Err(SimulationError::UnsupportedOp);
            }
            OpCode::Do | OpCode::End | OpCode::UnresolvedIdent { .. } | OpCode::Include(_) => {
                panic!("ICE: Encountered {:?}", op.code)
            }
        }

        ip += 1;
    }

    Ok(value_stack)
}
