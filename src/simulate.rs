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

            OpCode::Push(val) => stack.push(val),

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
        }

        ip += 1;
    }

    Ok(())
}
