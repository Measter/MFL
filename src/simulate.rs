use crate::opcode::{Op, OpCode};

pub(crate) fn simulate_program(program: &[Op]) {
    let mut ip = 0;
    let mut stack = Vec::new();

    while let Some(&op) = program.get(ip) {
        match op.code {
            OpCode::Add => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.last_mut())
                    .expect("Add requires 2 operands");
                *a += b;
            }
            OpCode::Subtract => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.last_mut())
                    .expect("Minus expects 2 operands");
                *a -= b;
            }

            OpCode::Push(val) => stack.push(val),

            OpCode::While { .. } => {}
            OpCode::Do { end_ip, .. } => {
                let a = stack.pop().expect("Do expects an operand");

                if a == 0 {
                    ip = end_ip + 1;
                    continue;
                }
            }
            OpCode::EndWhile { condition_ip, .. } => {
                ip = condition_ip;
            }
            OpCode::If { end_ip, had_else } => {
                let a = stack.pop().expect("If expects an operand");

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
                    .expect("Greater expects 2 operands");
                stack.push((a > b) as u64);
            }
            OpCode::Less => {
                let (b, a) = stack
                    .pop()
                    .zip(stack.pop())
                    .expect("Less expects 2 operands");
                stack.push((a < b) as u64);
            }
            OpCode::Equal => {
                let (a, b) = stack
                    .pop()
                    .zip(stack.pop())
                    .expect("Equal expects 2 operands");
                stack.push((a == b) as u64);
            }

            OpCode::Dump => {
                let val = stack.pop().expect("Dump requires an operand");
                println!("{}", val);
            }
            OpCode::Dup => {
                let a = stack.last().copied().expect("Dup requires an operand");
                stack.push(a);
            }
        }

        ip += 1;
    }
}
