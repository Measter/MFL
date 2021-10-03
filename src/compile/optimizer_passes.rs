use std::io::Write;

use crate::opcode::{Op, OpCode};

use super::compile_op;

type OptimizerFunction = fn(&[Op]) -> Option<(Vec<u8>, &[Op], &[Op])>;

pub(super) const PASSES: &[OptimizerFunction] = &[
    push_arithmetic,
    push_compare,
    mem_plus,
    mem_push_store,
    mem_load,
    pass_through,
];

/// Optimises adding Mem to whatever's on the stack.
fn mem_plus(ops: &[Op]) -> Option<(Vec<u8>, &[Op], &[Op])> {
    let mem = match ops {
        [mem, op, ..] if mem.code.is_mem() && op.code.is_add() => mem,
        _ => return None,
    };

    let mem_val = mem.code.unwrap_mem();
    let mut asm = Vec::new();

    if mem_val == 0 {
        writeln!(&mut asm, "    add QWORD [rsp], __memory").unwrap();
    } else {
        writeln!(&mut asm, "    pop rax").unwrap();
        writeln!(&mut asm, "    lea rax, [rax + __memory + {}]", mem_val).unwrap();
        writeln!(&mut asm, "    push rax").unwrap();
    }

    let (compiled, remaining) = ops.split_at(2);
    Some((asm, compiled, remaining))
}

/// Optimize a Push-Compare
fn push_compare(ops: &[Op]) -> Option<(Vec<u8>, &[Op], &[Op])> {
    let (push, op) = match ops {
        [push, op, ..] if push.code.is_push() && op.code.is_compare() => (push, op),
        _ => return None,
    };

    let push_val = push.code.unwrap_push();
    let mut asm = Vec::new();
    let op = op.code.compile_compare_op();

    writeln!(&mut asm, "    pop rax").unwrap();
    if push_val > u32::MAX as u64 {
        writeln!(&mut asm, "    mov rbx, {}", push_val).unwrap();
        writeln!(&mut asm, "    cmp rax, rbx").unwrap();
    } else {
        writeln!(&mut asm, "    cmp rax, {}", push_val).unwrap();
    }
    writeln!(&mut asm, "    {} r15b", op).unwrap();
    writeln!(&mut asm, "    push r15").unwrap();

    let (compiled, remaining) = ops.split_at(2);
    Some((asm, compiled, remaining))
}

/// Optimize a Push-ArithBinOp
fn push_arithmetic(ops: &[Op]) -> Option<(Vec<u8>, &[Op], &[Op])> {
    let (push, op) = match ops {
        [push, op, ..] if push.code.is_push() && op.code.is_arithmetic() => (push, op),
        _ => return None,
    };

    let mut push_val = push.code.unwrap_push();
    if matches!(op.code, OpCode::ShiftLeft | OpCode::ShiftRight) {
        push_val &= 0xFF;
    }

    let mut asm = Vec::new();
    let (op, _) = op.code.compile_arithmetic_op("rcx", "cl");

    if push_val <= u32::MAX as u64 {
        writeln!(&mut asm, "    {} QWORD [rsp], {}", op, push_val).unwrap();
    } else {
        writeln!(&mut asm, "    mov rax, {}", push_val).unwrap();
        writeln!(&mut asm, "    {} QWORD [rsp], rax", op).unwrap();
    }

    let (compiled, remaining) = ops.split_at(2);
    Some((asm, compiled, remaining))
}

/// Optimises the Mem-Push-Store sequence.
fn mem_push_store(ops: &[Op]) -> Option<(Vec<u8>, &[Op], &[Op])> {
    let (mem, push) = match ops {
        [mem, push, store, ..]
            if mem.code.is_mem() && push.code.is_push() && store.code.is_store() =>
        {
            (mem, push)
        }
        _ => return None,
    };

    let mem_val = mem.code.unwrap_mem();
    let push_val = push.code.unwrap_push() & 0xFF;
    let mut asm = Vec::new();

    writeln!(
        &mut asm,
        "    mov BYTE [__memory + {}], {}",
        mem_val, push_val
    )
    .unwrap();

    let (compiled, remaining) = ops.split_at(3);
    Some((asm, compiled, remaining))
}

/// Optimises the Mem-Load sequence.
fn mem_load(ops: &[Op]) -> Option<(Vec<u8>, &[Op], &[Op])> {
    let mem = match ops {
        [mem, load, ..] if mem.code.is_mem() && load.code.is_load() => mem,
        _ => return None,
    };

    let mem_val = mem.code.unwrap_mem();
    let mut asm = Vec::new();

    writeln!(&mut asm, "    mov r15b, BYTE [__memory + {}]", mem_val,).unwrap();
    writeln!(&mut asm, "    push r15",).unwrap();

    let (compiled, remaining) = ops.split_at(2);
    Some((asm, compiled, remaining))
}

/// Just compiles the first operation. Does no optimization at all.
fn pass_through(ops: &[Op]) -> Option<(Vec<u8>, &[Op], &[Op])> {
    let mut asm = Vec::new();
    let (compiled, remaining) = ops.split_at(1);
    compile_op(&mut asm, compiled[0]).unwrap();
    Some((asm, compiled, remaining))
}
