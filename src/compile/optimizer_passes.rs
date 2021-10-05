use std::io::Write;

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
};

use super::compile_op;

type OptimizerFunction = for<'a> fn(&Interners, &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])>;

pub(super) const PASSES: &[OptimizerFunction] = &[
    push_divmod,
    push_arithmetic,
    dup_pushint_compare_doif,
    dup_push_compare,
    push_compare,
    mem_plus,
    mem_push_store,
    mem_load,
    pass_through,
];

// Optimize the common Dup-PushInt-Compare-Do/If sequence
fn dup_pushint_compare_doif<'a>(
    _: &Interners,
    ops: &'a [Op],
) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let (dup, push, op, doif) = match ops {
        [dup, push, op, doif, ..]
            if dup.code.is_dup()
                && push.code.is_push_int()
                && op.code.is_compare()
                && (doif.code.is_do() || doif.code.is_if()) =>
        {
            (dup, push, op, doif)
        }
        _ => return None,
    };

    let push_val = push.code.unwrap_push_int();
    let dup_depth = dup.code.unwrap_dup();
    let mut asm = Vec::new();
    let end_ip = match doif.code {
        OpCode::Do { end_ip, .. } => end_ip,
        OpCode::If { end_ip } => end_ip,
        _ => unreachable!(),
    };
    let op = op.code.compile_compare_op_inverse_suffix();

    if push_val <= u32::MAX as u64 {
        writeln!(
            &mut asm,
            "    cmp QWORD [rsp + 8*{}], {}",
            dup_depth, push_val
        )
        .unwrap();
    } else {
        writeln!(&mut asm, "    mov rbx, {}", push_val).unwrap();
        writeln!(&mut asm, "    cmp QWORD [rsp + 8*{}], rbx", dup_depth).unwrap();
    }
    writeln!(&mut asm, "    j{} .LBL{}", op, end_ip).unwrap();

    let (compiled, remaining) = ops.split_at(4);
    Some((asm, compiled, remaining))
}

/// Optimises PushInt-DivMod
fn push_divmod<'a>(_: &Interners, ops: &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let a = match ops {
        [a, op, ..] if a.code.is_push_int() && op.code.is_div_mod() => a,
        _ => return None,
    };

    let mut asm = Vec::new();
    writeln!(&mut asm, "    mov rbx, {}", a.code.unwrap_push_int()).unwrap();
    writeln!(&mut asm, "    pop rax").unwrap();
    writeln!(&mut asm, "    xor rdx, rdx").unwrap();
    writeln!(&mut asm, "    div rbx").unwrap();
    writeln!(&mut asm, "    push rax").unwrap();
    writeln!(&mut asm, "    push rdx").unwrap();

    let (compiled, remaining) = ops.split_at(2);
    Some((asm, compiled, remaining))
}

/// Optimises adding Mem to whatever's on the stack.
fn mem_plus<'a>(_: &Interners, ops: &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let mem = match ops {
        [mem, op, ..] if mem.code.is_mem() && op.code.is_add() => mem,
        _ => return None,
    };

    let mem_val = mem.code.unwrap_mem();
    let mut asm = Vec::new();

    if mem_val <= u32::MAX as usize {
        writeln!(&mut asm, "    add QWORD [rsp], __memory + {}", mem_val).unwrap();
    } else {
        writeln!(&mut asm, "    mov rax, __memory + {}", mem_val).unwrap();
        writeln!(&mut asm, "    add QWORD [rsp], rax").unwrap();
    }

    let (compiled, remaining) = ops.split_at(2);
    Some((asm, compiled, remaining))
}

/// Optimize a Dup-Push-Compare
fn dup_push_compare<'a>(_: &Interners, ops: &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let (dup, push, op) = match ops {
        [dup, push, op, ..]
            if dup.code.is_dup() && push.code.is_push_int() && op.code.is_compare() =>
        {
            (dup, push, op)
        }
        _ => return None,
    };

    let push_val = push.code.unwrap_push_int();
    let dup_depth = dup.code.unwrap_dup();
    let mut asm = Vec::new();
    let op = op.code.compile_compare_op_suffix();

    if push_val <= u32::MAX as u64 {
        writeln!(
            &mut asm,
            "    cmp QWORD [rsp + 8*{}], {}",
            dup_depth, push_val
        )
        .unwrap();
    } else {
        writeln!(&mut asm, "    mov rbx, {}", push_val).unwrap();
        writeln!(&mut asm, "    cmp QWORD [rsp + 8*{}], rbx", dup_depth).unwrap();
    }
    writeln!(&mut asm, "    set{} r15b", op).unwrap();
    writeln!(&mut asm, "    push r15").unwrap();

    let (compiled, remaining) = ops.split_at(3);
    Some((asm, compiled, remaining))
}

/// Optimize a Push-Compare
fn push_compare<'a>(_: &Interners, ops: &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let (push, op) = match ops {
        [push, op, ..] if push.code.is_push_int() && op.code.is_compare() => (push, op),
        _ => return None,
    };

    let push_val = push.code.unwrap_push_int();
    let mut asm = Vec::new();
    let op = op.code.compile_compare_op_suffix();

    writeln!(&mut asm, "    pop rax").unwrap();
    if push_val <= u32::MAX as u64 {
        writeln!(&mut asm, "    cmp rax, {}", push_val).unwrap();
    } else {
        writeln!(&mut asm, "    mov rbx, {}", push_val).unwrap();
        writeln!(&mut asm, "    cmp rax, rbx").unwrap();
    }
    writeln!(&mut asm, "    set{} r15b", op).unwrap();
    writeln!(&mut asm, "    push r15").unwrap();

    let (compiled, remaining) = ops.split_at(2);
    Some((asm, compiled, remaining))
}

/// Optimize a Push-ArithBinOp
fn push_arithmetic<'a>(_: &Interners, ops: &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let (push, op) = match ops {
        [push, op, ..] if push.code.is_push_int() && op.code.is_compiler_opt_arithmetic() => {
            (push, op)
        }
        _ => return None,
    };

    let mut push_val = push.code.unwrap_push_int();
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
fn mem_push_store<'a>(_: &Interners, ops: &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let (mem, push) = match ops {
        [mem, push, store, ..]
            if mem.code.is_mem() && push.code.is_push_int() && store.code.is_store() =>
        {
            (mem, push)
        }
        _ => return None,
    };

    let mem_val = mem.code.unwrap_mem();
    let push_val = push.code.unwrap_push_int() & 0xFF;
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
fn mem_load<'a>(_: &Interners, ops: &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let mem = match ops {
        [mem, load, ..] if mem.code.is_mem() && load.code.is_load() => mem,
        _ => return None,
    };

    let mem_val = mem.code.unwrap_mem();
    let mut asm = Vec::new();

    writeln!(&mut asm, "    mov r15b, BYTE [__memory + {}]", mem_val,).unwrap();
    writeln!(&mut asm, "    push r15").unwrap();

    let (compiled, remaining) = ops.split_at(2);
    Some((asm, compiled, remaining))
}

/// Just compiles the first operation. Does no optimization at all.
pub(super) fn pass_through<'a>(
    interner: &Interners,
    ops: &'a [Op],
) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let mut asm = Vec::new();
    let (compiled, remaining) = ops.split_at(1);
    compile_op(&mut asm, compiled[0], interner).unwrap();
    Some((asm, compiled, remaining))
}
