use std::io::Write;

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
};

use super::compile_op;

type OptimizerFunction = for<'a> fn(&Interners, &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])>;

pub(super) const PASSES: &[OptimizerFunction] = &[
    swap_pushint_arithmetic_swap,
    push_divmod_swap_drop,
    push_divmod_drop,
    push_divmod,
    push_arithmetic,
    dup_pushint_compare_doif,
    dup_push_compare,
    push_compare,
    mem_plus,
    mem_push_store,
    mem_load,
    pushint_pushint_syscall3,
    pass_through,
];

/// Optimize PushInt-PushInt-SysCall(3) - Commonly used for writing to stdout
fn pushint_pushint_syscall3<'a>(
    _: &Interners,
    ops: &'a [Op],
) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let (a, b) = match ops {
        [a, b, syscall, ..]
            if a.code.is_push_int()
                && b.code.is_push_int()
                && syscall.code == OpCode::SysCall(3) =>
        {
            (a, b)
        }
        _ => return None,
    };

    let a_val = a.code.unwrap_push_int();
    let b_val = b.code.unwrap_push_int();

    let mut asm = Vec::new();

    writeln!(&mut asm, "    mov rax, {}", b_val).unwrap();
    writeln!(&mut asm, "    mov rdi, {}", a_val).unwrap();
    writeln!(&mut asm, "    pop rsi").unwrap();
    writeln!(&mut asm, "    pop rdx").unwrap();
    writeln!(&mut asm, "    syscall").unwrap();
    writeln!(&mut asm, "    push rax").unwrap();

    let (compiled, remaining) = ops.split_at(3);
    Some((asm, compiled, remaining))
}

/// Optimize a Swap-PushInt-ArithBinOp-Swap sequence
fn swap_pushint_arithmetic_swap<'a>(
    _: &Interners,
    ops: &'a [Op],
) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let (push, op) = match ops {
        [swapa, push, op, swapb, ..]
            if swapa.code.is_swap()
                && push.code.is_push_int()
                && op.code.is_compiler_opt_arithmetic()
                && swapb.code.is_swap() =>
        {
            (push, op)
        }
        _ => return None,
    };

    let mut push_val = push.code.unwrap_push_int();
    if matches!(op.code, OpCode::ShiftLeft | OpCode::ShiftRight) {
        push_val &= 0xFF;
    }

    let mut asm = Vec::new();
    let (op_instr, _) = op.code.compile_arithmetic_op("rcx", "cl");

    if push_val <= u32::MAX as u64 {
        writeln!(&mut asm, "    {} QWORD [rsp+8], {}", op_instr, push_val).unwrap();
    } else {
        writeln!(&mut asm, "    mov r8, {}", push_val).unwrap();
        writeln!(&mut asm, "    {} QWORD [rsp+8], r8", op_instr).unwrap();
    }

    let (compiled, remaining) = ops.split_at(4);
    Some((asm, compiled, remaining))
}

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
        writeln!(&mut asm, "    mov r9, {}", push_val).unwrap();
        writeln!(&mut asm, "    cmp QWORD [rsp + 8*{}], r9", dup_depth).unwrap();
    }
    writeln!(&mut asm, "    j{} .LBL{}", op, end_ip).unwrap();

    let (compiled, remaining) = ops.split_at(4);
    Some((asm, compiled, remaining))
}

/// Optimises PushInt-DivMod-Swap-Drop (mod macro)
fn push_divmod_swap_drop<'a>(
    _: &Interners,
    ops: &'a [Op],
) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let a = match ops {
        [a, div, swap, drop, ..]
            if a.code.is_push_int()
                && div.code.is_div_mod()
                && swap.code.is_swap()
                && drop.code.is_drop() =>
        {
            a
        }
        _ => return None,
    };

    let mut asm = Vec::new();
    writeln!(&mut asm, "    mov r9, {}", a.code.unwrap_push_int()).unwrap();
    writeln!(&mut asm, "    pop rax").unwrap();
    writeln!(&mut asm, "    xor rdx, rdx").unwrap();
    writeln!(&mut asm, "    div r9").unwrap();
    writeln!(&mut asm, "    push rdx").unwrap();

    let (compiled, remaining) = ops.split_at(4);
    Some((asm, compiled, remaining))
}

/// Optimises PushInt-DivMod-Drop (division macro)
fn push_divmod_drop<'a>(_: &Interners, ops: &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let a = match ops {
        [a, div, drop, ..]
            if a.code.is_push_int() && div.code.is_div_mod() && drop.code.is_drop() =>
        {
            a
        }
        _ => return None,
    };

    let mut asm = Vec::new();
    writeln!(&mut asm, "    mov r9, {}", a.code.unwrap_push_int()).unwrap();
    writeln!(&mut asm, "    pop rax").unwrap();
    writeln!(&mut asm, "    xor rdx, rdx").unwrap();
    writeln!(&mut asm, "    div r9").unwrap();
    writeln!(&mut asm, "    push rax").unwrap();

    let (compiled, remaining) = ops.split_at(3);
    Some((asm, compiled, remaining))
}

/// Optimises PushInt-DivMod
fn push_divmod<'a>(_: &Interners, ops: &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let a = match ops {
        [a, op, ..] if a.code.is_push_int() && op.code.is_div_mod() => a,
        _ => return None,
    };

    let mut asm = Vec::new();
    writeln!(&mut asm, "    mov r9, {}", a.code.unwrap_push_int()).unwrap();
    writeln!(&mut asm, "    pop rax").unwrap();
    writeln!(&mut asm, "    xor rdx, rdx").unwrap();
    writeln!(&mut asm, "    div r9").unwrap();
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
        writeln!(&mut asm, "    mov r8, __memory + {}", mem_val).unwrap();
        writeln!(&mut asm, "    add QWORD [rsp], r8").unwrap();
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
        writeln!(&mut asm, "    mov r9, {}", push_val).unwrap();
        writeln!(&mut asm, "    cmp QWORD [rsp + 8*{}], r9", dup_depth).unwrap();
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

    writeln!(&mut asm, "    pop r8").unwrap();
    if push_val <= u32::MAX as u64 {
        writeln!(&mut asm, "    cmp r8, {}", push_val).unwrap();
    } else {
        writeln!(&mut asm, "    mov r9, {}", push_val).unwrap();
        writeln!(&mut asm, "    cmp r8, r9").unwrap();
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
    let (op_instr, _) = op.code.compile_arithmetic_op("rcx", "cl");

    if push_val <= u32::MAX as u64 {
        writeln!(&mut asm, "    {} QWORD [rsp], {}", op_instr, push_val).unwrap();
    } else {
        writeln!(&mut asm, "    mov r8, {}", push_val).unwrap();
        writeln!(&mut asm, "    {} QWORD [rsp], r8", op_instr).unwrap();
    }

    let (compiled, remaining) = ops.split_at(2);
    Some((asm, compiled, remaining))
}

/// Optimises the Mem-Push-Store sequence.
fn mem_push_store<'a>(_: &Interners, ops: &'a [Op]) -> Option<(Vec<u8>, &'a [Op], &'a [Op])> {
    let (mem, push) = match ops {
        [mem, push, store, ..]
            if mem.code.is_mem()
                && push.code.is_push_int()
                && store.code.is_store()
                && !store.code.unwrap_store() =>
        {
            (mem, push)
        }
        [push, mem, store, ..]
            if mem.code.is_mem()
                && push.code.is_push_int()
                && store.code.is_store()
                && store.code.unwrap_store() =>
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
    compile_op(&mut asm, &compiled[0], interner).unwrap();
    Some((asm, compiled, remaining))
}
