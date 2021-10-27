use std::borrow::Cow;

use crate::{
    compile_new::assembly::Register,
    interners::Interners,
    opcode::{Op, OpCode},
};

use super::assembly::{Assembler, InstructionPart};

type OptimizerFunction = for<'a> fn(&[Op], usize, &mut Assembler, &Interners) -> Option<usize>;

pub(super) const PASSES: &[OptimizerFunction] = &[
    push_compare,
    push_shift,
    push_arithmetic,
    mem_push_store,
    mem_load,
    compile_single_instruction,
];

fn dyn_reg(reg_id: usize) -> InstructionPart {
    InstructionPart::DynamicRegister {
        reg_id,
        is_byte: false,
    }
}
fn dyn_byte_reg(reg_id: usize) -> InstructionPart {
    InstructionPart::DynamicRegister {
        reg_id,
        is_byte: true,
    }
}
fn str_lit(lit: impl Into<Cow<'static, str>>) -> InstructionPart {
    InstructionPart::Literal(lit.into())
}

const ARITH_OP_MAX: u64 = u32::MAX as u64;

impl OpCode {
    fn is_compiler_opt_arithmetic(self) -> bool {
        use OpCode::*;
        matches!(self, Add | BitAnd | BitOr | Subtract)
    }

    fn is_compiler_opt_shift(self) -> bool {
        use OpCode::*;
        matches!(self, ShiftLeft | ShiftRight)
    }

    pub fn is_compare(self) -> bool {
        use OpCode::*;
        matches!(
            self,
            Equal | Greater | GreaterEqual | Less | LessEqual | NotEq
        )
    }
}

/// Optimize a Push-Compare
fn push_compare(ops: &[Op], ip: usize, assembler: &mut Assembler, _: &Interners) -> Option<usize> {
    let (push, op) = match ops {
        [push, op, ..]
            if op.code.is_compare() && matches!(push.code, OpCode::PushInt(0..=ARITH_OP_MAX)) =>
        {
            (push, op)
        }
        _ => return None,
    };

    let push_val = push.code.unwrap_push_int();

    assembler.set_op_range(ip, ip + 2);
    let reg = assembler.reg_alloc_dyn_pop();
    let op_suffix = op.code.compile_compare_op_suffix();

    assembler.push_instr([
        str_lit("    cmp "),
        dyn_reg(reg),
        str_lit(format!(", {}", push_val)),
    ]);
    assembler.push_instr([str_lit(format!("    set{} ", op_suffix)), dyn_byte_reg(reg)]);
    assembler.reg_free_dyn_push(reg);

    Some(2)
}

/// Optimize a Push-ShiftOp
fn push_shift(ops: &[Op], ip: usize, assembler: &mut Assembler, _: &Interners) -> Option<usize> {
    let (push, op) = match ops {
        [push, op, ..]
            if op.code.is_compiler_opt_shift() && matches!(push.code, OpCode::PushInt(0..=255)) =>
        {
            (push, op)
        }
        _ => return None,
    };

    let push_val = push.code.unwrap_push_int();

    assembler.set_op_range(ip, ip + 2);
    let reg = assembler.reg_alloc_dyn_pop();

    assembler.push_instr([
        str_lit(op.code.compile_arithmetic_op()),
        dyn_reg(reg),
        str_lit(format!(", {}", push_val)),
    ]);

    assembler.reg_free_dyn_push(reg);

    Some(2)
}

/// Optimize a Push-ArithBinOp
fn push_arithmetic(
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    _: &Interners,
) -> Option<usize> {
    let (push, op) = match ops {
        [push, op, ..]
            if op.code.is_compiler_opt_arithmetic()
                && matches!(push.code, OpCode::PushInt(0..=ARITH_OP_MAX)) =>
        {
            (push, op)
        }
        _ => return None,
    };

    let push_val = push.code.unwrap_push_int();

    assembler.set_op_range(ip, ip + 2);
    let reg = assembler.reg_alloc_dyn_pop();

    assembler.push_instr([
        str_lit(op.code.compile_arithmetic_op()),
        dyn_reg(reg),
        str_lit(format!(", {}", push_val)),
    ]);

    assembler.reg_free_dyn_push(reg);

    Some(2)
}

// Optimizes a Mem-Push-Store sequence.
fn mem_push_store(
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    _: &Interners,
) -> Option<usize> {
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

    assembler.set_op_range(ip, ip + 3);

    assembler.push_instr([str_lit(format!(
        "    mov BYTE [__memory + {}], {}",
        mem_val, push_val
    ))]);

    Some(3)
}

/// Optimises the Mem-Load sequence.
fn mem_load(ops: &[Op], ip: usize, assembler: &mut Assembler, _: &Interners) -> Option<usize> {
    let mem = match ops {
        [mem, load, ..] if mem.code.is_mem() && load.code.is_load() => mem,
        _ => return None,
    };

    let mem_val = mem.code.unwrap_mem();
    assembler.set_op_range(ip, ip + 2);

    let reg = assembler.reg_alloc_dyn_literal("0");
    assembler.push_instr([
        str_lit("    mov "),
        dyn_byte_reg(reg),
        str_lit(format!(", BYTE [__memory + {}]", mem_val)),
    ]);
    assembler.reg_free_dyn_push(reg);

    Some(2)
}

/// Compiles a single instruction in isolation. Doesn't actually optimize.
pub(super) fn compile_single_instruction(
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    interner: &Interners,
) -> Option<usize> {
    use super::InstructionPart::FixedRegister;

    let op = ops.get(0)?;
    assembler.set_op_range(ip, ip + 1);
    match op.code {
        OpCode::Add | OpCode::Subtract | OpCode::BitOr | OpCode::BitAnd => {
            let b_id = assembler.reg_alloc_dyn_pop();
            let a_id = assembler.reg_alloc_dyn_pop();

            assembler.push_instr([
                str_lit(op.code.compile_arithmetic_op()),
                dyn_reg(a_id),
                str_lit(", "),
                dyn_reg(b_id),
            ]);

            assembler.reg_free_dyn_drop(b_id);
            assembler.reg_free_dyn_push(a_id);
        }
        OpCode::ShiftLeft | OpCode::ShiftRight => {
            assembler.reg_alloc_fixed_pop(Register::Rcx);
            let a_id = assembler.reg_alloc_dyn_pop();

            assembler.push_instr([
                str_lit(op.code.compile_arithmetic_op()),
                dyn_reg(a_id),
                str_lit(", "),
                FixedRegister(Register::Cl),
            ]);

            assembler.reg_free_fixed_drop(Register::Rcx);
            assembler.reg_free_dyn_push(a_id);
        }
        OpCode::DivMod => {
            let divisor_reg = assembler.reg_alloc_dyn_pop();
            assembler.reg_alloc_fixed_pop(Register::Rax);
            assembler.reg_alloc_fixed_literal(Register::Rdx, "0");

            assembler.push_instr([str_lit("    div "), dyn_reg(divisor_reg)]);

            assembler.reg_free_dyn_drop(divisor_reg);
            assembler.reg_free_fixed_push(Register::Rax);
            assembler.reg_free_fixed_push(Register::Rdx);
        }
        OpCode::Multiply => {
            assembler.reg_alloc_fixed_pop(Register::Rax);
            assembler.reg_alloc_fixed_literal(Register::Rdx, "0");
            let mult_reg = assembler.reg_alloc_dyn_pop();

            assembler.push_instr([str_lit("    mul "), dyn_reg(mult_reg)]);

            assembler.reg_free_dyn_drop(mult_reg);
            assembler.reg_free_fixed_drop(Register::Rdx);
            assembler.reg_free_fixed_push(Register::Rax);
        }

        OpCode::Equal
        | OpCode::NotEq
        | OpCode::Less
        | OpCode::LessEqual
        | OpCode::Greater
        | OpCode::GreaterEqual => {
            let b_id = assembler.reg_alloc_dyn_pop();
            let a_id = assembler.reg_alloc_dyn_pop();
            let dst_id = assembler.reg_alloc_dyn_literal("0");

            assembler.push_instr([
                str_lit("    cmp "),
                dyn_reg(a_id),
                str_lit(", "),
                dyn_reg(b_id),
            ]);

            assembler.push_instr([
                str_lit(format!("    set{} ", op.code.compile_compare_op_suffix())),
                dyn_byte_reg(dst_id),
            ]);

            assembler.reg_free_dyn_drop(b_id);
            assembler.reg_free_dyn_drop(a_id);
            assembler.reg_free_dyn_push(dst_id);
        }

        OpCode::ArgC => {
            let reg = assembler.reg_alloc_dyn_literal("QWORD [__argc]");
            assembler.reg_free_dyn_push(reg);
        }
        OpCode::ArgV => {
            let reg = assembler.reg_alloc_dyn_literal("QWORD [__argv]");
            assembler.reg_free_dyn_push(reg);
        }
        OpCode::PushBool(val) => {
            let reg = assembler.reg_alloc_dyn_literal((val as u64).to_string());
            assembler.reg_free_dyn_push(reg);
        }
        OpCode::PushInt(val) => {
            let reg = assembler.reg_alloc_dyn_literal(val.to_string());
            assembler.reg_free_dyn_push(reg);
        }
        OpCode::PushStr(id) => {
            let literal = interner.resolve_literal(id);
            let id = id.into_inner().get();

            let len_reg = assembler.reg_alloc_dyn_literal(literal.len().to_string());
            let ptr_reg = assembler.reg_alloc_dyn_literal(format!("__string_literal{}", id));
            assembler.reg_free_dyn_push(len_reg);
            assembler.reg_free_dyn_push(ptr_reg);
        }
        OpCode::Mem { offset } => {
            let reg = assembler.reg_alloc_dyn_literal(format!("__memory + {}", offset));
            assembler.reg_free_dyn_push(reg);
        }

        OpCode::Drop => {
            let reg = assembler.reg_alloc_dyn_pop();
            assembler.reg_free_dyn_drop(reg);
        }
        OpCode::Dup { depth } => {
            let reg = assembler.reg_alloc_dyn_dup(depth);
            assembler.reg_free_dyn_push(reg);
        }
        OpCode::DupPair => {
            let reg_top = assembler.reg_alloc_dyn_dup(0);
            let reg_lower = assembler.reg_alloc_dyn_dup(1);
            assembler.reg_free_dyn_push(reg_lower);
            assembler.reg_free_dyn_push(reg_top);
        }
        OpCode::Print => {
            assembler.reg_alloc_fixed_pop(Register::Rdi);
            assembler.push_instr([str_lit("    call dump")]);
            assembler.reg_free_fixed_drop(Register::Rdi);
        }
        OpCode::Rot => {
            let a_reg = assembler.reg_alloc_dyn_pop();
            let b_reg = assembler.reg_alloc_dyn_pop();
            let c_reg = assembler.reg_alloc_dyn_pop();

            assembler.reg_free_dyn_push(b_reg);
            assembler.reg_free_dyn_push(a_reg);
            assembler.reg_free_dyn_push(c_reg);
        }
        OpCode::Swap => {
            let a_id = assembler.reg_alloc_dyn_pop();
            let b_id = assembler.reg_alloc_dyn_pop();
            assembler.reg_free_dyn_push(a_id);
            assembler.reg_free_dyn_push(b_id);
        }

        OpCode::Load => {
            let addr_reg = assembler.reg_alloc_dyn_pop();
            let val_reg = assembler.reg_alloc_dyn_literal("0");

            assembler.push_instr([
                str_lit("    mov "),
                dyn_byte_reg(val_reg),
                str_lit(", BYTE ["),
                dyn_reg(addr_reg),
                str_lit("]"),
            ]);

            assembler.reg_free_dyn_drop(addr_reg);
            assembler.reg_free_dyn_push(val_reg);
        }
        OpCode::Load64 => {
            let addr_reg = assembler.reg_alloc_dyn_pop();
            let val_reg = assembler.reg_alloc_dyn_nop();

            assembler.push_instr([
                str_lit("    mov "),
                dyn_reg(val_reg),
                str_lit(", QWORD ["),
                dyn_reg(addr_reg),
                str_lit("]"),
            ]);

            assembler.reg_free_dyn_drop(addr_reg);
            assembler.reg_free_dyn_push(val_reg);
        }
        OpCode::Store { forth_style } => {
            #[allow(clippy::branches_sharing_code)]
            let (val_reg, addr_reg) = if forth_style {
                let addr_reg = assembler.reg_alloc_dyn_pop();
                let val_reg = assembler.reg_alloc_dyn_pop();
                (val_reg, addr_reg)
            } else {
                let val_reg = assembler.reg_alloc_dyn_pop();
                let addr_reg = assembler.reg_alloc_dyn_pop();
                (val_reg, addr_reg)
            };
            assembler.push_instr([
                str_lit("    mov BYTE ["),
                dyn_reg(addr_reg),
                str_lit("], "),
                dyn_byte_reg(val_reg),
            ]);

            assembler.reg_free_dyn_drop(val_reg);
            assembler.reg_free_dyn_drop(addr_reg);
        }
        OpCode::Store64 { forth_style } => {
            #[allow(clippy::branches_sharing_code)]
            let (val_reg, addr_reg) = if forth_style {
                let addr_reg = assembler.reg_alloc_dyn_pop();
                let val_reg = assembler.reg_alloc_dyn_pop();
                (val_reg, addr_reg)
            } else {
                let val_reg = assembler.reg_alloc_dyn_pop();
                let addr_reg = assembler.reg_alloc_dyn_pop();
                (val_reg, addr_reg)
            };
            assembler.push_instr([
                str_lit("    mov QWORD ["),
                dyn_reg(addr_reg),
                str_lit("], "),
                dyn_reg(val_reg),
            ]);

            assembler.reg_free_dyn_drop(val_reg);
            assembler.reg_free_dyn_drop(addr_reg);
        }

        OpCode::DoWhile { end_ip, .. } | OpCode::DoIf { end_ip, .. } => {
            let reg_id = assembler.reg_alloc_dyn_pop();

            assembler.push_instr([
                str_lit("    test "),
                dyn_reg(reg_id),
                str_lit(", "),
                dyn_reg(reg_id),
            ]);
            assembler.push_instr([str_lit(format!("    jz .LBL{}", end_ip))]);

            assembler.reg_free_dyn_drop(reg_id);
            assembler.block_boundry();
        }
        OpCode::While { ip } => {
            assembler.push_instr([str_lit(format!(".LBL{}:", ip))]);
            assembler.block_boundry();
        }
        OpCode::EndWhile {
            condition_ip,
            end_ip,
        } => {
            assembler.push_instr([str_lit(format!("    jmp .LBL{}", condition_ip))]);
            assembler.push_instr([str_lit(format!(".LBL{}:", end_ip))]);
            assembler.block_boundry();
        }

        OpCode::If => {
            assembler.block_boundry();
        }
        OpCode::Elif { end_ip, else_start } | OpCode::Else { end_ip, else_start } => {
            assembler.push_instr([str_lit(format!("    jmp .LBL{}", end_ip))]);
            assembler.push_instr([str_lit(format!(".LBL{}:", else_start))]);
            assembler.block_boundry();
        }
        OpCode::EndIf { ip } => {
            assembler.push_instr([str_lit(format!(".LBL{}:", ip))]);
            assembler.block_boundry();
        }

        OpCode::SysCall(a @ 0..=6) => {
            let regs = [
                Register::Rax,
                Register::Rdi,
                Register::Rsi,
                Register::Rdx,
                Register::R10,
                Register::R8,
                Register::R9,
            ];

            for &reg in &regs[..=a] {
                assembler.reg_alloc_fixed_pop(reg);
            }

            assembler.push_instr([str_lit("    syscall")]);

            for &reg in &regs[1..=a] {
                assembler.reg_free_fixed_drop(reg);
            }
            assembler.reg_free_fixed_push(Register::Rax);
        }

        OpCode::CastPtr => {}

        OpCode::SysCall(arg_count) => {
            panic!("ICE: Invalid syscall argument count: {}", arg_count)
        }
        OpCode::Do | OpCode::End | OpCode::Ident(_) | OpCode::Include(_) => {
            panic!("ICE: Encountered: {:?}", op.code)
        }
    }

    Some(1)
}
