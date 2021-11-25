use std::borrow::Cow;

use crate::{
    compile::{assembly::X86Register, FIXED_REGS},
    interners::Interners,
    n_ops::NOps,
    opcode::{Op, OpCode},
    program::{Procedure, Program},
    Width,
};

use super::assembly::{Assembler, InstructionPart, RegisterType};

type OptimizerFunction =
    fn(&Program, &Procedure, &[Op], usize, &mut Assembler, &mut Interners) -> Option<usize>;

pub(super) const PASSES: &[OptimizerFunction] = &[
    dup_boundry,
    duppair_boundry,
    push_compare,
    push_shift,
    push_arithmetic,
    mem_push_store,
    mem_load,
    compile_single_instruction,
];

fn dyn_reg(reg_id: usize) -> InstructionPart {
    InstructionPart::EmitRegister {
        reg: RegisterType::Dynamic(reg_id),
        width: Width::Qword,
    }
}
fn dyn_sized_reg(reg_id: usize, width: Width) -> InstructionPart {
    InstructionPart::EmitRegister {
        reg: RegisterType::Dynamic(reg_id),
        width,
    }
}
pub(super) fn use_reg(reg: RegisterType) -> InstructionPart {
    InstructionPart::UseRegister { reg }
}
pub(super) fn str_lit(lit: impl Into<Cow<'static, str>>) -> InstructionPart {
    InstructionPart::Literal(lit.into())
}

const ARITH_OP_MAX: u64 = u32::MAX as u64;

impl Width {
    fn to_asm(self) -> &'static str {
        match self {
            Width::Byte => "BYTE",
            Width::Word => "WORD",
            Width::Dword => "DWORD",
            Width::Qword => "QWORD",
        }
    }
}

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

/// Optimize a Dup immediately following a block boundry
/// (While, DoWhile, If, DoIf, Elif, Else, EndIf, EndWhile)
fn dup_boundry(
    program: &Program,
    proc: &Procedure,
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    interner: &mut Interners,
) -> Option<usize> {
    use OpCode::*;
    let (start, _) = ops.firstn()?;
    let dup = match start {
        [boundry, dup]
            if matches!(
                boundry.code,
                While { .. }
                    | DoWhile { .. }
                    | DoIf { .. }
                    | If
                    | Elif { .. }
                    | Else { .. }
                    | EndIf { .. }
                    | EndWhile { .. }
            ) && dup.code.is_dup() =>
        {
            dup
        }
        _ => return None,
    };

    // We don't actually need any special handling for the boundry token,
    // so we can just throw it into the single-instruction handler.
    compile_single_instruction(program, proc, ops, ip, assembler, interner)?;

    let depth = dup.code.unwrap_dup();
    assembler.set_op_range(ip + 1, ip + 2);

    let reg = assembler.reg_alloc_dyn_dup(depth);
    assembler.reg_free_dyn_push(reg);

    Some(start.len())
}

/// Optimize a DupPair immediately following a block boundry
/// (While, DoWhile, If, DoIf, Elif, Else, EndIf, EndWhile)
fn duppair_boundry(
    program: &Program,
    proc: &Procedure,
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    interner: &mut Interners,
) -> Option<usize> {
    use OpCode::*;
    let (start, _) = ops.firstn()?;
    match start {
        [boundry, dup]
            if matches!(
                boundry.code,
                While { .. }
                    | DoWhile { .. }
                    | DoIf { .. }
                    | If
                    | Elif { .. }
                    | Else { .. }
                    | EndIf { .. }
                    | EndWhile { .. }
            ) && dup.code.is_dup_pair() => {}
        _ => return None,
    }

    // We don't actually need any special handling for the boundry token,
    // so we can just throw it into the single-instruction handler.
    compile_single_instruction(program, proc, ops, ip, assembler, interner)?;

    assembler.set_op_range(ip + 1, ip + 2);

    let top_reg = assembler.reg_alloc_dyn_dup(0);
    let bottom_reg = assembler.reg_alloc_dyn_dup(1);
    assembler.reg_free_dyn_push(bottom_reg);
    assembler.reg_free_dyn_push(top_reg);

    Some(start.len())
}

/// Optimize a Push-Compare
fn push_compare(
    _: &Program,
    _: &Procedure,
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    _: &mut Interners,
) -> Option<usize> {
    let (start, _) = ops.firstn()?;
    let (push, op) = match start {
        [push, op]
            if op.code.is_compare() && matches!(push.code, OpCode::PushInt(0..=ARITH_OP_MAX)) =>
        {
            (push, op)
        }
        _ => return None,
    };

    let push_val = push.code.unwrap_push_int();

    assembler.set_op_range(ip, ip + start.len());
    let reg = assembler.reg_alloc_dyn_pop();
    let result_reg = assembler.reg_alloc_dyn_literal("0");
    let op_suffix = op.code.compile_compare_op_suffix();

    assembler.push_instr([
        str_lit("    cmp "),
        dyn_reg(reg),
        str_lit(format!(", {}", push_val)),
    ]);
    assembler.push_instr([
        str_lit(format!("    set{} ", op_suffix)),
        dyn_sized_reg(result_reg, Width::Byte),
    ]);
    assembler.reg_free_dyn_drop(reg);
    assembler.reg_free_dyn_push(result_reg);

    Some(start.len())
}

/// Optimize a Push-ShiftOp
fn push_shift(
    _: &Program,
    _: &Procedure,
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    _: &mut Interners,
) -> Option<usize> {
    let (start, _) = ops.firstn()?;
    let (push, op) = match start {
        [push, op]
            if op.code.is_compiler_opt_shift() && matches!(push.code, OpCode::PushInt(0..=255)) =>
        {
            (push, op)
        }
        _ => return None,
    };

    let push_val = push.code.unwrap_push_int();

    assembler.set_op_range(ip, ip + start.len());
    let reg = assembler.reg_alloc_dyn_pop();

    assembler.push_instr([
        str_lit(op.code.compile_arithmetic_op()),
        dyn_reg(reg),
        str_lit(format!(", {}", push_val)),
    ]);

    assembler.reg_free_dyn_push(reg);

    Some(start.len())
}

/// Optimize a Push-ArithBinOp
fn push_arithmetic(
    _: &Program,
    _: &Procedure,
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    _: &mut Interners,
) -> Option<usize> {
    let (start, _) = ops.firstn()?;
    let (push, op) = match start {
        [push, op]
            if op.code.is_compiler_opt_arithmetic()
                && matches!(push.code, OpCode::PushInt(0..=ARITH_OP_MAX)) =>
        {
            (push, op)
        }
        _ => return None,
    };

    let push_val = push.code.unwrap_push_int();

    assembler.set_op_range(ip, ip + start.len());
    let reg = assembler.reg_alloc_dyn_pop();

    assembler.push_instr([
        str_lit(op.code.compile_arithmetic_op()),
        dyn_reg(reg),
        str_lit(format!(", {}", push_val)),
    ]);

    assembler.reg_free_dyn_push(reg);

    Some(start.len())
}

// Optimizes a Mem-Push-Store sequence.
fn mem_push_store(
    program: &Program,
    proc: &Procedure,
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    interner: &mut Interners,
) -> Option<usize> {
    let (start, _) = ops.firstn()?;
    let (mem, push, store) = match start {
        [push, mem, store]
            if mem.code.is_memory()
                && matches!(push.code, OpCode::PushInt(0..=ARITH_OP_MAX))
                && store.code.is_store() =>
        {
            (mem, push, store)
        }
        _ => return None,
    };

    let (_, proc_id, offset, global) = mem.code.unwrap_memory();
    let push_val = push.code.unwrap_push_int();
    let width = store.code.unwrap_store();
    assembler.set_op_range(ip, ip + start.len());

    if global {
        assembler.use_global_alloc(proc_id);
        let mem_id = interner.get_symbol_name(program, proc_id);

        assembler.push_instr([str_lit(format!(
            "    mov {} [__{} + {}], {}",
            width.to_asm(),
            mem_id,
            offset,
            push_val
        ))]);
    } else {
        let proc_data = proc.kind().get_proc_data();
        let base_offset = proc_data.alloc_size_and_offsets[&proc_id].offset;
        assembler.push_instr([str_lit(format!(
            "    mov {} [rbp + {} + {}], {}",
            width.to_asm(),
            base_offset,
            offset,
            push_val
        ))]);
    }

    Some(start.len())
}

/// Optimises the Mem-Load sequence.
fn mem_load(
    program: &Program,
    proc: &Procedure,
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    interner: &mut Interners,
) -> Option<usize> {
    let (start, _) = ops.firstn()?;
    let (mem, load) = match start {
        [mem, load] if mem.code.is_memory() && load.code.is_load() => (mem, load),
        _ => return None,
    };

    let (_, proc_id, mem_offset, global) = mem.code.unwrap_memory();
    let width = load.code.unwrap_load();
    assembler.set_op_range(ip, ip + start.len());

    let reg = if width != Width::Qword {
        assembler.reg_alloc_dyn_literal("0")
    } else {
        assembler.reg_alloc_dyn_nop()
    };

    if global {
        assembler.use_global_alloc(proc_id);
        let mem_id = interner.get_symbol_name(program, proc_id);

        assembler.push_instr([
            str_lit("    mov "),
            dyn_sized_reg(reg, width),
            str_lit(format!(
                ", {} [__{} + {}]",
                width.to_asm(),
                mem_id,
                mem_offset
            )),
        ]);
    } else {
        let proc_data = proc.kind().get_proc_data();
        let base_offset = proc_data.alloc_size_and_offsets[&proc_id].offset;
        assembler.push_instr([
            str_lit("    mov "),
            dyn_sized_reg(reg, width),
            str_lit(format!(
                ", {} [rbp + {} + {}]",
                width.to_asm(),
                base_offset,
                mem_offset
            )),
        ]);
    }

    assembler.reg_free_dyn_push(reg);

    Some(start.len())
}

/// Compiles a single instruction in isolation. Doesn't actually optimize.
pub(super) fn compile_single_instruction(
    program: &Program,
    proc: &Procedure,
    ops: &[Op],
    ip: usize,
    assembler: &mut Assembler,
    interner: &mut Interners,
) -> Option<usize> {
    use super::{InstructionPart::EmitRegister, RegisterType::Fixed};

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
        OpCode::BitNot => {
            let a_id = assembler.reg_alloc_dyn_pop();
            assembler.push_instr([str_lit("    not "), dyn_reg(a_id)]);
            assembler.reg_free_dyn_push(a_id);
        }
        OpCode::ShiftLeft | OpCode::ShiftRight => {
            assembler.reg_alloc_fixed_pop(X86Register::Rcx);
            let a_id = assembler.reg_alloc_dyn_pop();

            assembler.push_instr([
                str_lit(op.code.compile_arithmetic_op()),
                dyn_reg(a_id),
                str_lit(", "),
                EmitRegister {
                    reg: Fixed(X86Register::Rcx),
                    width: Width::Byte,
                },
            ]);

            assembler.reg_free_fixed_drop(X86Register::Rcx);
            assembler.reg_free_dyn_push(a_id);
        }
        OpCode::DivMod => {
            let divisor_reg = assembler.reg_alloc_dyn_pop();
            assembler.reg_alloc_fixed_pop(X86Register::Rax);
            assembler.reg_alloc_fixed_literal(X86Register::Rdx, "0");

            assembler.push_instr([str_lit("    div "), dyn_reg(divisor_reg)]);

            assembler.reg_free_dyn_drop(divisor_reg);
            assembler.reg_free_fixed_push(X86Register::Rax);
            assembler.reg_free_fixed_push(X86Register::Rdx);
        }
        OpCode::Multiply => {
            assembler.reg_alloc_fixed_pop(X86Register::Rax);
            assembler.reg_alloc_fixed_nop(X86Register::Rdx);
            let mult_reg = assembler.reg_alloc_dyn_pop();

            assembler.push_instr([str_lit("    mul "), dyn_reg(mult_reg)]);

            assembler.reg_free_dyn_drop(mult_reg);
            assembler.reg_free_fixed_drop(X86Register::Rdx);
            assembler.reg_free_fixed_push(X86Register::Rax);
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
                dyn_sized_reg(dst_id, Width::Byte),
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
        OpCode::PushStr { id, is_c_str } => {
            assembler.use_string(id);

            let literal = interner.resolve_literal(id);
            let id = id.into_inner().get();

            if !is_c_str {
                // Strings are null-terminated during parsing, but the Porth-style strings shouldn't
                // include that character.
                let len = literal.len() - 1;

                let len_reg = assembler.reg_alloc_dyn_literal(len.to_string());
                assembler.reg_free_dyn_push(len_reg);
            }
            let ptr_reg = assembler.reg_alloc_dyn_literal(format!("__string_literal{}", id));
            assembler.reg_free_dyn_push(ptr_reg);
        }
        OpCode::Memory {
            proc_id,
            offset,
            global: false,
            ..
        } => {
            let proc_data = proc.kind().get_proc_data();
            let base_offset = proc_data.alloc_size_and_offsets[&proc_id].offset;
            let reg = assembler.reg_alloc_dyn_lea(format!("rbp + {} + {}", base_offset, offset));
            assembler.reg_free_dyn_push(reg);
        }
        OpCode::Memory {
            proc_id,
            offset,
            global: true,
            ..
        } => {
            assembler.use_global_alloc(proc_id);

            let alloc_name = interner.get_symbol_name(program, proc_id);
            let reg = assembler.reg_alloc_dyn_literal(format!("__{} + {}", alloc_name, offset));
            assembler.reg_free_dyn_push(reg);
        }

        OpCode::Drop => {
            let reg = assembler.reg_alloc_dyn_pop();
            assembler.reg_free_dyn_drop(reg);
        }
        OpCode::Dup { depth: 0 } => {
            let top = assembler.reg_alloc_dyn_pop();
            let duped = assembler.reg_alloc_dyn_mov(RegisterType::Dynamic(top));
            assembler.reg_free_dyn_push(top);
            assembler.reg_free_dyn_push(duped);
        }
        OpCode::Dup { depth: 1 } => {
            let top = assembler.reg_alloc_dyn_pop();
            let lower = assembler.reg_alloc_dyn_pop();
            let duped = assembler.reg_alloc_dyn_mov(RegisterType::Dynamic(lower));
            assembler.reg_free_dyn_push(lower);
            assembler.reg_free_dyn_push(top);
            assembler.reg_free_dyn_push(duped);
        }
        OpCode::Dup { depth } => {
            let reg = assembler.reg_alloc_dyn_dup(depth);
            assembler.reg_free_dyn_push(reg);
        }
        OpCode::DupPair => {
            let reg_top = assembler.reg_alloc_dyn_pop();
            let reg_lower = assembler.reg_alloc_dyn_pop();
            let reg_dup_top = assembler.reg_alloc_dyn_mov(RegisterType::Dynamic(reg_top));
            let reg_dup_lower = assembler.reg_alloc_dyn_mov(RegisterType::Dynamic(reg_lower));

            assembler.reg_free_dyn_push(reg_lower);
            assembler.reg_free_dyn_push(reg_top);
            assembler.reg_free_dyn_push(reg_dup_lower);
            assembler.reg_free_dyn_push(reg_dup_top);
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

        OpCode::Load(width) => {
            let addr_reg = assembler.reg_alloc_dyn_pop();
            let val_reg = if width == Width::Qword {
                assembler.reg_alloc_dyn_nop()
            } else {
                assembler.reg_alloc_dyn_literal("0")
            };

            assembler.push_instr([
                str_lit("    mov "),
                dyn_sized_reg(val_reg, width),
                str_lit(format!(", {} [", width.to_asm())),
                dyn_reg(addr_reg),
                str_lit("]"),
            ]);

            assembler.reg_free_dyn_drop(addr_reg);
            assembler.reg_free_dyn_push(val_reg);
        }
        OpCode::Store(width) => {
            let addr_reg = assembler.reg_alloc_dyn_pop();
            let val_reg = assembler.reg_alloc_dyn_pop();
            assembler.push_instr([
                str_lit(format!("    mov {} [", width.to_asm())),
                dyn_reg(addr_reg),
                str_lit("], "),
                dyn_sized_reg(val_reg, width),
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

        OpCode::CallProc { proc_id, .. } => {
            let callee = program.get_proc(proc_id);
            assembler.use_function(proc_id);
            let proc_name = interner.get_symbol_name(program, proc_id);

            let num_regs = FIXED_REGS.len().min(callee.entry_stack().len());
            for &reg in &FIXED_REGS[..num_regs] {
                assembler.reg_alloc_fixed_pop(reg);
            }

            assembler.swap_stacks();
            assembler.block_boundry();
            assembler.push_instr([str_lit(format!("    call proc_{}", proc_name))]);
            assembler.swap_stacks();

            let num_regs = FIXED_REGS.len().min(callee.exit_stack().len());
            for &reg in FIXED_REGS[..num_regs].iter().rev() {
                assembler.reg_free_fixed_push(reg);
            }
        }
        OpCode::Epilogue => {
            let num_regs = FIXED_REGS.len().min(proc.exit_stack().len());
            for &reg in &FIXED_REGS[..num_regs] {
                assembler.reg_alloc_fixed_pop(reg);
            }
        }
        OpCode::Prologue => {
            // Entry of the function, we need to push the values on the value stack
            // in reverse order.
            let num_call_regs = FIXED_REGS.len().min(proc.entry_stack().len());
            let call_regs = &FIXED_REGS[..num_call_regs];

            for &reg in call_regs.iter().rev() {
                assembler.reg_free_fixed_push(reg);
            }
        }
        OpCode::Return { .. } => {
            assembler.swap_stacks();

            let proc_data = proc.kind().get_proc_data();
            if !proc_data.allocs.is_empty() {
                assembler.push_instr([str_lit(format!(
                    "    add rsp, {}",
                    proc_data.total_alloc_size
                ))]);
            }
            assembler.push_instr([str_lit("    ret")]);
        }

        OpCode::SysCall(a @ 0..=6) => {
            for &reg in &FIXED_REGS[..=a] {
                assembler.reg_alloc_fixed_pop(reg);
            }

            assembler.push_instr([
                str_lit("    syscall"),
                // For lazyness we'll assume it uses all the registers.
                use_reg(Fixed(X86Register::Rax)),
                use_reg(Fixed(X86Register::Rdi)),
                use_reg(Fixed(X86Register::Rsi)),
                use_reg(Fixed(X86Register::Rdx)),
                use_reg(Fixed(X86Register::R10)),
                use_reg(Fixed(X86Register::R8)),
                use_reg(Fixed(X86Register::R9)),
            ]);

            for &reg in &FIXED_REGS[1..=a] {
                assembler.reg_free_fixed_drop(reg);
            }
            assembler.reg_free_fixed_push(X86Register::Rax);
        }

        OpCode::CastBool | OpCode::CastInt | OpCode::CastPtr => {}

        OpCode::SysCall(arg_count) => {
            panic!("ICE: Invalid syscall argument count: {}", arg_count)
        }
        OpCode::Do
        | OpCode::End
        | OpCode::UnresolvedIdent { .. }
        | OpCode::ResolvedIdent { .. } => {
            panic!("ICE: Encountered: {:?}", op.code)
        }
    }

    Some(1)
}
