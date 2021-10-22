use std::{borrow::Cow, collections::HashMap, fs::File, io::BufWriter, io::Write, path::Path};

use codespan_reporting::files::Files;
use color_eyre::eyre::{eyre, Context, Result};

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    source_file::SourceStorage,
    MEMORY_CAPACITY,
};

mod assembly;
use assembly::*;

#[derive(Debug)]
struct RegisterAllocator {
    available_registers: Vec<Register>,
}

impl RegisterAllocator {
    fn new() -> Self {
        Self {
            available_registers: vec![
                Register::Rbx,
                Register::R11,
                Register::R12,
                Register::R13,
                Register::R14,
                Register::R15,
            ],
        }
    }

    fn allocate(&mut self) -> Option<Register> {
        self.available_registers.pop()
    }

    fn free(&mut self, reg: Register) {
        self.available_registers.push(reg);
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct OpRange {
    start: usize,
    end: usize,
}

fn write_assembly(
    out_file_path: &Path,
    source_store: &SourceStorage,
    interner: &Interners,
    ops: &[Op],
    asm: &[Assembly],
) -> Result<()> {
    let mut cur_exe_dur =
        std::env::current_exe().with_context(|| eyre!("Failed to get compiler exe path"))?;
    cur_exe_dur.set_file_name("std_asm.asm");
    let mut std_asm = File::open(&cur_exe_dur)
        .with_context(|| eyre!("Failed to open {}", cur_exe_dur.display()))?;

    let out_file = File::create(out_file_path)
        .with_context(|| eyre!("Failed to create file: {}", out_file_path.display()))?;
    let mut out_file = BufWriter::new(out_file);

    writeln!(&mut out_file, "BITS 64")?;
    writeln!(&mut out_file, "segment .text")?;
    writeln!(&mut out_file, "global _start")?;

    std::io::copy(&mut std_asm, &mut out_file).with_context(|| {
        eyre!(
            "Failed to copy std_asm.asm contents to {}",
            out_file_path.display()
        )
    })?;

    writeln!(&mut out_file, "_start:")?;
    writeln!(&mut out_file, "    pop QWORD [__argc]")?;
    writeln!(&mut out_file, "    mov QWORD [__argv], rsp")?;
    // R15 is used for single-byte handling, so we ideally do not want to touch the upper bytes.
    writeln!(&mut out_file, "    xor r15, r15")?;

    let mut register_allocator = RegisterAllocator::new();
    let mut register_map = HashMap::new();

    let mut last_op_range = usize::MAX..usize::MAX; // Intentinally invalid.
    for asm in asm {
        if last_op_range != asm.op_range {
            last_op_range = asm.op_range.clone();
            for (op, ip) in ops[asm.op_range.clone()].iter().zip(asm.op_range.clone()) {
                let location = source_store
                    .location(op.token.location.file_id, op.token.location.source_start)?;
                writeln!(
                    &mut out_file,
                    ";; IP{} -- {}:{}:{} -- {:?}",
                    ip,
                    source_store.name(op.token.location.file_id)?,
                    location.line_number,
                    location.column_number,
                    op.code,
                )?;
            }
        }

        asm.asm
            .render(&mut out_file, &mut register_allocator, &mut register_map)?;
    }

    writeln!(&mut out_file, "    mov rax, 60")?;
    writeln!(&mut out_file, "    mov rdi, 0")?;
    writeln!(&mut out_file, "    syscall")?;

    writeln!(&mut out_file, "segment .rodata")?;
    for (id, literal) in interner.iter_literals() {
        let id = id.into_inner().get();
        write!(&mut out_file, "    __string_literal{}: db ", id)?;

        for b in literal.as_bytes() {
            write!(&mut out_file, "{},", b)?;
        }

        out_file.write_all(b"0\n")?;
    }

    writeln!(&mut out_file, "segment .bss")?;
    writeln!(&mut out_file, "    __argc: resq {}", 1)?;
    writeln!(&mut out_file, "    __argv: resq {}", 1)?;
    writeln!(&mut out_file, "    __memory: resb {}", MEMORY_CAPACITY)?;

    Ok(())
}

impl OpCode {
    fn compile_arithmetic_op(self) -> &'static str {
        match self {
            OpCode::Add => "    add ",
            OpCode::BitOr => "    or ",
            OpCode::BitAnd => "    and ",
            OpCode::Multiply => "    mul ",
            OpCode::ShiftLeft => "    shl ",
            OpCode::ShiftRight => "    shr ",
            OpCode::Subtract => "    sub ",
            _ => panic!("ICE: Attempted to compile_arithmetic_op a {:?}", self),
        }
    }

    fn compile_compare_op_suffix(self) -> &'static str {
        match self {
            OpCode::Equal => "e",
            OpCode::Greater => "g",
            OpCode::GreaterEqual => "ge",
            OpCode::Less => "l",
            OpCode::LessEqual => "le",
            OpCode::NotEq => "ne",
            _ => panic!("ICE: Attempted to compile_compare_op a {:?}", self),
        }
    }
}

fn build_assembly(program: &[Op], interner: &Interners) -> Vec<Assembly> {
    use InstructionPart::{DynamicRegister, FixedRegister};

    let mut assembler = Assembler::default();

    let dyn_reg = |reg_id| DynamicRegister {
        reg_id,
        is_byte: false,
    };
    let dyn_byte_reg = |reg_id| DynamicRegister {
        reg_id,
        is_byte: true,
    };

    fn str_lit(lit: impl Into<Cow<'static, str>>) -> InstructionPart {
        InstructionPart::Literal(lit.into())
    }

    for (ip, op) in program.iter().enumerate() {
        assembler.set_op_range(ip, ip + 1);

        match op.code {
            OpCode::Add | OpCode::Subtract | OpCode::BitOr | OpCode::BitAnd => {
                let a_id = assembler.reg_alloc_dyn_pop();
                let b_id = assembler.reg_alloc_dyn_pop();

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

            OpCode::ArgC => assembler.push_instr([str_lit("    push QWORD [__argc]")]),
            OpCode::ArgV => assembler.push_instr([str_lit("    push QWORD [__argv]")]),
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
                let reg = assembler.reg_alloc_dyn_literal(format!("QWORD [rsp + 8*{}]", depth));
                assembler.reg_free_dyn_push(reg);
            }
            OpCode::DupPair => {
                let reg_top = assembler.reg_alloc_dyn_literal("QWORD [rsp]");
                let reg_lower = assembler.reg_alloc_dyn_literal("QWORD [rsp+8]");
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
            }
            OpCode::While { ip } => {
                assembler.push_instr([str_lit(format!(".LBL{}:", ip))]);
            }
            OpCode::EndWhile {
                condition_ip,
                end_ip,
            } => {
                assembler.push_instr([str_lit(format!("    jmp .LBL{}", condition_ip))]);
                assembler.push_instr([str_lit(format!(".LBL{}:", end_ip))]);
            }

            OpCode::If => {}
            OpCode::Elif { end_ip, else_start } | OpCode::Else { end_ip, else_start } => {
                assembler.push_instr([str_lit(format!("    jmp .LBL{}", end_ip))]);
                assembler.push_instr([str_lit(format!(".LBL{}:", else_start))]);
            }
            OpCode::EndIf { ip } => {
                assembler.push_instr([str_lit(format!(".LBL{}:", ip))]);
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
    }

    assembler.into_assembly()
}

pub(crate) fn compile_program(
    program: &[Op],
    source_store: &SourceStorage,
    interner: &Interners,
    out_file_path: &Path,
    optimize: bool,
) -> Result<()> {
    let assembly = build_assembly(program, interner);

    dbg!(&assembly);

    write_assembly(out_file_path, source_store, interner, program, &assembly)?;

    Ok(())
}
