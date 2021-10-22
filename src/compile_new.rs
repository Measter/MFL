use std::{
    borrow::Cow, collections::HashMap, fs::File, io::BufWriter, io::Write, ops::Range, path::Path,
};

use codespan_reporting::files::Files;
use color_eyre::eyre::{eyre, Context, Result};
use derive_more::Display;

use crate::{
    interners::Interners,
    opcode::{Op, OpCode},
    source_file::SourceStorage,
    MEMORY_CAPACITY,
};

#[derive(Debug, Clone, Copy, Display)]
enum Register {
    #[display(fmt = "r8")]
    R8,
    #[display(fmt = "r8b")]
    R8b,
    #[display(fmt = "r9")]
    R9,
    #[display(fmt = "r9b")]
    R9b,
    #[display(fmt = "r10")]
    R10,
    #[display(fmt = "r10b")]
    R10b,
    #[display(fmt = "r11")]
    R11,
    #[display(fmt = "r11b")]
    R11b,
    #[display(fmt = "r12")]
    R12,
    #[display(fmt = "r12b")]
    R12b,
    #[display(fmt = "r13")]
    R13,
    #[display(fmt = "r13b")]
    R13b,
    #[display(fmt = "r14")]
    R14,
    #[display(fmt = "r14b")]
    R14b,
    #[display(fmt = "r15")]
    R15,
    #[display(fmt = "r15b")]
    R15b,
    #[display(fmt = "rax")]
    Rax,
    #[display(fmt = "al")]
    Al,
    #[display(fmt = "rbx")]
    Rbx,
    #[display(fmt = "bl")]
    Bl,
    #[display(fmt = "rcx")]
    Rcx,
    #[display(fmt = "cl")]
    Cl,
    #[display(fmt = "rdx")]
    Rdx,
    #[display(fmt = "dl")]
    Dl,
    #[display(fmt = "rdi")]
    Rdi,
    #[display(fmt = "dil")]
    Dil,
    #[display(fmt = "rsi")]
    Rsi,
    #[display(fmt = "sil")]
    Sil,
}

impl Register {
    fn to_byte_reg(self) -> Self {
        match self {
            Register::R8 => Register::R8b,
            Register::R9 => Register::R9b,
            Register::R10 => Register::R10b,
            Register::R11 => Register::R11b,
            Register::R12 => Register::R12b,
            Register::R13 => Register::R13b,
            Register::R14 => Register::R14b,
            Register::R15 => Register::R15b,
            Register::Rax => Register::Al,
            Register::Rbx => Register::Bl,
            Register::Rcx => Register::Cl,
            Register::Rdx => Register::Dl,
            Register::Rdi => Register::Dil,
            Register::Rsi => Register::Sil,
            _ => panic!("ICE: Cannot get byte version of {:?}", self),
        }
    }
}

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

#[derive(Debug)]
enum InstructionPart {
    Literal(Cow<'static, str>),
    DynamicRegister { reg_id: usize, is_byte: bool },
    FixedRegister(Register),
}

#[derive(Debug)]
enum AsmInstruction {
    RegAllocDynamicPop(usize),
    RegAllocFixedPop(Register),
    RegAllocDynamicNop(usize),
    RegAllocDynamicLiteral(usize, Cow<'static, str>),
    RegAllocFixedLiteral(Register, Cow<'static, str>),
    RegFreeDynamic { reg_id: usize, push: bool },
    RegFreeFixed { reg_id: Register, push: bool },
    Instruction(Vec<InstructionPart>),
}

impl AsmInstruction {
    fn render(
        &self,
        out_file: &mut BufWriter<File>,
        allocator: &mut RegisterAllocator,
        map: &mut HashMap<usize, Register>,
    ) -> Result<()> {
        match self {
            AsmInstruction::RegAllocDynamicNop(reg_id) => {
                let reg = match allocator.allocate() {
                    Some(reg) => reg,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                map.insert(*reg_id, reg);
            }
            AsmInstruction::RegAllocDynamicPop(reg_id) => {
                let reg = match allocator.allocate() {
                    Some(reg) => reg,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                map.insert(*reg_id, reg);
                writeln!(out_file, "    pop {}", reg)?;
            }
            AsmInstruction::RegAllocFixedPop(reg) => {
                writeln!(out_file, "    pop {}", reg)?;
            }
            AsmInstruction::RegAllocDynamicLiteral(reg_id, literal) => {
                let reg = match allocator.allocate() {
                    Some(reg) => reg,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                map.insert(*reg_id, reg);
                writeln!(out_file, "    mov {}, {}", reg, literal)?;
            }
            AsmInstruction::RegAllocFixedLiteral(reg, literal) => {
                writeln!(out_file, "    mov {}, {}", reg, literal)?;
            }
            AsmInstruction::RegFreeDynamic { reg_id, push } => {
                let reg = map
                    .remove(reg_id)
                    .expect("ICE: Attempted to remove unallocated register");
                if *push {
                    writeln!(out_file, "    push {}", reg)?;
                }
                allocator.free(reg);
            }
            AsmInstruction::RegFreeFixed { reg_id, push } => {
                if *push {
                    writeln!(out_file, "    push {}", reg_id)?;
                }
            }
            AsmInstruction::Instruction(parts) => {
                for part in parts {
                    match part {
                        InstructionPart::Literal(lit) => out_file.write_all(lit.as_bytes())?,
                        InstructionPart::DynamicRegister { reg_id, is_byte } => {
                            let mut reg = *map
                                .get(reg_id)
                                .expect("ICE: Attempted to fetch unallocated register");
                            if *is_byte {
                                reg = reg.to_byte_reg();
                            }
                            write!(out_file, "{}", reg)?;
                        }
                        InstructionPart::FixedRegister(reg) => {
                            write!(out_file, "{}", reg)?;
                        }
                    }
                }

                writeln!(out_file)?;
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
struct Assembly {
    asm: AsmInstruction,
    op_range: Range<usize>,
}

impl Assembly {
    fn new(asm: AsmInstruction, range: OpRange) -> Self {
        Self {
            asm,
            op_range: range.start..range.end,
        }
    }
}

#[derive(Debug, Clone, Copy)]
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
    use AsmInstruction::*;
    use InstructionPart::{DynamicRegister, FixedRegister};

    let mut assembly = Vec::new();
    let mut register_id = 0;
    let mut next_register = || {
        let new_id = register_id;
        register_id += 1;
        new_id
    };

    let dyn_reg = |reg_id| DynamicRegister {
        reg_id,
        is_byte: false,
    };
    let dyn_byte_reg = |reg_id| DynamicRegister {
        reg_id,
        is_byte: true,
    };

    let str_lit = |lit: &'static str| InstructionPart::Literal(lit.into());
    let string_lit = |lit: String| InstructionPart::Literal(lit.into());

    let dyn_free_push = |id| RegFreeDynamic {
        reg_id: id,
        push: true,
    };
    let dyn_free_drop = |id| RegFreeDynamic {
        reg_id: id,
        push: false,
    };
    let fixed_free_push = |id| RegFreeFixed {
        reg_id: id,
        push: true,
    };
    let fixed_free_drop = |id| RegFreeFixed {
        reg_id: id,
        push: false,
    };

    for (ip, op) in program.iter().enumerate() {
        let op_range = OpRange {
            start: ip,
            end: ip + 1,
        };

        let mut push_asm = |asm| assembly.push(Assembly::new(asm, op_range));
        match op.code {
            OpCode::Add | OpCode::Subtract | OpCode::BitOr | OpCode::BitAnd => {
                let a_id = next_register();
                let b_id = next_register();
                push_asm(RegAllocDynamicPop(b_id));
                push_asm(RegAllocDynamicPop(a_id));
                let op_asm = Instruction(vec![
                    str_lit(op.code.compile_arithmetic_op()),
                    dyn_reg(a_id),
                    str_lit(", "),
                    dyn_reg(b_id),
                ]);
                push_asm(op_asm);
                push_asm(dyn_free_drop(b_id));
                push_asm(dyn_free_push(a_id));
            }
            OpCode::ShiftLeft | OpCode::ShiftRight => {
                let a_id = next_register();
                push_asm(RegAllocFixedPop(Register::Rcx));
                push_asm(RegAllocDynamicPop(a_id));
                let op_asm = Instruction(vec![
                    str_lit(op.code.compile_arithmetic_op()),
                    dyn_reg(a_id),
                    str_lit(", "),
                    FixedRegister(Register::Cl),
                ]);
                push_asm(op_asm);
                push_asm(fixed_free_drop(Register::Rcx));
                push_asm(dyn_free_push(a_id));
            }
            OpCode::DivMod => {
                let divisor_reg = next_register();

                push_asm(RegAllocDynamicPop(divisor_reg));
                push_asm(RegAllocFixedPop(Register::Rax));
                push_asm(RegAllocFixedLiteral(Register::Rdx, "0".into()));

                push_asm(Instruction(vec![str_lit("    div "), dyn_reg(divisor_reg)]));

                push_asm(dyn_free_drop(divisor_reg));
                push_asm(fixed_free_push(Register::Rax));
                push_asm(fixed_free_push(Register::Rdx));
            }
            OpCode::Multiply => {
                let mult_reg = next_register();

                push_asm(RegAllocFixedPop(Register::Rax));
                push_asm(RegAllocFixedLiteral(Register::Rdx, "0".into()));
                push_asm(RegAllocDynamicPop(mult_reg));

                push_asm(Instruction(vec![str_lit("    mul "), dyn_reg(mult_reg)]));

                push_asm(dyn_free_drop(mult_reg));
                push_asm(fixed_free_drop(Register::Rdx));
                push_asm(fixed_free_push(Register::Rax));
            }

            OpCode::Equal
            | OpCode::NotEq
            | OpCode::Less
            | OpCode::LessEqual
            | OpCode::Greater
            | OpCode::GreaterEqual => {
                let a_id = next_register();
                let b_id = next_register();
                let dst_id = next_register();
                push_asm(RegAllocDynamicPop(b_id));
                push_asm(RegAllocDynamicPop(a_id));
                push_asm(RegAllocDynamicLiteral(dst_id, "0".into()));

                let op_asm = Instruction(vec![
                    str_lit("    cmp "),
                    dyn_reg(a_id),
                    str_lit(", "),
                    dyn_reg(b_id),
                ]);
                push_asm(op_asm);

                let set_asm = Instruction(vec![
                    string_lit(format!("    set{} ", op.code.compile_compare_op_suffix())),
                    dyn_byte_reg(dst_id),
                ]);
                push_asm(set_asm);

                push_asm(dyn_free_drop(b_id));
                push_asm(dyn_free_drop(a_id));
                push_asm(dyn_free_push(dst_id));
            }

            OpCode::ArgC => push_asm(Instruction(vec![str_lit("    push QWORD [__argc]")])),
            OpCode::ArgV => push_asm(Instruction(vec![str_lit("    push QWORD [__argv]")])),
            OpCode::PushBool(val) => {
                let reg = next_register();
                push_asm(RegAllocDynamicLiteral(reg, (val as u64).to_string().into()));
                push_asm(dyn_free_push(reg));
            }
            OpCode::PushInt(val) => {
                let reg = next_register();
                push_asm(RegAllocDynamicLiteral(reg, val.to_string().into()));
                push_asm(dyn_free_push(reg));
            }
            OpCode::PushStr(id) => {
                let literal = interner.resolve_literal(id);
                let id = id.into_inner().get();
                let len_reg = next_register();
                let ptr_reg = next_register();

                push_asm(RegAllocDynamicLiteral(
                    len_reg,
                    literal.len().to_string().into(),
                ));
                push_asm(RegAllocDynamicLiteral(
                    ptr_reg,
                    format!("__string_literal{}", id).into(),
                ));
                push_asm(dyn_free_push(len_reg));
                push_asm(dyn_free_push(ptr_reg));
            }
            OpCode::Mem { offset } => {
                let reg = next_register();
                push_asm(RegAllocDynamicLiteral(
                    reg,
                    format!("__memory + {}", offset).into(),
                ));
                push_asm(dyn_free_push(reg));
            }

            OpCode::Drop => {
                push_asm(Instruction(vec![str_lit("    add rsp, 8")]));
            }
            OpCode::Dup { depth } => {
                let reg = next_register();
                push_asm(RegAllocDynamicLiteral(
                    reg,
                    format!("QWORD [rsp + 8*{}]", depth).into(),
                ));
                push_asm(dyn_free_push(reg));
            }
            OpCode::DupPair => {
                let reg_top = next_register();
                let reg_lower = next_register();
                push_asm(RegAllocDynamicLiteral(reg_top, "QWORD [rsp]".into()));
                push_asm(RegAllocDynamicLiteral(reg_lower, "QWORD [rsp+8]".into()));
                push_asm(dyn_free_push(reg_lower));
                push_asm(dyn_free_push(reg_top));
            }
            OpCode::Print => {
                push_asm(RegAllocFixedPop(Register::Rdi));
                push_asm(Instruction(vec![str_lit("    call dump")]));
                push_asm(fixed_free_drop(Register::Rdi));
            }
            OpCode::Rot => {
                let a_reg = next_register();
                let b_reg = next_register();
                let c_reg = next_register();

                push_asm(RegAllocDynamicPop(a_reg));
                push_asm(RegAllocDynamicPop(b_reg));
                push_asm(RegAllocDynamicPop(c_reg));

                push_asm(dyn_free_push(b_reg));
                push_asm(dyn_free_push(a_reg));
                push_asm(dyn_free_push(c_reg));
            }
            OpCode::Swap => {
                let a_id = next_register();
                let b_id = next_register();
                push_asm(RegAllocDynamicPop(a_id));
                push_asm(RegAllocDynamicPop(b_id));
                push_asm(dyn_free_push(a_id));
                push_asm(dyn_free_push(b_id));
            }

            OpCode::Load => {
                let val_reg = next_register();
                let addr_reg = next_register();

                push_asm(RegAllocDynamicPop(addr_reg));
                push_asm(RegAllocDynamicLiteral(val_reg, "0".into()));

                push_asm(Instruction(vec![
                    str_lit("    mov "),
                    dyn_byte_reg(val_reg),
                    str_lit(", BYTE ["),
                    dyn_reg(addr_reg),
                    str_lit("]"),
                ]));

                push_asm(dyn_free_drop(addr_reg));
                push_asm(dyn_free_push(val_reg));
            }
            OpCode::Load64 => {
                let addr_reg = next_register();
                let val_reg = next_register();

                push_asm(RegAllocDynamicPop(addr_reg));
                push_asm(RegAllocDynamicNop(val_reg));

                push_asm(Instruction(vec![
                    str_lit("    mov "),
                    dyn_reg(val_reg),
                    str_lit(", QWORD ["),
                    dyn_reg(addr_reg),
                    str_lit("]"),
                ]));

                push_asm(dyn_free_drop(addr_reg));
                push_asm(dyn_free_push(val_reg));
            }
            OpCode::Store { forth_style } => {
                let val_reg = next_register();
                let addr_reg = next_register();
                if forth_style {
                    push_asm(RegAllocDynamicPop(addr_reg));
                    push_asm(RegAllocDynamicPop(val_reg));
                } else {
                    push_asm(RegAllocDynamicPop(val_reg));
                    push_asm(RegAllocDynamicPop(addr_reg));
                }
                push_asm(Instruction(vec![
                    str_lit("    mov BYTE ["),
                    dyn_reg(addr_reg),
                    str_lit("], "),
                    dyn_byte_reg(val_reg),
                ]));

                push_asm(dyn_free_drop(val_reg));
                push_asm(dyn_free_drop(addr_reg));
            }
            OpCode::Store64 { forth_style } => {
                let val_reg = next_register();
                let addr_reg = next_register();
                if forth_style {
                    push_asm(RegAllocDynamicPop(addr_reg));
                    push_asm(RegAllocDynamicPop(val_reg));
                } else {
                    push_asm(RegAllocDynamicPop(val_reg));
                    push_asm(RegAllocDynamicPop(addr_reg));
                }
                push_asm(Instruction(vec![
                    str_lit("    mov QWORD ["),
                    dyn_reg(addr_reg),
                    str_lit("], "),
                    dyn_reg(val_reg),
                ]));

                push_asm(dyn_free_drop(val_reg));
                push_asm(dyn_free_drop(addr_reg));
            }

            OpCode::DoWhile { end_ip, .. } | OpCode::DoIf { end_ip, .. } => {
                let reg_id = next_register();
                push_asm(RegAllocDynamicPop(reg_id));

                push_asm(Instruction(vec![
                    str_lit("    test "),
                    dyn_reg(reg_id),
                    str_lit(", "),
                    dyn_reg(reg_id),
                ]));
                push_asm(Instruction(vec![string_lit(format!(
                    "    jz .LBL{}",
                    end_ip
                ))]));

                push_asm(dyn_free_drop(reg_id));
            }
            OpCode::While { ip } => {
                push_asm(Instruction(vec![string_lit(format!(".LBL{}:", ip))]));
            }
            OpCode::EndWhile {
                condition_ip,
                end_ip,
            } => {
                push_asm(Instruction(vec![string_lit(format!(
                    "    jmp .LBL{}",
                    condition_ip
                ))]));
                push_asm(Instruction(vec![string_lit(format!(".LBL{}:", end_ip))]));
            }

            OpCode::If => {}
            OpCode::Elif { end_ip, else_start } | OpCode::Else { end_ip, else_start } => {
                push_asm(Instruction(vec![string_lit(format!(
                    "    jmp .LBL{}",
                    end_ip
                ))]));
                push_asm(Instruction(vec![string_lit(format!(
                    ".LBL{}:",
                    else_start
                ))]));
            }
            OpCode::EndIf { ip } => {
                push_asm(Instruction(vec![string_lit(format!(".LBL{}:", ip))]));
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
                    push_asm(RegAllocFixedPop(reg));
                }

                push_asm(Instruction(vec![str_lit("    syscall")]));

                for &reg in &regs[1..=a] {
                    push_asm(fixed_free_drop(reg));
                }
                push_asm(fixed_free_push(Register::Rax));
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

    assembly
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
