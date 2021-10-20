use std::{collections::HashMap, fs::File, io::BufWriter, io::Write, ops::Range, path::Path};

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
    #[display(fmt = "r11")]
    R11,
    #[display(fmt = "r12")]
    R12,
    #[display(fmt = "r13")]
    R13,
    #[display(fmt = "r14")]
    R14,
    #[display(fmt = "r15")]
    R15,
    #[display(fmt = "rax")]
    Rax,
    #[display(fmt = "rbx")]
    Rbx,
    #[display(fmt = "rcx")]
    Rcx,
    #[display(fmt = "rdx")]
    Rdx,
    #[display(fmt = "rdi")]
    Rdi,
}

#[derive(Debug)]
struct RegisterAllocator {
    available_registers: Vec<Register>,
}

impl RegisterAllocator {
    fn new() -> Self {
        Self {
            available_registers: vec![
                Register::R11,
                Register::R12,
                Register::R13,
                Register::R14,
                Register::R15,
            ],
        }
    }

    fn allocate(&mut self) -> Register {
        self.available_registers
            .pop()
            .expect("ICE: Register exhaustion")
    }

    fn free(&mut self, reg: Register) {
        self.available_registers.push(reg);
    }
}

#[derive(Debug)]
enum InstructionPart {
    Literal(&'static str),
    DynamicRegister(usize),
    FixedRegister(Register),
}

#[derive(Debug)]
enum AsmInstruction {
    RegAllocDynamicPop(usize),
    RegAllocFixedPop(Register),
    RegAllocDynamicLiteral(usize, String),
    RegAllocFixedLiteral(Register, String),
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
            AsmInstruction::RegAllocDynamicPop(reg_id) => {
                let reg = allocator.allocate();
                map.insert(*reg_id, reg);
                writeln!(out_file, "    pop {}", reg)?;
            }
            AsmInstruction::RegAllocFixedPop(reg) => {
                writeln!(out_file, "    pop {}", reg)?;
            }
            AsmInstruction::RegAllocDynamicLiteral(reg_id, literal) => {
                let reg = allocator.allocate();
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
                allocator.free(reg);
                if *push {
                    writeln!(out_file, "    push {}", reg)?;
                }
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
                        InstructionPart::DynamicRegister(reg_id) => {
                            let reg = map
                                .get(reg_id)
                                .expect("ICE: Attempted to fetch unallocated register");
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
}

fn build_assembly(program: &[Op], interner: &Interners) -> Vec<Assembly> {
    use AsmInstruction::*;
    use InstructionPart::*;

    let mut assembly = Vec::new();
    let mut register_id = 0;
    let mut next_register = || {
        let new_id = register_id;
        register_id += 1;
        new_id
    };

    let mut push_asm = |asm, op_range| assembly.push(Assembly::new(asm, op_range));

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

        match op.code {
            OpCode::Add | OpCode::Subtract | OpCode::BitOr | OpCode::BitAnd => {
                let a_id = next_register();
                push_asm(RegAllocDynamicPop(a_id), op_range);
                let b_id = next_register();
                push_asm(RegAllocDynamicPop(b_id), op_range);
                let add_asm = Instruction(vec![
                    Literal(op.code.compile_arithmetic_op()),
                    DynamicRegister(a_id),
                    Literal(", "),
                    DynamicRegister(b_id),
                ]);
                push_asm(add_asm, op_range);
                push_asm(dyn_free_drop(b_id), op_range);
                push_asm(dyn_free_push(a_id), op_range);
            }
            OpCode::ShiftLeft => todo!(),
            OpCode::ShiftRight => todo!(),
            OpCode::DivMod => todo!(),
            OpCode::Multiply => todo!(),

            OpCode::Equal => todo!(),
            OpCode::NotEq => todo!(),
            OpCode::Less => todo!(),
            OpCode::LessEqual => todo!(),
            OpCode::Greater => todo!(),
            OpCode::GreaterEqual => todo!(),

            OpCode::ArgC => todo!(),
            OpCode::ArgV => todo!(),
            OpCode::PushBool(val) => {
                let reg = next_register();
                push_asm(
                    RegAllocDynamicLiteral(reg, (val as u64).to_string()),
                    op_range,
                );
                push_asm(dyn_free_push(reg), op_range);
            }
            OpCode::PushInt(val) => {
                let reg = next_register();
                push_asm(RegAllocDynamicLiteral(reg, val.to_string()), op_range);
                push_asm(dyn_free_push(reg), op_range);
            }
            OpCode::PushStr(id) => {
                let literal = interner.resolve_literal(id);
                let id = id.into_inner().get();
                let len_reg = next_register();
                let ptr_reg = next_register();

                push_asm(
                    RegAllocDynamicLiteral(len_reg, literal.len().to_string()),
                    op_range,
                );
                push_asm(
                    RegAllocDynamicLiteral(ptr_reg, format!("__string_literal{}", id)),
                    op_range,
                );
                push_asm(dyn_free_push(len_reg), op_range);
                push_asm(dyn_free_push(ptr_reg), op_range);
            }
            OpCode::Mem { .. } => todo!(),

            OpCode::Drop => {
                let reg = next_register();
                push_asm(RegAllocDynamicPop(reg), op_range);
                push_asm(dyn_free_drop(reg), op_range);
            }
            OpCode::Dup { depth } => {
                let reg = next_register();
                push_asm(
                    RegAllocDynamicLiteral(reg, format!("QWORD [rsp + 8*{}]", depth)),
                    op_range,
                );
                push_asm(dyn_free_push(reg), op_range);
            }
            OpCode::DupPair => {
                let reg_top = next_register();
                let reg_lower = next_register();
                push_asm(
                    RegAllocDynamicLiteral(reg_top, "QWORD [rsp]".to_owned()),
                    op_range,
                );
                push_asm(
                    RegAllocDynamicLiteral(reg_lower, "QWORD [rsp+8]".to_owned()),
                    op_range,
                );
                push_asm(dyn_free_push(reg_lower), op_range);
                push_asm(dyn_free_push(reg_top), op_range);
            }
            OpCode::Print => {
                push_asm(RegAllocFixedPop(Register::Rdi), op_range);
                push_asm(Instruction(vec![Literal("    call dump")]), op_range);
                push_asm(fixed_free_drop(Register::Rdi), op_range);
            }
            OpCode::Rot => todo!(),
            OpCode::Swap => todo!(),

            OpCode::Load => todo!(),
            OpCode::Load64 => todo!(),
            OpCode::Store { .. } => todo!(),
            OpCode::Store64 { .. } => todo!(),

            OpCode::While { .. } => todo!(),
            OpCode::DoWhile { .. } => todo!(),
            OpCode::EndWhile { .. } => todo!(),

            OpCode::If => todo!(),
            OpCode::Elif { .. } => todo!(),
            OpCode::DoIf { .. } => todo!(),
            OpCode::Else { .. } => todo!(),
            OpCode::EndIf { .. } => todo!(),

            OpCode::SysCall(0..=6) => todo!(),

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
