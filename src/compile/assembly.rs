use std::{
    borrow::Cow,
    collections::HashMap,
    fs::File,
    io::{BufWriter, Write},
    ops::Range,
};

use color_eyre::eyre::Result;

use crate::Width;

use super::{OpRange, RegisterAllocator};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum X86Register {
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    Rax,
    Rbx,
    Rcx,
    Rdx,
    Rdi,
    Rsi,
}

impl X86Register {
    pub(super) fn as_width(self, width: Width) -> &'static str {
        match (self, width) {
            (X86Register::R8, Width::Byte) => "r8b",
            (X86Register::R8, Width::Word) => "r8w",
            (X86Register::R8, Width::Dword) => "r8d",
            (X86Register::R8, Width::Qword) => "r8",

            (X86Register::R9, Width::Byte) => "r9b",
            (X86Register::R9, Width::Word) => "r9w",
            (X86Register::R9, Width::Dword) => "r9d",
            (X86Register::R9, Width::Qword) => "r9",

            (X86Register::R10, Width::Byte) => "r10b",
            (X86Register::R10, Width::Word) => "r10w",
            (X86Register::R10, Width::Dword) => "r10d",
            (X86Register::R10, Width::Qword) => "r10",

            (X86Register::R11, Width::Byte) => "r11b",
            (X86Register::R11, Width::Word) => "r11w",
            (X86Register::R11, Width::Dword) => "r11d",
            (X86Register::R11, Width::Qword) => "r11",

            (X86Register::R12, Width::Byte) => "r12b",
            (X86Register::R12, Width::Word) => "r12w",
            (X86Register::R12, Width::Dword) => "r12d",
            (X86Register::R12, Width::Qword) => "r12",

            (X86Register::R13, Width::Byte) => "r13b",
            (X86Register::R13, Width::Word) => "r13w",
            (X86Register::R13, Width::Dword) => "r13d",
            (X86Register::R13, Width::Qword) => "r13",

            (X86Register::R14, Width::Byte) => "r14b",
            (X86Register::R14, Width::Word) => "r14w",
            (X86Register::R14, Width::Dword) => "r14d",
            (X86Register::R14, Width::Qword) => "r14",

            (X86Register::R15, Width::Byte) => "r15b",
            (X86Register::R15, Width::Word) => "r15w",
            (X86Register::R15, Width::Dword) => "r15d",
            (X86Register::R15, Width::Qword) => "r15",

            (X86Register::Rax, Width::Byte) => "al",
            (X86Register::Rax, Width::Word) => "ax",
            (X86Register::Rax, Width::Dword) => "eax",
            (X86Register::Rax, Width::Qword) => "rax",

            (X86Register::Rbx, Width::Byte) => "bl",
            (X86Register::Rbx, Width::Word) => "bx",
            (X86Register::Rbx, Width::Dword) => "ebx",
            (X86Register::Rbx, Width::Qword) => "rbx",

            (X86Register::Rcx, Width::Byte) => "cl",
            (X86Register::Rcx, Width::Word) => "cx",
            (X86Register::Rcx, Width::Dword) => "ecx",
            (X86Register::Rcx, Width::Qword) => "rcx",

            (X86Register::Rdx, Width::Byte) => "dl",
            (X86Register::Rdx, Width::Word) => "dx",
            (X86Register::Rdx, Width::Dword) => "edx",
            (X86Register::Rdx, Width::Qword) => "rdx",

            (X86Register::Rdi, Width::Byte) => "dil",
            (X86Register::Rdi, Width::Word) => "di",
            (X86Register::Rdi, Width::Dword) => "edi",
            (X86Register::Rdi, Width::Qword) => "rdi",

            (X86Register::Rsi, Width::Byte) => "sil",
            (X86Register::Rsi, Width::Word) => "si",
            (X86Register::Rsi, Width::Dword) => "esi",
            (X86Register::Rsi, Width::Qword) => "rsi",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegisterType {
    Dynamic(usize),
    Fixed(X86Register),
}

#[derive(Debug)]
pub enum InstructionPart {
    Literal(Cow<'static, str>),
    /// Used to actually emit a register as part of an instruction.
    EmitRegister {
        reg: RegisterType,
        width: Width,
    },
    /// Marks a register as used for the allocation optimizer, but doesn't emit anything when rendered.
    UseRegister {
        reg: RegisterType,
    },
}

#[derive(Debug)]
pub enum AsmInstruction {
    RegAllocPop {
        reg: RegisterType,
    },
    RegAllocNop {
        reg: RegisterType,
    },
    RegAllocDup {
        reg: RegisterType,
        depth: usize,
    },
    RegAllocLiteral {
        reg: RegisterType,
        value: Cow<'static, str>,
    },
    RegAllocMov {
        src: RegisterType,
        dst: RegisterType,
    },
    RegFree {
        reg: RegisterType,
        push: bool,
    },
    Instruction(Vec<InstructionPart>),
    /// Designates a boundry that stops the allocation optimizer's search.
    BlockBoundry,
    Nop,
}

impl AsmInstruction {
    pub(super) fn render(
        &self,
        out_file: &mut BufWriter<File>,
        allocator: &mut RegisterAllocator,
        map: &mut HashMap<usize, X86Register>,
    ) -> Result<()> {
        use RegisterType::*;
        match self {
            &AsmInstruction::RegAllocNop {
                reg: Dynamic(reg_id),
            } => {
                let reg = match allocator.allocate() {
                    Some(reg) => reg,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                eprintln!("Reg Allocate Nop {} > {:?}", reg_id, reg);
                map.insert(reg_id, reg);
            }
            &AsmInstruction::RegAllocDup {
                reg: Dynamic(reg_id),
                depth,
            } => {
                let reg = match allocator.allocate() {
                    Some(reg) => reg,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                eprintln!("Reg Allocate Dup({}) {} > {:?}", depth, reg_id, reg);
                map.insert(reg_id, reg);
                writeln!(
                    out_file,
                    "    mov {}, QWORD [rsp + 8*{}]",
                    reg.as_width(Width::Qword),
                    depth
                )?;
            }
            &AsmInstruction::RegAllocPop {
                reg: Dynamic(reg_id),
            } => {
                let reg = match allocator.allocate() {
                    Some(reg) => reg,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                eprintln!("Reg Allocate Pop {} > {:?}", reg_id, reg);
                map.insert(reg_id, reg);
                writeln!(out_file, "    pop {}", reg.as_width(Width::Qword))?;
            }
            AsmInstruction::RegAllocLiteral {
                reg: Dynamic(reg_id),
                value,
            } => {
                let reg = match allocator.allocate() {
                    Some(reg) => reg,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                eprintln!("Reg Allocate Lit {} > {:?}", reg_id, reg);
                map.insert(*reg_id, reg);
                writeln!(
                    out_file,
                    "    mov {}, {}",
                    reg.as_width(Width::Qword),
                    value
                )?;
            }
            &AsmInstruction::RegAllocDup {
                reg: Fixed(reg),
                depth,
            } => {
                writeln!(
                    out_file,
                    "    mov {}, QWORD [rsp + 8*{}]",
                    reg.as_width(Width::Qword),
                    depth
                )?;
            }
            AsmInstruction::RegAllocNop { .. } => {}
            &AsmInstruction::RegAllocPop { reg: Fixed(reg) } => {
                writeln!(out_file, "    pop {}", reg.as_width(Width::Qword))?;
            }
            AsmInstruction::RegAllocLiteral {
                reg: Fixed(reg),
                value,
            } => {
                writeln!(
                    out_file,
                    "    mov {}, {}",
                    reg.as_width(Width::Qword),
                    value
                )?;
            }

            &AsmInstruction::RegAllocMov {
                src: Dynamic(src_id),
                dst: Dynamic(dst_id),
            } => {
                let (src_reg, dst_reg) = match allocator.allocate().zip(allocator.allocate()) {
                    Some(regs) => regs,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                eprintln!(
                    "Reg Allocate Mov Src {} > {}, Dst {} > {}",
                    src_id,
                    src_reg.as_width(Width::Qword),
                    dst_id,
                    dst_reg.as_width(Width::Qword)
                );
                map.insert(src_id, src_reg);
                map.insert(dst_id, dst_reg);
                writeln!(
                    out_file,
                    "    mov {}, {}",
                    dst_reg.as_width(Width::Qword),
                    src_reg.as_width(Width::Qword)
                )?;
            }
            &AsmInstruction::RegAllocMov {
                src: Dynamic(src_id),
                dst: Fixed(dst_reg),
            } => {
                let src_reg = match allocator.allocate() {
                    Some(regs) => regs,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                eprintln!(
                    "Reg Allocate Mov Src {} > {}, Dst {}",
                    src_id,
                    src_reg.as_width(Width::Qword),
                    dst_reg.as_width(Width::Qword)
                );
                map.insert(src_id, src_reg);
                writeln!(
                    out_file,
                    "    mov {}, {}",
                    dst_reg.as_width(Width::Qword),
                    src_reg.as_width(Width::Qword)
                )?;
            }
            &AsmInstruction::RegAllocMov {
                src: Fixed(src_reg),
                dst: Dynamic(dst_id),
            } => {
                let dst_reg = match allocator.allocate() {
                    Some(regs) => regs,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                eprintln!(
                    "Reg Allocate Mov Src {}, Dst {} > {}",
                    src_reg.as_width(Width::Qword),
                    dst_id,
                    dst_reg.as_width(Width::Qword)
                );
                map.insert(dst_id, dst_reg);
                writeln!(
                    out_file,
                    "    mov {}, {}",
                    dst_reg.as_width(Width::Qword),
                    src_reg.as_width(Width::Qword)
                )?;
            }
            &AsmInstruction::RegAllocMov {
                src: Fixed(src_reg),
                dst: Fixed(dst_reg),
            } => {
                eprintln!(
                    "Reg Allocate Mov Src {}, Dst {}",
                    src_reg.as_width(Width::Qword),
                    dst_reg.as_width(Width::Qword)
                );
                writeln!(
                    out_file,
                    "    mov {}, {}",
                    dst_reg.as_width(Width::Qword),
                    src_reg.as_width(Width::Qword)
                )?;
            }

            &AsmInstruction::RegFree {
                reg: Dynamic(reg_id),
                push,
            } => {
                let reg = map
                    .remove(&reg_id)
                    .expect("ICE: Attempted to remove unallocated register");

                let kind = if push {
                    writeln!(out_file, "    push {}", reg.as_width(Width::Qword))?;
                    "Push"
                } else {
                    "Drop"
                };
                eprintln!("Reg Free {} {} > {:?}", kind, reg_id, reg);
                allocator.free(reg);
            }
            &AsmInstruction::RegFree {
                reg: Fixed(reg_id),
                push,
            } => {
                if push {
                    writeln!(out_file, "    push {}", reg_id.as_width(Width::Qword))?;
                }
            }

            AsmInstruction::Instruction(parts) => {
                for part in parts {
                    match part {
                        InstructionPart::Literal(lit) => out_file.write_all(lit.as_bytes())?,
                        &InstructionPart::EmitRegister {
                            reg: RegisterType::Dynamic(reg_id),
                            width,
                        } => {
                            let reg = *map.get(&reg_id).unwrap_or_else(|| {
                                panic!("ICE: Attempted to fetch unallocated register {}", reg_id)
                            });
                            write!(out_file, "{}", reg.as_width(width))?;
                        }
                        &InstructionPart::EmitRegister {
                            reg: RegisterType::Fixed(reg),
                            width,
                        } => {
                            write!(out_file, "{}", reg.as_width(width))?;
                        }
                        InstructionPart::UseRegister { .. } => {}
                    }
                }

                writeln!(out_file)?;
            }
            AsmInstruction::BlockBoundry | AsmInstruction::Nop => {}
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct Assembly {
    pub asm: AsmInstruction,
    pub op_range: Range<usize>,
    pub merged_range: Range<usize>,
}

impl Assembly {
    fn new(asm: AsmInstruction, range: OpRange) -> Self {
        Self {
            asm,
            op_range: range.start..range.end,
            merged_range: range.start..range.end,
        }
    }
}

#[derive(Debug, Default)]
pub struct Assembler {
    assembly: Vec<Assembly>,
    register_id: usize,
    op_range: OpRange,
}

impl Assembler {
    fn next_register(&mut self) -> usize {
        self.register_id += 1;
        self.register_id
    }

    pub fn into_assembly(self) -> Vec<Assembly> {
        self.assembly
    }

    pub fn block_boundry(&mut self) {
        self.assembly
            .push(Assembly::new(AsmInstruction::BlockBoundry, self.op_range));
    }

    pub fn set_op_range(&mut self, start: usize, end: usize) {
        self.op_range = OpRange { start, end };
    }

    pub fn push_instr(&mut self, instr: impl Into<Vec<InstructionPart>>) {
        let asm = AsmInstruction::Instruction(instr.into());
        self.assembly.push(Assembly::new(asm, self.op_range));
    }

    pub fn reg_alloc_dyn_pop(&mut self) -> usize {
        let id = self.next_register();
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocPop {
                reg: RegisterType::Dynamic(id),
            },
            self.op_range,
        ));
        id
    }

    pub fn reg_alloc_dyn_nop(&mut self) -> usize {
        let id = self.next_register();
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocNop {
                reg: RegisterType::Dynamic(id),
            },
            self.op_range,
        ));
        id
    }

    pub fn reg_alloc_dyn_dup(&mut self, depth: usize) -> usize {
        let id = self.next_register();
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocDup {
                depth,
                reg: RegisterType::Dynamic(id),
            },
            self.op_range,
        ));
        id
    }

    pub fn reg_alloc_dyn_literal(&mut self, value: impl Into<Cow<'static, str>>) -> usize {
        let id = self.next_register();
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocLiteral {
                reg: RegisterType::Dynamic(id),
                value: value.into(),
            },
            self.op_range,
        ));
        id
    }

    pub fn reg_alloc_fixed_pop(&mut self, reg: X86Register) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocPop {
                reg: RegisterType::Fixed(reg),
            },
            self.op_range,
        ));
    }

    pub fn reg_alloc_fixed_nop(&mut self, reg: X86Register) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocNop {
                reg: RegisterType::Fixed(reg),
            },
            self.op_range,
        ));
    }

    pub fn reg_alloc_fixed_literal(
        &mut self,
        reg: X86Register,
        value: impl Into<Cow<'static, str>>,
    ) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocLiteral {
                reg: RegisterType::Fixed(reg),
                value: value.into(),
            },
            self.op_range,
        ));
    }

    pub fn reg_free_dyn_push(&mut self, reg_id: usize) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegFree {
                reg: RegisterType::Dynamic(reg_id),
                push: true,
            },
            self.op_range,
        ));
    }

    pub fn reg_free_dyn_drop(&mut self, reg_id: usize) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegFree {
                reg: RegisterType::Dynamic(reg_id),
                push: false,
            },
            self.op_range,
        ));
    }

    pub fn reg_free_fixed_push(&mut self, reg_id: X86Register) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegFree {
                reg: RegisterType::Fixed(reg_id),
                push: true,
            },
            self.op_range,
        ));
    }

    pub fn reg_free_fixed_drop(&mut self, reg_id: X86Register) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegFree {
                reg: RegisterType::Fixed(reg_id),
                push: false,
            },
            self.op_range,
        ));
    }
}
