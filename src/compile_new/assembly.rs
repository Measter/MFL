use std::{
    borrow::Cow,
    collections::HashMap,
    fs::File,
    io::{BufWriter, Write},
    ops::Range,
};

use color_eyre::eyre::Result;
use derive_more::Display;

use super::{OpRange, RegisterAllocator};

#[derive(Debug, Clone, Copy, Display, Eq)]
pub enum X86Register {
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

impl PartialEq for X86Register {
    fn eq(&self, other: &Self) -> bool {
        use X86Register::*;
        match self {
            R8 | R8b => matches!(other, R8 | R8b),
            R9 | R9b => matches!(other, R9 | R9b),
            R10 | R10b => matches!(other, R10 | R10b),
            R11 | R11b => matches!(other, R11 | R11b),
            R12 | R12b => matches!(other, R12 | R12b),
            R13 | R13b => matches!(other, R13 | R13b),
            R14 | R14b => matches!(other, R14 | R14b),
            R15 | R15b => matches!(other, R15 | R15b),
            Rax | Al => matches!(other, Rax | Al),
            Rbx | Bl => matches!(other, Rbx | Bl),
            Rcx | Cl => matches!(other, Rcx | Cl),
            Rdx | Dl => matches!(other, Rdx | Dl),
            Rdi | Dil => matches!(other, Rdi | Dil),
            Rsi | Sil => matches!(other, Rsi | Sil),
        }
    }
}

impl X86Register {
    pub(super) fn to_byte_reg(self) -> Self {
        match self {
            X86Register::R8 => X86Register::R8b,
            X86Register::R9 => X86Register::R9b,
            X86Register::R10 => X86Register::R10b,
            X86Register::R11 => X86Register::R11b,
            X86Register::R12 => X86Register::R12b,
            X86Register::R13 => X86Register::R13b,
            X86Register::R14 => X86Register::R14b,
            X86Register::R15 => X86Register::R15b,
            X86Register::Rax => X86Register::Al,
            X86Register::Rbx => X86Register::Bl,
            X86Register::Rcx => X86Register::Cl,
            X86Register::Rdx => X86Register::Dl,
            X86Register::Rdi => X86Register::Dil,
            X86Register::Rsi => X86Register::Sil,
            _ => panic!("ICE: Cannot get byte version of {:?}", self),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum RegisterType {
    Dynamic(usize),
    Fixed(X86Register),
}

#[derive(Debug)]
pub enum InstructionPart {
    Literal(Cow<'static, str>),
    Register { reg: RegisterType, is_byte: bool },
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
                writeln!(out_file, "    mov {}, QWORD [rsp + 8*{}]", reg, depth)?;
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
                writeln!(out_file, "    pop {}", reg)?;
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
                writeln!(out_file, "    mov {}, {}", reg, value)?;
            }
            &AsmInstruction::RegAllocDup {
                reg: Fixed(reg),
                depth,
            } => {
                writeln!(out_file, "    mov {}, QWORD [rsp + 8*{}]", reg, depth)?;
            }
            AsmInstruction::RegAllocNop { .. } => {}
            &AsmInstruction::RegAllocPop { reg: Fixed(reg) } => {
                writeln!(out_file, "    pop {}", reg)?;
            }
            AsmInstruction::RegAllocLiteral {
                reg: Fixed(reg),
                value,
            } => {
                writeln!(out_file, "    mov {}, {}", reg, value)?;
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
                    src_id, src_reg, dst_id, dst_reg
                );
                map.insert(src_id, src_reg);
                map.insert(dst_id, dst_reg);
                writeln!(out_file, "    mov {}, {}", dst_reg, src_reg)?;
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
                    src_id, src_reg, dst_reg
                );
                map.insert(src_id, src_reg);
                writeln!(out_file, "    mov {}, {}", dst_reg, src_reg)?;
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
                    src_reg, dst_id, dst_reg
                );
                map.insert(dst_id, dst_reg);
                writeln!(out_file, "    mov {}, {}", dst_reg, src_reg)?;
            }
            &AsmInstruction::RegAllocMov {
                src: Fixed(src_reg),
                dst: Fixed(dst_reg),
            } => {
                eprintln!("Reg Allocate Mov Src {}, Dst {}", src_reg, dst_reg);
                writeln!(out_file, "    mov {}, {}", dst_reg, src_reg)?;
            }

            &AsmInstruction::RegFree {
                reg: Dynamic(reg_id),
                push,
            } => {
                let reg = map
                    .remove(&reg_id)
                    .expect("ICE: Attempted to remove unallocated register");

                let kind = if push {
                    writeln!(out_file, "    push {}", reg)?;
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
                    writeln!(out_file, "    push {}", reg_id)?;
                }
            }

            AsmInstruction::Instruction(parts) => {
                for part in parts {
                    match part {
                        InstructionPart::Literal(lit) => out_file.write_all(lit.as_bytes())?,
                        &InstructionPart::Register {
                            reg: RegisterType::Dynamic(reg_id),
                            is_byte,
                        } => {
                            let mut reg = *map.get(&reg_id).unwrap_or_else(|| {
                                panic!("ICE: Attempted to fetch unallocated register {}", reg_id)
                            });
                            if is_byte {
                                reg = reg.to_byte_reg();
                            }
                            write!(out_file, "{}", reg)?;
                        }
                        &InstructionPart::Register {
                            reg: RegisterType::Fixed(reg),
                            is_byte,
                        } => {
                            if is_byte {
                                write!(out_file, "{}", reg.to_byte_reg())?;
                            } else {
                                write!(out_file, "{}", reg)?;
                            }
                        }
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
