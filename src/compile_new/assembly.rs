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

#[derive(Debug, Clone, Copy, Display)]
pub enum Register {
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
pub enum InstructionPart {
    Literal(Cow<'static, str>),
    DynamicRegister { reg_id: usize, is_byte: bool },
    FixedRegister(Register),
}

#[derive(Debug)]
pub enum AsmInstruction {
    RegAllocDynamicPop(usize),
    RegAllocFixedPop(Register),
    RegAllocDynamicNop(usize),
    RegAllocDynamicDup { reg_id: usize, depth: usize },
    RegAllocDynamicLiteral(usize, Cow<'static, str>),
    RegAllocFixedLiteral(Register, Cow<'static, str>),
    RegFreeDynamic { reg_id: usize, push: bool },
    RegFreeFixed { reg_id: Register, push: bool },
    Instruction(Vec<InstructionPart>),
    BlockBoundry,
    Nop,
}

impl AsmInstruction {
    pub(super) fn render(
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
                eprintln!("Reg Allocate Nop {} > {:?}", reg_id, reg);
                map.insert(*reg_id, reg);
            }
            AsmInstruction::RegAllocDynamicDup { reg_id, depth } => {
                let reg = match allocator.allocate() {
                    Some(reg) => reg,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                eprintln!("Reg Allocate Dup({}) {} > {:?}", depth, reg_id, reg);
                map.insert(*reg_id, reg);
                writeln!(out_file, "    mov {}, QWORD [rsp + 8*{}]", reg, depth)?;
            }
            AsmInstruction::RegAllocDynamicPop(reg_id) => {
                let reg = match allocator.allocate() {
                    Some(reg) => reg,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                eprintln!("Reg Allocate Pop {} > {:?}", reg_id, reg);
                map.insert(*reg_id, reg);
                writeln!(out_file, "    pop {}", reg)?;
            }
            AsmInstruction::RegAllocDynamicLiteral(reg_id, literal) => {
                let reg = match allocator.allocate() {
                    Some(reg) => reg,
                    None => panic!("ICE: Register exhaustion. {:?}", self),
                };
                eprintln!("Reg Allocate Lit {} > {:?}", reg_id, reg);
                map.insert(*reg_id, reg);
                writeln!(out_file, "    mov {}, {}", reg, literal)?;
            }
            AsmInstruction::RegAllocFixedPop(reg) => {
                writeln!(out_file, "    pop {}", reg)?;
            }
            AsmInstruction::RegAllocFixedLiteral(reg, literal) => {
                writeln!(out_file, "    mov {}, {}", reg, literal)?;
            }

            AsmInstruction::RegFreeDynamic { reg_id, push } => {
                let reg = map
                    .remove(reg_id)
                    .expect("ICE: Attempted to remove unallocated register");

                let kind = if *push {
                    writeln!(out_file, "    push {}", reg)?;
                    "Push"
                } else {
                    "Drop"
                };
                eprintln!("Reg Free {} {} > {:?}", kind, reg_id, reg);
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
                            let mut reg = *map.get(reg_id).unwrap_or_else(|| {
                                panic!("ICE: Attempted to fetch unallocated register {}", reg_id)
                            });
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
            AsmInstruction::RegAllocDynamicPop(id),
            self.op_range,
        ));
        id
    }

    pub fn reg_alloc_dyn_nop(&mut self) -> usize {
        let id = self.next_register();
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocDynamicNop(id),
            self.op_range,
        ));
        id
    }

    pub fn reg_alloc_dyn_dup(&mut self, depth: usize) -> usize {
        let id = self.next_register();
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocDynamicDup { depth, reg_id: id },
            self.op_range,
        ));
        id
    }

    pub fn reg_alloc_dyn_literal(&mut self, value: impl Into<Cow<'static, str>>) -> usize {
        let id = self.next_register();
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocDynamicLiteral(id, value.into()),
            self.op_range,
        ));
        id
    }

    pub fn reg_alloc_fixed_pop(&mut self, reg: Register) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocFixedPop(reg),
            self.op_range,
        ));
    }

    pub fn reg_alloc_fixed_literal(&mut self, reg: Register, value: impl Into<Cow<'static, str>>) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegAllocFixedLiteral(reg, value.into()),
            self.op_range,
        ));
    }

    pub fn reg_free_dyn_push(&mut self, reg_id: usize) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegFreeDynamic { reg_id, push: true },
            self.op_range,
        ));
    }

    pub fn reg_free_dyn_drop(&mut self, reg_id: usize) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegFreeDynamic {
                reg_id,
                push: false,
            },
            self.op_range,
        ));
    }

    pub fn reg_free_fixed_push(&mut self, reg_id: Register) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegFreeFixed { reg_id, push: true },
            self.op_range,
        ));
    }

    pub fn reg_free_fixed_drop(&mut self, reg_id: Register) {
        self.assembly.push(Assembly::new(
            AsmInstruction::RegFreeFixed {
                reg_id,
                push: false,
            },
            self.op_range,
        ));
    }
}
