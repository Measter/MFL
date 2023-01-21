use std::{borrow::Cow, fmt::Display, io::Write};

use color_eyre::eyre::Result;

use crate::{opcode::OpId, program::static_analysis::ValueId, Width};

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

#[derive(Debug, Clone, Copy)]
pub enum ValueLocation {
    Register(X86Register),
    StackSlot(usize),
}

#[derive(Debug)]
pub struct Fixup {
    src: ValueLocation,
    dst: ValueLocation,
}

#[derive(Debug)]
pub enum InstructionPart {
    Literal(Cow<'static, str>),
    /// Used to actually emit a register as part of an instruction.
    EmitRegister {
        reg: X86Register,
        width: Width,
    },
    EmitStackLocation {
        slot: usize,
    },
}

#[derive(Debug)]
pub struct AsmInstruction {
    pub fixups: Vec<Fixup>,
    pub literal_parts: Vec<InstructionPart>,
}

#[derive(Debug)]
pub struct Assembly {
    pub asm: AsmInstruction,
    pub comment: Option<String>,
    pub op_id: OpId,
}

impl Assembly {
    pub fn new(asm: AsmInstruction, op_id: OpId) -> Self {
        Self {
            asm,
            op_id,
            comment: None,
        }
    }

    pub fn comment(self, comment: impl Into<String>) -> Self {
        Self {
            comment: Some(comment.into()),
            ..self
        }
    }

    pub fn render(&self, out_file: &mut impl Write) -> Result<()> {
        for fixup in &self.asm.fixups {
            write!(out_file, "    mov ")?;
            match fixup.dst {
                ValueLocation::Register(reg) => write!(out_file, "{}", reg.as_width(Width::Qword))?,
                ValueLocation::StackSlot(slot) => write!(out_file, "[rsp + {slot}")?,
            }
            write!(out_file, ", ")?;

            match fixup.src {
                ValueLocation::Register(reg) => write!(out_file, "{}", reg.as_width(Width::Qword))?,
                ValueLocation::StackSlot(slot) => write!(out_file, "[rsp + {slot}")?,
            }
            writeln!(out_file)?;
        }

        out_file.write_all(b"    ")?;
        for part in &self.asm.literal_parts {
            match part {
                InstructionPart::Literal(lit) => write!(out_file, "{lit} ")?,
                InstructionPart::EmitRegister { reg, width } => {
                    write!(out_file, "{}", reg.as_width(*width))?
                }
                InstructionPart::EmitStackLocation { slot } => write!(out_file, "[rsp + {slot}]")?,
            }
        }
        writeln!(out_file)?;

        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct Assembler {
    assembly: Vec<Assembly>,
    used_stack_slots: usize,
    free_stack_slots: Vec<usize>,

    free_registers: Vec<X86Register>,
    value_locations: Vec<(ValueId, ValueLocation)>,
}

impl Assembler {
    pub fn new() -> Self {
        let regs = vec![
            X86Register::Rax,
            X86Register::Rbx,
            X86Register::Rcx,
            X86Register::Rdx,
            X86Register::Rsi,
            X86Register::Rdi,
            X86Register::R8,
            X86Register::R9,
            X86Register::R10,
            X86Register::R11,
            X86Register::R12,
            X86Register::R13,
            X86Register::R14,
            X86Register::R15,
        ];
        Self {
            assembly: Vec::new(),
            used_stack_slots: 0,
            free_stack_slots: Vec::new(),
            free_registers: regs,
            value_locations: Vec::new(),
        }
    }

    pub fn assembly(&self) -> &[Assembly] {
        &self.assembly
    }

    fn next_stack_slot(&mut self) -> usize {
        if let Some(slot) = self.free_stack_slots.pop() {
            slot
        } else {
            let next = self.used_stack_slots;
            self.used_stack_slots += 1;
            next
        }
    }

    pub fn used_stack_slots(&self) -> usize {
        self.used_stack_slots
    }

    pub fn push_instr(&mut self, instr: Assembly) {
        self.assembly.push(instr);
    }

    pub fn allocate_fixed_registers(&mut self, regs: &[X86Register]) -> Vec<Fixup> {
        let (to_alloc_regs, fixup_regs): (Vec<_>, Vec<_>) = self
            .free_registers
            .iter()
            .copied()
            .partition(|r| regs.contains(r));
        let fixups = Vec::new();

        self.free_registers.retain(|r| !to_alloc_regs.contains(r));

        dbg!(&fixup_regs, &to_alloc_regs);
        // TODO: Actually make fixups.
        assert_eq!(to_alloc_regs.len(), regs.len());

        fixups
    }

    pub fn allocate_register(&mut self) -> (X86Register, Vec<Fixup>) {
        match self.free_registers.pop() {
            Some(reg) => (reg, Vec::new()),
            None => {
                let next_stack_slot = self.next_stack_slot();
                for (_value, loc) in &mut self.value_locations {
                    if let ValueLocation::Register(reg) = loc {
                        let reg = *reg;
                        let new_loc = ValueLocation::StackSlot(next_stack_slot);
                        let fixup = Fixup {
                            src: *loc,
                            dst: new_loc,
                        };

                        *loc = new_loc;
                        return (reg, vec![fixup]);
                    }
                }

                unreachable!()
            }
        }
    }

    #[track_caller]
    pub fn get_value_location(&self, val: ValueId) -> ValueLocation {
        for &(stored_val, loc) in &self.value_locations {
            if stored_val == val {
                return loc;
            }
        }

        panic!("ICE: Tried to get location of unallocated value: {val:?}");
    }

    #[track_caller]
    pub fn set_value_location(&mut self, val: ValueId, reg: X86Register) {
        for (old_value, loc) in &mut self.value_locations {
            if *old_value == val || matches!(*loc, ValueLocation::Register(r) if r == reg) {
                panic!(
                    "ICE: Tried to set value location twice. {:?} from {:?} to {:?}",
                    val, *loc, reg
                );
            }
        }

        self.value_locations
            .push((val, ValueLocation::Register(reg)));
    }

    #[track_caller]
    pub fn free_value_location(&mut self, val: ValueId) {
        let Some(idx) = self.value_locations.iter().position(|(v, _)| *v == val) else {
            panic!("ICE: Tried to remove unallocated value {val:?}");
        };

        let (_, loc) = self.value_locations.remove(idx);
        match loc {
            ValueLocation::Register(reg) => self.free_registers.push(reg),
            ValueLocation::StackSlot(slot) => self.free_stack_slots.push(slot),
        }
    }
}
