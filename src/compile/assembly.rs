use std::{borrow::Cow, io::Write};

use color_eyre::eyre::Result;

use crate::{opcode::OpId, Width};

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

#[derive(Debug)]
enum ValueLocation {
    Register(X86Register),
    StackSlot(usize),
}

#[derive(Debug)]
struct Fixups {
    src: ValueLocation,
    dst: ValueLocation,
}

#[derive(Debug)]
pub struct AsmInstruction {
    fixups: Vec<Fixups>,
    literal_parts: Vec<Cow<'static, str>>,
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
        todo!()
    }
}

#[derive(Debug, Default)]
pub struct Assembler {
    name: String,
    assembly: Vec<Assembly>,
    used_stack_slots: usize,
    free_stack_slots: Vec<usize>,
}

impl Assembler {
    pub fn new(name: String) -> Self {
        Self {
            name,
            assembly: Vec::new(),
            used_stack_slots: 0,
            free_stack_slots: Vec::new(),
        }
    }

    pub fn assembly(&self) -> &[Assembly] {
        &self.assembly
    }

    pub fn used_stack_slots(&self) -> usize {
        self.used_stack_slots
    }

    pub fn push_instr(&mut self) {
        // TODO
    }
}
