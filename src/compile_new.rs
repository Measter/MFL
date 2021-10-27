use std::{collections::HashMap, fs::File, io::BufWriter, io::Write, ops::Range, path::Path};

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
mod optimizer_passes;
use optimizer_passes::PASSES;

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

fn build_assembly(mut program: &[Op], interner: &Interners, optimize: bool) -> Vec<Assembly> {
    let mut assembler = Assembler::default();

    let mut ip = 0;
    while !program.is_empty() {
        let len_compiled = if optimize {
            PASSES
                .iter()
                .filter_map(|pass| pass(program, ip, &mut assembler, interner))
                .next()
        } else {
            optimizer_passes::compile_single_instruction(program, ip, &mut assembler, interner)
        }
        .expect("ICE: Failed to compile single instruction");
        program = &program[len_compiled..];
        ip += len_compiled;
    }

    assembler.into_assembly()
}

fn merge_dyn_dyn_registers(
    asm: &mut [Assembly],
    new_range: Range<usize>,
    start_reg_id: usize,
    end_reg_id: usize,
) {
    eprintln!(
        "--- Merge {} and {} in range {}..={}",
        start_reg_id,
        end_reg_id,
        new_range.start,
        new_range.end - 1
    );

    for asm in &mut *asm {
        asm.merged_range = new_range.clone();
        match &mut asm.asm {
            AsmInstruction::RegAllocDynamicPop(id) if *id == end_reg_id => {
                asm.asm = AsmInstruction::Nop;
            }
            AsmInstruction::RegFreeDynamic { reg_id, push: true } if *reg_id == start_reg_id => {
                asm.asm = AsmInstruction::Nop;
            }
            AsmInstruction::RegFreeDynamic { reg_id, .. } if *reg_id == end_reg_id => {
                *reg_id = start_reg_id;
            }
            AsmInstruction::Instruction(instrs) => {
                for instr in instrs {
                    match instr {
                        InstructionPart::DynamicRegister { reg_id, .. }
                            if *reg_id == end_reg_id =>
                        {
                            *reg_id = start_reg_id
                        }
                        _ => continue,
                    }
                }
            }
            AsmInstruction::RegAllocDynamicDup { .. }
            | AsmInstruction::RegAllocDynamicPop(_)
            | AsmInstruction::RegAllocFixedPop(_)
            | AsmInstruction::RegAllocDynamicNop(_)
            | AsmInstruction::RegAllocDynamicLiteral(_, _)
            | AsmInstruction::RegAllocFixedLiteral(_, _)
            | AsmInstruction::RegFreeDynamic { .. }
            | AsmInstruction::RegFreeFixed { .. }
            | AsmInstruction::BlockBoundry
            | AsmInstruction::Nop => continue,
        }
    }
}

fn combine_stack_ops(asm: &mut [Assembly]) {
    loop {
        let mut did_change = false;

        'start_search: for mut start_idx in 0..asm.len() {
            let start_reg_id = match &asm[start_idx].asm {
                AsmInstruction::RegFreeDynamic { push: true, reg_id } => *reg_id,
                _ => continue,
            };

            // The current instruction is a dynamic free-push. We'll search forward for the next
            // stack operation. If it's a RegAllocDynamicPop then we can merge the two operations.
            // If we find any other kind of stack operation, then we have to abort.

            let mut end_idx = start_idx + 1;
            let mut replaced_reg_id = None;
            for (search_idx, asm) in asm.iter().enumerate().skip(end_idx) {
                end_idx = search_idx;
                match &asm.asm {
                    AsmInstruction::RegAllocDynamicPop(id) => {
                        replaced_reg_id = Some(*id);
                        break;
                    }

                    // These access the stack in an unsupported way, so we have to abandon
                    // the search for the current op.
                    AsmInstruction::RegFreeDynamic { push: true, .. }
                    | AsmInstruction::RegFreeFixed { push: true, .. }
                    | AsmInstruction::RegAllocFixedPop(_)
                    | AsmInstruction::RegAllocDynamicDup { .. } => continue 'start_search,

                    // We can't optimize past the end of a block.
                    AsmInstruction::BlockBoundry => {
                        continue 'start_search;
                    }

                    // These don't alter the stack, so we can ignore these.
                    AsmInstruction::RegFreeDynamic { push: false, .. }
                    | AsmInstruction::RegFreeFixed { push: false, .. }
                    | AsmInstruction::RegAllocDynamicNop(_)
                    | AsmInstruction::RegAllocDynamicLiteral(_, _)
                    | AsmInstruction::RegAllocFixedLiteral(_, _)
                    | AsmInstruction::Instruction(_)
                    | AsmInstruction::Nop => {}
                }
            }

            // We need to handle running off the end of the assembly.
            let replaced_reg_id = match replaced_reg_id {
                Some(id) => id,
                None => break,
            };

            // Now we need to search backwards for the beginning of the start register's operation.
            let start_op_range = asm[start_idx].merged_range.clone();
            while start_idx > 0 && asm[start_idx - 1].merged_range == start_op_range {
                start_idx -= 1;
            }

            // Now search the other direction to find the end of the replaced registers operation.
            let end_op_range = asm[end_idx].merged_range.clone();
            while end_idx < asm.len() - 1 && asm[end_idx + 1].merged_range == end_op_range {
                end_idx += 1;
            }

            let range_to_merge = &mut asm[start_idx..=end_idx];
            let new_op_range = start_op_range.start..end_op_range.end;

            merge_dyn_dyn_registers(range_to_merge, new_op_range, start_reg_id, replaced_reg_id);
            did_change = true;
        }

        if !did_change {
            break;
        }
    }
}

pub(crate) fn compile_program(
    program: &[Op],
    source_store: &SourceStorage,
    interner: &Interners,
    out_file_path: &Path,
    optimize: bool,
) -> Result<()> {
    let mut assembly = build_assembly(program, interner, optimize);

    if optimize {
        combine_stack_ops(&mut assembly);
    }

    write_assembly(out_file_path, source_store, interner, program, &assembly)?;

    Ok(())
}
