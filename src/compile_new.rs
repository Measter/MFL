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
    available_registers: Vec<X86Register>,
}

impl RegisterAllocator {
    fn new() -> Self {
        Self {
            available_registers: vec![
                X86Register::Rbx,
                X86Register::R11,
                X86Register::R12,
                X86Register::R13,
                X86Register::R14,
                X86Register::R15,
            ],
        }
    }

    fn allocate(&mut self) -> Option<X86Register> {
        self.available_registers.pop()
    }

    fn free(&mut self, reg: X86Register) {
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

fn merge_dyn_to_dyn_registers(
    asm: &mut [Assembly],
    new_range: Range<usize>,
    start_reg_id: usize,
    end_reg_id: usize,
) {
    eprintln!(
        "--- Dyn/Dyn Merge {} and {} in range {}..={}",
        start_reg_id,
        end_reg_id,
        new_range.start,
        new_range.end - 1
    );

    for asm in &mut *asm {
        asm.merged_range = new_range.clone();
        use RegisterType::*;
        match &mut asm.asm {
            &mut AsmInstruction::RegAllocPop {
                reg: Dynamic(id), ..
            } if id == end_reg_id => {
                asm.asm = AsmInstruction::Nop;
            }
            &mut AsmInstruction::RegFree {
                reg: Dynamic(reg_id),
                push: true,
            } if reg_id == start_reg_id => {
                asm.asm = AsmInstruction::Nop;
            }
            AsmInstruction::RegFree {
                reg: Dynamic(reg_id),
                ..
            } if *reg_id == end_reg_id => {
                *reg_id = start_reg_id;
            }
            AsmInstruction::Instruction(instrs) => {
                for instr in instrs {
                    match instr {
                        InstructionPart::Register {
                            reg: RegisterType::Dynamic(reg_id),
                            ..
                        } if *reg_id == end_reg_id => *reg_id = start_reg_id,
                        _ => continue,
                    }
                }
            }

            AsmInstruction::RegAllocDup { .. }
            | AsmInstruction::RegAllocPop { .. }
            | AsmInstruction::RegAllocNop { .. }
            | AsmInstruction::RegAllocLiteral { .. }
            | AsmInstruction::RegFree { .. }
            | AsmInstruction::BlockBoundry
            | AsmInstruction::Nop => continue,
        }
    }
}

fn merge_dyn_to_fixed_registers(
    asm: &mut [Assembly],
    new_range: Range<usize>,
    dynamic_reg_id: usize,
    fixed_reg: X86Register,
) {
    eprintln!(
        "--- Dyn/Fixed Merge {} and {} in range {}..={}",
        dynamic_reg_id,
        fixed_reg,
        new_range.start,
        new_range.end - 1
    );

    for asm in asm {
        use RegisterType::*;
        asm.merged_range = new_range.clone();
        match &mut asm.asm {
            &mut AsmInstruction::RegAllocPop { reg: Dynamic(id) } if id == dynamic_reg_id => {
                asm.asm = AsmInstruction::RegAllocPop {
                    reg: Fixed(fixed_reg),
                };
            }
            &mut AsmInstruction::RegAllocNop { reg: Dynamic(id) } if id == dynamic_reg_id => {
                asm.asm = AsmInstruction::RegAllocNop {
                    reg: Fixed(fixed_reg),
                };
            }
            &mut AsmInstruction::RegAllocDup {
                reg: Dynamic(id),
                depth,
            } if id == dynamic_reg_id => {
                asm.asm = AsmInstruction::RegAllocDup {
                    reg: Fixed(fixed_reg),
                    depth,
                }
            }
            AsmInstruction::RegAllocLiteral {
                reg: Dynamic(id),
                value,
            } if *id == dynamic_reg_id => {
                asm.asm = AsmInstruction::RegAllocLiteral {
                    reg: Fixed(fixed_reg),
                    value: value.clone(),
                }
            }

            &mut AsmInstruction::RegAllocPop { reg: Fixed(reg) } if reg == fixed_reg => {
                asm.asm = AsmInstruction::Nop;
            }
            &mut AsmInstruction::RegFree {
                reg: Dynamic(reg_id),
                push: true,
            } if reg_id == dynamic_reg_id => {
                asm.asm = AsmInstruction::Nop;
            }

            AsmInstruction::Instruction(instructions) => {
                for instr in instructions {
                    match *instr {
                        InstructionPart::Register {
                            reg: RegisterType::Dynamic(reg_id),
                            is_byte,
                        } if reg_id == dynamic_reg_id => {
                            *instr = InstructionPart::Register {
                                reg: RegisterType::Fixed(fixed_reg),
                                is_byte,
                            }
                        }
                        _ => continue,
                    }
                }
            }

            AsmInstruction::RegAllocPop { .. }
            | AsmInstruction::RegAllocNop { .. }
            | AsmInstruction::RegAllocLiteral { .. }
            | AsmInstruction::RegAllocDup { .. }
            | AsmInstruction::RegFree { .. }
            | AsmInstruction::BlockBoundry
            | AsmInstruction::Nop => continue,
        }
    }
}

fn merge_fixed_to_dyn_registers(
    asm: &mut [Assembly],
    new_range: Range<usize>,
    dynamic_reg_id: usize,
    fixed_reg: X86Register,
) {
    eprintln!(
        "--- Dyn/Fixed Merge {} and {} in range {}..={}",
        dynamic_reg_id,
        fixed_reg,
        new_range.start,
        new_range.end - 1
    );

    for asm in asm {
        use RegisterType::*;
        asm.merged_range = new_range.clone();
        match &mut asm.asm {
            &mut AsmInstruction::RegAllocPop { reg: Dynamic(id) } if id == dynamic_reg_id => {
                asm.asm = AsmInstruction::Nop;
            }
            &mut AsmInstruction::RegFree {
                reg: Dynamic(id),
                push,
            } if id == dynamic_reg_id => {
                asm.asm = AsmInstruction::RegFree {
                    reg: Fixed(fixed_reg),
                    push,
                };
            }

            &mut AsmInstruction::RegFree {
                reg: Fixed(reg_id),
                push: true,
            } if reg_id == fixed_reg => {
                asm.asm = AsmInstruction::Nop;
            }

            AsmInstruction::Instruction(instructions) => {
                for instr in instructions {
                    match *instr {
                        InstructionPart::Register {
                            reg: RegisterType::Dynamic(reg_id),
                            is_byte,
                        } if reg_id == dynamic_reg_id => {
                            *instr = InstructionPart::Register {
                                reg: RegisterType::Fixed(fixed_reg),
                                is_byte,
                            }
                        }
                        _ => continue,
                    }
                }
            }

            AsmInstruction::RegAllocPop { .. }
            | AsmInstruction::RegAllocNop { .. }
            | AsmInstruction::RegAllocLiteral { .. }
            | AsmInstruction::RegAllocDup { .. }
            | AsmInstruction::RegFree { .. }
            | AsmInstruction::BlockBoundry
            | AsmInstruction::Nop => continue,
        }
    }
}

fn uses_fixed_reg(asm: &[Assembly], fixed_reg: X86Register) -> bool {
    for op in asm {
        use RegisterType::*;
        match &op.asm {
            &AsmInstruction::RegAllocPop { reg: Fixed(reg_id) }
            | &AsmInstruction::RegFree {
                reg: Fixed(reg_id), ..
            }
            | &AsmInstruction::RegAllocLiteral {
                reg: Fixed(reg_id), ..
            } if reg_id == fixed_reg => return true,

            AsmInstruction::Instruction(instrs) => {
                for instr in instrs {
                    match *instr {
                        InstructionPart::Register {
                            reg: RegisterType::Fixed(reg_id),
                            ..
                        } if reg_id == fixed_reg => return true,
                        _ => continue,
                    }
                }
            }
            _ => continue,
        }
    }

    false
}

fn find_op_bounds(idx: usize, program: &[Assembly]) -> Range<usize> {
    let op_range = program[idx].merged_range.clone();
    let mut start_idx = idx;
    let mut end_idx = idx;

    while start_idx > 0 && program[start_idx - 1].merged_range == op_range {
        start_idx -= 1;
    }

    while end_idx < program.len() - 1 && program[end_idx + 1].merged_range == op_range {
        end_idx += 1;
    }

    start_idx..end_idx + 1
}

fn get_op_asm_ranges(
    program: &mut [Assembly],
    end_idx: usize,
    start_asm_range: Range<usize>,
    start_op_range: Range<usize>,
) -> (&mut [Assembly], Range<usize>) {
    let end_asm_range = find_op_bounds(end_idx, program);
    let end_op_range = program[end_idx].merged_range.clone();

    let asm_idx_range = start_asm_range.start..end_asm_range.end;
    let range_to_merge = &mut program[asm_idx_range];
    let new_op_range = start_op_range.start..end_op_range.end;
    (range_to_merge, new_op_range)
}

fn find_dynamic_first_merge(
    program: &mut [Assembly],
    start_idx: usize,
    start_reg_id: usize,
) -> bool {
    use RegisterType::*;

    let start_asm_range = find_op_bounds(start_idx, program);
    let start_op_range = program[start_idx].merged_range.clone();
    for (end_idx, asm) in program.iter().enumerate().skip(start_idx + 1) {
        match asm.asm {
            AsmInstruction::RegAllocPop {
                reg: Dynamic(replaced_reg_id),
            } => {
                let (range_to_merge, new_op_range) =
                    get_op_asm_ranges(program, end_idx, start_asm_range, start_op_range);

                merge_dyn_to_dyn_registers(
                    range_to_merge,
                    new_op_range,
                    start_reg_id,
                    replaced_reg_id,
                );
                return true;
            }

            AsmInstruction::RegAllocPop {
                reg: Fixed(new_reg),
            } => {
                if uses_fixed_reg(&program[start_asm_range.clone()], new_reg) {
                    break;
                }

                let (range_to_merge, new_op_range) =
                    get_op_asm_ranges(program, end_idx, start_asm_range, start_op_range);

                merge_dyn_to_fixed_registers(range_to_merge, new_op_range, start_reg_id, new_reg);
                return true;
            }

            // These access the stack in an unsupported way, so we have to abandon
            // the search for the current op.
            AsmInstruction::RegFree { push: true, .. } | AsmInstruction::RegAllocDup { .. } => {
                break
            }

            // We can't optimize past the end of a block.
            AsmInstruction::BlockBoundry => break,

            // These don't alter the stack, so we can ignore these.
            AsmInstruction::RegFree { push: false, .. }
            | AsmInstruction::RegAllocNop { .. }
            | AsmInstruction::RegAllocLiteral { .. }
            | AsmInstruction::Instruction(_)
            | AsmInstruction::Nop => {}
        }
    }

    false
}

fn find_fixed_first_merge(
    program: &mut [Assembly],
    start_idx: usize,
    fixed_reg: X86Register,
) -> bool {
    use RegisterType::*;

    let start_asm_range = find_op_bounds(start_idx, program);
    let start_op_range = program[start_idx].merged_range.clone();
    for (end_idx, asm) in program.iter().enumerate().skip(start_idx + 1) {
        match asm.asm {
            AsmInstruction::RegAllocPop {
                reg: Dynamic(replaced_reg_id),
            } => {
                if uses_fixed_reg(&program[start_asm_range.clone()], fixed_reg) {
                    break;
                }

                let (range_to_merge, new_op_range) =
                    get_op_asm_ranges(program, end_idx, start_asm_range, start_op_range);

                merge_fixed_to_dyn_registers(
                    range_to_merge,
                    new_op_range,
                    replaced_reg_id,
                    fixed_reg,
                );
                return true;
            }

            // These access the stack in an unsupported way, so we have to abandon
            // the search for the current op.
            AsmInstruction::RegAllocPop { .. }
            | AsmInstruction::RegFree { push: true, .. }
            | AsmInstruction::RegAllocDup { .. } => break,

            // We can't optimize past the end of a block.
            AsmInstruction::BlockBoundry => break,

            // These don't alter the stack, so we can ignore these.
            AsmInstruction::RegFree { push: false, .. }
            | AsmInstruction::RegAllocNop { .. }
            | AsmInstruction::RegAllocLiteral { .. }
            | AsmInstruction::Instruction(_)
            | AsmInstruction::Nop => {}
        }
    }

    false
}

fn combine_stack_ops(program: &mut [Assembly]) {
    loop {
        let mut did_change = false;

        for start_idx in 0..program.len() {
            use RegisterType::*;
            match program[start_idx].asm {
                AsmInstruction::RegFree {
                    push: true,
                    reg: Dynamic(start_reg_id),
                } => did_change |= find_dynamic_first_merge(program, start_idx, start_reg_id),
                AsmInstruction::RegFree {
                    push: true,
                    reg: Fixed(start_reg_id),
                } => did_change |= find_fixed_first_merge(program, start_idx, start_reg_id),
                _ => continue,
            };
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
