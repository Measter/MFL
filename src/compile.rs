use std::{collections::HashMap, fs::File, io::BufWriter, io::Write, ops::Range, path::Path};

use codespan_reporting::files::Files;
use color_eyre::eyre::{eyre, Context, Result};
use lasso::Spur;

use crate::{
    interners::Interners,
    opcode::{OpCode, Procedure},
    source_file::SourceStorage,
    Program, Width, OPT_INSTR, OPT_STACK,
};

mod assembly;
use assembly::*;
mod optimizer_passes;
use optimizer_passes::{str_lit, use_reg, PASSES};

const CALL_STACK_LEN: usize = usize::pow(2, 20); // 1 MB

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

fn build_assembly(
    proc: &Procedure,
    interner: &Interners,
    opt_level: u8,
    assembler: &mut Assembler,
) {
    let mut proc_body = &*proc.body;
    let mut ip = 0;
    while !proc_body.is_empty() {
        let len_compiled = if opt_level >= OPT_INSTR {
            PASSES
                .iter()
                .filter_map(|pass| pass(proc, proc_body, ip, assembler, interner))
                .next()
        } else {
            optimizer_passes::compile_single_instruction(proc, proc_body, ip, assembler, interner)
        }
        .expect("ICE: Failed to compile single instruction");
        proc_body = &proc_body[len_compiled..];
        ip += len_compiled;
    }
}

fn merge_dyn_to_dyn_registers(
    program_chunk: &mut [Assembly],
    new_range: Range<usize>,
    start_reg_id: usize,
    end_reg_id: usize,
) {
    eprintln!(
        "    Merge {} and {} in range {}..={}",
        start_reg_id,
        end_reg_id,
        new_range.start,
        new_range.end - 1
    );

    for asm_info in &mut *program_chunk {
        asm_info.merged_range = new_range.clone();
        use RegisterType::*;
        match &mut asm_info.asm {
            &mut AsmInstruction::RegAllocPop {
                reg: Dynamic(id), ..
            } if id == end_reg_id => {
                asm_info.asm = AsmInstruction::Nop;
            }
            &mut AsmInstruction::RegFree {
                reg: Dynamic(reg_id),
                push: true,
            } if reg_id == start_reg_id => {
                asm_info.asm = AsmInstruction::Nop;
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
                        InstructionPart::EmitRegister {
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
            | AsmInstruction::RegAllocLea { .. }
            | AsmInstruction::RegAllocLiteral { .. }
            | AsmInstruction::RegAllocMov { .. }
            | AsmInstruction::RegFree { .. }
            | AsmInstruction::BlockBoundry
            | AsmInstruction::SwapStacks
            | AsmInstruction::Nop => continue,
        }
    }
}

fn merge_dyn_to_fixed_registers(
    program_chunk: &mut [Assembly],
    new_range: Range<usize>,
    dynamic_reg_id: usize,
    fixed_reg: X86Register,
) {
    eprintln!(
        "    Merge {} and {} in range {}..={}",
        dynamic_reg_id,
        fixed_reg.as_width(Width::Qword),
        new_range.start,
        new_range.end - 1
    );

    for asm_info in program_chunk {
        use RegisterType::*;
        asm_info.merged_range = new_range.clone();
        match &mut asm_info.asm {
            &mut AsmInstruction::RegAllocPop { reg: Dynamic(id) } if id == dynamic_reg_id => {
                asm_info.asm = AsmInstruction::RegAllocPop {
                    reg: Fixed(fixed_reg),
                };
            }
            &mut AsmInstruction::RegAllocNop { reg: Dynamic(id) } if id == dynamic_reg_id => {
                asm_info.asm = AsmInstruction::RegAllocNop {
                    reg: Fixed(fixed_reg),
                };
            }
            &mut AsmInstruction::RegAllocDup {
                reg: Dynamic(id),
                depth,
            } if id == dynamic_reg_id => {
                asm_info.asm = AsmInstruction::RegAllocDup {
                    reg: Fixed(fixed_reg),
                    depth,
                }
            }
            AsmInstruction::RegAllocLiteral {
                reg: Dynamic(id),
                value,
            } if *id == dynamic_reg_id => {
                asm_info.asm = AsmInstruction::RegAllocLiteral {
                    reg: Fixed(fixed_reg),
                    value: value.clone(),
                }
            }
            AsmInstruction::RegAllocLea {
                reg: Dynamic(id),
                addr,
            } if *id == dynamic_reg_id => {
                asm_info.asm = AsmInstruction::RegAllocLea {
                    reg: Fixed(fixed_reg),
                    addr: addr.clone(),
                }
            }

            &mut AsmInstruction::RegAllocPop { reg: Fixed(reg) } if reg == fixed_reg => {
                asm_info.asm = AsmInstruction::Nop;
            }
            &mut AsmInstruction::RegFree {
                reg: Dynamic(reg_id),
                push: true,
            } if reg_id == dynamic_reg_id => {
                asm_info.asm = AsmInstruction::Nop;
            }

            AsmInstruction::Instruction(instructions) => {
                for instr in instructions {
                    match *instr {
                        InstructionPart::EmitRegister {
                            reg: RegisterType::Dynamic(reg_id),
                            width,
                        } if reg_id == dynamic_reg_id => {
                            *instr = InstructionPart::EmitRegister {
                                reg: RegisterType::Fixed(fixed_reg),
                                width,
                            }
                        }
                        _ => continue,
                    }
                }
            }

            AsmInstruction::RegAllocPop { .. }
            | AsmInstruction::RegAllocNop { .. }
            | AsmInstruction::RegAllocLea { .. }
            | AsmInstruction::RegAllocLiteral { .. }
            | AsmInstruction::RegAllocMov { .. }
            | AsmInstruction::RegAllocDup { .. }
            | AsmInstruction::RegFree { .. }
            | AsmInstruction::BlockBoundry
            | AsmInstruction::SwapStacks
            | AsmInstruction::Nop => continue,
        }
    }
}

fn merge_fixed_to_dyn_registers(
    program_chunk: &mut [Assembly],
    new_range: Range<usize>,
    dynamic_reg_id: usize,
    fixed_reg: X86Register,
) {
    eprintln!(
        "    Merge {} and {} in range {}..={}",
        dynamic_reg_id,
        fixed_reg.as_width(Width::Qword),
        new_range.start,
        new_range.end - 1
    );

    for asm_info in program_chunk {
        use RegisterType::*;
        asm_info.merged_range = new_range.clone();
        match &mut asm_info.asm {
            &mut AsmInstruction::RegAllocPop { reg: Dynamic(id) } if id == dynamic_reg_id => {
                asm_info.asm = AsmInstruction::Nop;
            }
            &mut AsmInstruction::RegFree {
                reg: Dynamic(id),
                push,
            } if id == dynamic_reg_id => {
                asm_info.asm = AsmInstruction::RegFree {
                    reg: Fixed(fixed_reg),
                    push,
                };
            }

            &mut AsmInstruction::RegFree {
                reg: Fixed(reg_id),
                push: true,
            } if reg_id == fixed_reg => {
                asm_info.asm = AsmInstruction::Nop;
            }

            AsmInstruction::Instruction(instructions) => {
                for instr in instructions {
                    match *instr {
                        InstructionPart::EmitRegister {
                            reg: RegisterType::Dynamic(reg_id),
                            width,
                        } if reg_id == dynamic_reg_id => {
                            *instr = InstructionPart::EmitRegister {
                                reg: RegisterType::Fixed(fixed_reg),
                                width,
                            }
                        }
                        _ => continue,
                    }
                }
            }

            AsmInstruction::RegAllocPop { .. }
            | AsmInstruction::RegAllocNop { .. }
            | AsmInstruction::RegAllocLea { .. }
            | AsmInstruction::RegAllocLiteral { .. }
            | AsmInstruction::RegAllocMov { .. }
            | AsmInstruction::RegAllocDup { .. }
            | AsmInstruction::RegFree { .. }
            | AsmInstruction::BlockBoundry
            | AsmInstruction::SwapStacks
            | AsmInstruction::Nop => continue,
        }
    }
}

fn uses_fixed_reg(program_chunk: &[Assembly], fixed_reg: X86Register) -> bool {
    for asm_info in program_chunk {
        use RegisterType::*;
        match &asm_info.asm {
            &AsmInstruction::RegAllocPop { reg: Fixed(reg_id) }
            | &AsmInstruction::RegAllocNop { reg: Fixed(reg_id) }
            | &AsmInstruction::RegAllocDup {
                reg: Fixed(reg_id), ..
            }
            | &AsmInstruction::RegAllocMov {
                src: Fixed(reg_id), ..
            }
            | &AsmInstruction::RegAllocMov {
                dst: Fixed(reg_id), ..
            }
            | &AsmInstruction::RegFree {
                reg: Fixed(reg_id), ..
            }
            | &AsmInstruction::RegAllocLiteral {
                reg: Fixed(reg_id), ..
            } if reg_id == fixed_reg => return true,

            &AsmInstruction::RegAllocMov {
                src: Fixed(src_reg),
                dst: Fixed(dst_reg),
            } if src_reg == fixed_reg || dst_reg == fixed_reg => {
                return true;
            }

            AsmInstruction::Instruction(instrs) => {
                for instr in instrs {
                    match *instr {
                        InstructionPart::EmitRegister {
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
                let end_asm_range = find_op_bounds(end_idx, program);
                // We also need to check between the starting op and the ending op in case any of the
                // ops in there use the register.
                let between_asm_range = start_asm_range.end..end_asm_range.start;

                if start_asm_range != end_asm_range
                    && (uses_fixed_reg(&program[start_asm_range.clone()], new_reg)
                        || uses_fixed_reg(&program[between_asm_range], new_reg))
                {
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

            // We can't optimize past the end of a block or function call.
            AsmInstruction::BlockBoundry | AsmInstruction::SwapStacks => break,

            // These don't alter the stack, so we can ignore these.
            AsmInstruction::RegFree { push: false, .. }
            | AsmInstruction::RegAllocNop { .. }
            | AsmInstruction::RegAllocLea { .. }
            | AsmInstruction::RegAllocLiteral { .. }
            | AsmInstruction::RegAllocMov { .. }
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
                let end_asm_range = find_op_bounds(end_idx, program);
                // We also need to check between the starting op and the ending op in case any of the
                // ops in there use the register.
                let between_asm_range = start_asm_range.end..end_asm_range.start;
                if start_asm_range != end_asm_range
                    && (uses_fixed_reg(&program[end_asm_range], fixed_reg)
                        || uses_fixed_reg(&program[between_asm_range], fixed_reg))
                {
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

            // This one's pretty simple: We've pushed a register, then immediately popped back into it.
            // Can just Nop both the push and pop.
            AsmInstruction::RegAllocPop {
                reg: Fixed(replaced_reg),
            } if replaced_reg == fixed_reg => {
                let end_asm_range = find_op_bounds(end_idx, program);
                // We need to check between the starting op and the ending op in case any of the
                // ops in there use the register.
                let between_asm_range = start_asm_range.end..end_asm_range.start;
                if start_asm_range != end_asm_range
                    && uses_fixed_reg(&program[between_asm_range], fixed_reg)
                {
                    break;
                }

                program[start_idx].asm = AsmInstruction::Nop;
                program[end_idx].asm = AsmInstruction::Nop;

                let (range_to_merge, new_op_range) =
                    get_op_asm_ranges(program, end_idx, start_asm_range, start_op_range);

                for asm in range_to_merge {
                    asm.merged_range = new_op_range.clone();
                }

                return true;
            }

            // This is for pushing fixed register A, then popping into fixed register B.
            // We can replace this with a simple MOV.
            AsmInstruction::RegAllocPop {
                reg: Fixed(new_reg),
            } => {
                let end_asm_range = find_op_bounds(end_idx, program);
                // We need to check between the starting op and the ending op in case any of the
                // ops in there use either register.
                let between_asm_range = start_asm_range.end..end_asm_range.start;
                let chunk = &program[between_asm_range];
                if start_asm_range != end_asm_range && uses_fixed_reg(chunk, fixed_reg)
                    || uses_fixed_reg(chunk, new_reg)
                {
                    break;
                }

                program[start_idx].asm = AsmInstruction::Nop; // Nop the push.
                program[end_idx].asm = AsmInstruction::RegAllocMov {
                    src: Fixed(fixed_reg),
                    dst: Fixed(new_reg),
                };

                let (range_to_merge, new_op_range) =
                    get_op_asm_ranges(program, end_idx, start_asm_range, start_op_range);

                for asm in range_to_merge {
                    asm.merged_range = new_op_range.clone();
                }

                return true;
            }

            // These access the stack in an unsupported way, so we have to abandon
            // the search for the current op.
            AsmInstruction::RegFree { push: true, .. } | AsmInstruction::RegAllocDup { .. } => {
                break
            }

            // We can't optimize past the end of a block or a function call.
            AsmInstruction::BlockBoundry | AsmInstruction::SwapStacks => break,

            // These don't alter the stack, so we can ignore these.
            AsmInstruction::RegFree { push: false, .. }
            | AsmInstruction::RegAllocNop { .. }
            | AsmInstruction::RegAllocLea { .. }
            | AsmInstruction::RegAllocLiteral { .. }
            | AsmInstruction::RegAllocMov { .. }
            | AsmInstruction::Instruction(_)
            | AsmInstruction::Nop => {}
        }
    }

    false
}

fn find_unused_reg(program: &mut [Assembly], start_idx: usize, reg: RegisterType) -> bool {
    for end_idx in start_idx + 1..program.len() {
        match &program[end_idx].asm {
            AsmInstruction::RegFree {
                reg: freed_reg,
                push: false,
            } if *freed_reg == reg => {
                // If we get here, we haven't used the register, so Nop it.
                program[start_idx].asm = AsmInstruction::Nop;
                program[end_idx].asm = AsmInstruction::Nop;
                return true;
            }
            AsmInstruction::RegFree {
                reg: freed_reg,
                push: true,
            } if *freed_reg == reg => {
                // The result is actually used, so we need to *not* Nop it.
                return false;
            }
            AsmInstruction::Instruction(instrs) => {
                for instr in instrs {
                    match instr {
                        InstructionPart::EmitRegister { reg: used_reg, .. }
                        | InstructionPart::UseRegister { reg: used_reg }
                            if *used_reg == reg =>
                        {
                            return false;
                        }
                        _ => continue,
                    }
                }
            }
            _ => continue,
        }
    }

    false
}

fn optimize_allocation(program: &mut [Assembly]) {
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

                // We can also optimize other forms of allocation, by checking if the register is actually
                // used. If it isn't, just Nop both the alloc and free.
                AsmInstruction::RegAllocDup { reg, .. }
                | AsmInstruction::RegAllocLiteral { reg, .. }
                | AsmInstruction::RegAllocLea { reg, .. }
                | AsmInstruction::RegAllocMov { dst: reg, .. } => {
                    did_change |= find_unused_reg(program, start_idx, reg);
                }

                // Also optimize sequential stack swaps
                AsmInstruction::SwapStacks
                    if matches![
                        program.get(start_idx + 1).map(|p| &p.asm),
                        Some(AsmInstruction::SwapStacks)
                    ] =>
                {
                    program[start_idx].asm = AsmInstruction::Nop;
                    program[start_idx + 1].asm = AsmInstruction::Nop;
                }
                _ => continue,
            };
        }

        if !did_change {
            break;
        }
    }
}

fn assemble_procedure(
    assembler: &mut Assembler,
    proc: &Procedure,
    proc_name: Option<Spur>,
    source_store: &SourceStorage,
    interner: &Interners,
    out_file: &mut BufWriter<File>,
    opt_level: u8,
) -> Result<()> {
    match proc_name {
        Some(id) => {
            let name = interner.resolve_lexeme(id);
            println!("Compiling {}...", name);
            assembler.push_instr([str_lit(format!("proc_{}:", name))]);

            if !proc.allocs.is_empty() {
                assembler.push_instr([str_lit(";; Local allocs")]);
                // Output a list of allocs and their offsets.
                for &alloc_id in proc.allocs.keys() {
                    let name = interner.resolve_lexeme(alloc_id);
                    let alloc_data = proc.alloc_size_and_offsets[&alloc_id];
                    assembler.push_instr([str_lit(format!(
                        ";; {:?} {} -- offset: {} -- size: {}",
                        alloc_id, name, alloc_data.offset, alloc_data.size
                    ))]);
                }
                assembler.push_instr([str_lit(format!("    sub rsp, {}", proc.total_alloc_size))]);
            }

            assembler.swap_stacks();
        }
        None => {
            println!("Compiling main...");
            assembler.push_instr([str_lit("_start:")]);
            assembler.push_instr([str_lit("    pop QWORD [__argc]")]);
            assembler.push_instr([str_lit("    mov QWORD [__argv], rsp")]);
            assembler.push_instr([str_lit("    mov rbp, __call_stack_end")]);
        }
    }

    eprintln!("  Building assembly...");
    build_assembly(proc, interner, opt_level, assembler);

    if proc_name.is_none() {
        assembler.reg_alloc_fixed_literal(X86Register::Rax, "60");
        assembler.reg_alloc_fixed_literal(X86Register::Rdi, "0");
        assembler.push_instr([
            str_lit("    syscall"),
            use_reg(RegisterType::Fixed(X86Register::Rax)),
            use_reg(RegisterType::Fixed(X86Register::Rdi)),
        ]);
        assembler.reg_free_fixed_drop(X86Register::Rax);
        assembler.reg_free_fixed_drop(X86Register::Rdi);
    }

    if opt_level >= OPT_STACK {
        eprintln!("  Optimizing stack ops...");
        optimize_allocation(assembler.assembly_mut());
    }

    let mut register_allocator = RegisterAllocator::new();
    let mut register_map = HashMap::new();

    let mut last_op_range = usize::MAX..usize::MAX; // Intentinally invalid.

    eprintln!();
    eprintln!("  Rendering...");
    for asm in assembler.assembly() {
        if last_op_range != asm.op_range {
            last_op_range = asm.op_range.clone();
            for (op, ip) in proc.body[asm.op_range.clone()]
                .iter()
                .zip(asm.op_range.clone())
            {
                let location = source_store
                    .location(op.token.location.file_id, op.token.location.source_start)?;
                writeln!(
                    out_file,
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
            .render(out_file, &mut register_allocator, &mut register_map)?;
    }

    eprintln!();

    Ok(())
}

pub(crate) fn compile_program(
    program: &Program,
    source_store: &SourceStorage,
    interner: &Interners,
    out_file_path: &Path,
    opt_level: u8,
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

    let mut assembler = Assembler::default();

    assemble_procedure(
        &mut assembler,
        &program.global,
        None,
        source_store,
        interner,
        &mut out_file,
        opt_level,
    )?;

    writeln!(&mut out_file)?;

    for (id, proc) in &program.procedures {
        assembler.reset();
        assemble_procedure(
            &mut assembler,
            proc,
            Some(*id),
            source_store,
            interner,
            &mut out_file,
            opt_level,
        )?;

        writeln!(&mut out_file)?;
    }

    writeln!(&mut out_file, "segment .bss")?;
    writeln!(&mut out_file, "    __argc: resq {}", 1)?;
    writeln!(&mut out_file, "    __argv: resq {}", 1)?;
    writeln!(&mut out_file, "    __call_stack: resq {}", CALL_STACK_LEN)?;
    writeln!(&mut out_file, "    __call_stack_end:")?;

    for &id in assembler.used_allocs() {
        let size = program.global.alloc_size_and_offsets[&id].size;
        let name = interner.resolve_lexeme(id);
        writeln!(&mut out_file, "    __{}: resb {} ; {:?}", name, size, id)?;
    }

    writeln!(&mut out_file, "segment .rodata")?;
    for &id in assembler.used_strings() {
        let literal = interner.resolve_literal(id);
        // Strip the last null char, as we output a null anyway to simplify the loop,
        // and it'll clean up the comment.
        let literal = &literal[..literal.len() - 1];
        let id = id.into_inner().get();
        writeln!(out_file, "    ; {:?}", literal)?;
        write!(out_file, "    __string_literal{}: db ", id)?;

        for b in literal.as_bytes() {
            write!(out_file, "{},", b)?;
        }

        out_file.write_all(b"0\n")?;
    }

    Ok(())
}
