use std::{borrow::Cow, fs::File, io::BufWriter, io::Write, path::Path};

use color_eyre::eyre::{eyre, Context, Result};
use hashbrown::HashSet;
use lasso::Spur;
use log::{debug, trace};

use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{Op, OpCode},
    program::{Procedure, ProcedureId, Program},
    source_file::SourceStorage,
    Width,
};

mod assembly;
use assembly::*;

fn str_lit(lit: impl Into<Cow<'static, str>>) -> InstructionPart {
    InstructionPart::Literal(lit.into())
}

fn reg(reg: X86Register) -> InstructionPart {
    InstructionPart::EmitRegister {
        reg,
        width: Width::Qword,
    }
}

fn stack_slot(slot: usize) -> InstructionPart {
    InstructionPart::EmitStackLocation { slot }
}

fn location(loc: ValueLocation) -> InstructionPart {
    match loc {
        ValueLocation::Register(register) => reg(register),
        ValueLocation::StackSlot(slot) => stack_slot(slot),
    }
}

#[derive(Debug, Default)]
struct SymbolTracker {
    used_global_allocs: HashSet<ProcedureId>,
    used_literals: HashSet<Spur>,
    used_functions: HashSet<ProcedureId>,
    used_function_queue: Vec<ProcedureId>,
}

impl SymbolTracker {
    pub fn use_string(&mut self, id: Spur) {
        self.used_literals.insert(id);
    }

    pub fn use_global_alloc(&mut self, id: ProcedureId) {
        self.used_global_allocs.insert(id);
    }

    pub fn use_function(&mut self, id: ProcedureId) {
        let new_func = self.used_functions.insert(id);
        if new_func {
            self.used_function_queue.push(id);
        }
    }
}

// Function call ABI:
// Because we're re-using the syscall register, we can store up to 7 values in registers
// when calling and returning from a function.
//
// The stack order will be like this:
// [r9, r8, r10, rdx, rsi, rdi, rax]
const CALL_REGS: [X86Register; 7] = [
    X86Register::Rax,
    X86Register::Rdi,
    X86Register::Rsi,
    X86Register::Rdx,
    X86Register::R10,
    X86Register::R8,
    X86Register::R9,
];

impl OpCode {
    fn compile_arithmetic_op(&self) -> &'static str {
        match self {
            OpCode::Add => "add",
            OpCode::BitOr => "or",
            OpCode::BitAnd => "and",
            OpCode::Multiply => "mul",
            OpCode::ShiftLeft => "shl",
            OpCode::ShiftRight => "shr",
            OpCode::Subtract => "sub",
            _ => panic!("ICE: Attempted to compile_arithmetic_op a {:?}", self),
        }
    }

    fn compile_compare_op_suffix(&self) -> &'static str {
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

fn compile_single_instruction(
    program: &Program,
    proc: &Procedure,
    local_alloc_count: usize,
    op: &Op,
    opt_level: u8,
    assembler: &mut Assembler,
    interner: &mut Interners,
    source_store: &SourceStorage,
    symbol_tracker: &mut SymbolTracker,
) {
    match &op.code {
        OpCode::Add | OpCode::Subtract | OpCode::BitOr | OpCode::BitAnd => {
            let op_ios = proc.analyzer().get_op_io(op.id);
            let [input_a, input_b] = *op_ios.inputs().as_arr();
            let [output] = *op_ios.outputs().as_arr();

            let a_loc = assembler.get_value_location(input_a);
            let b_loc = assembler.get_value_location(input_b);

            // We can handle b_loc being in a stack slot, but let's make sure
            // that a_loc is a register.
            let fixups = Vec::new();
            let ValueLocation::Register(a_reg) = a_loc else {
                todo!()
            };

            // The destination register should be the same as a_loc, so we don't
            // need to allocate a new one.

            assembler.free_value_location(input_a);
            assembler.free_value_location(input_b);
            let output_reg = assembler.allocate_fixed_registers(&[a_reg]);
            assert!(output_reg.is_empty(), "ICE: Register was just freed");
            assembler.set_value_location(output, a_reg);

            let instruction = AsmInstruction {
                fixups,
                literal_parts: vec![
                    str_lit(op.code.compile_arithmetic_op()),
                    reg(a_reg),
                    str_lit(","),
                    location(b_loc),
                ],
            };

            let instruction = Assembly::new(instruction, op.id).comment(format!(
                "{}:{}:{} -- {:?}",
                source_store.name(op.token.location.file_id),
                op.token.location.line,
                op.token.location.column,
                op.code
            ));
            assembler.push_instr(instruction);
        }
        OpCode::ArgC => todo!(),
        OpCode::ArgV => todo!(),
        OpCode::BitNot => todo!(),
        OpCode::CallProc { module, proc_id } => todo!(),
        OpCode::CastBool => todo!(),
        OpCode::CastInt => todo!(),
        OpCode::CastPtr => todo!(),
        OpCode::DivMod => todo!(),
        OpCode::Dup { depth } => todo!(),
        OpCode::DupPair => todo!(),
        OpCode::Drop => {
            let [input] = *proc.analyzer().get_op_io(op.id).inputs().as_arr();
            assembler.free_value_location(input);
        }
        OpCode::Epilogue => {
            let instruction = AsmInstruction {
                fixups: Vec::new(),
                literal_parts: vec![str_lit("ret")],
            };
            let instruction = Assembly::new(instruction, op.id);
            assembler.push_instr(instruction);

            // Punt this until later
            assert!(proc.exit_stack().is_empty());
        }
        OpCode::Equal => todo!(),
        OpCode::If {
            open_token,
            condition,
            else_block,
            end_token,
        } => todo!(),
        OpCode::Less => todo!(),
        OpCode::LessEqual => todo!(),
        OpCode::Load { width, kind } => todo!(),
        OpCode::Greater => todo!(),
        OpCode::GreaterEqual => todo!(),
        OpCode::Memory {
            module_id,
            proc_id,
            offset,
            global,
        } => todo!(),
        OpCode::Multiply => todo!(),
        OpCode::NotEq => todo!(),
        OpCode::Prologue => {
            // Entry of the function. Our stack frame is already set up, so all we do
            // here is allocate our registers.

            // TODO: Figure out how to handle passing in more than 7 parameters.
            if proc.entry_stack().len() > 7 {
                panic!("ICE: Cannot handle more than 7 parameters");
            }

            if proc.entry_stack().is_empty() {
                return;
            }

            let call_regs = &CALL_REGS[..proc.entry_stack().len()];
            let fixups = assembler.allocate_fixed_registers(call_regs);
            assert!(
                fixups.is_empty(),
                "Prologue should have no registers in use"
            );

            let inputs = proc.analyzer().get_op_io(op.id).inputs();

            for (&reg, &value) in call_regs.iter().rev().zip(inputs) {
                println!("Value {value:?} -> {reg:?}");
                assembler.set_value_location(value, reg);
            }
        }
        OpCode::PushBool(_) => todo!(),
        OpCode::PushInt(val) => {
            let (register, fixups) = assembler.allocate_register();
            let [value_id] = *proc.analyzer().get_op_io(op.id).outputs().as_arr();

            assembler.set_value_location(value_id, register);

            let instruction = AsmInstruction {
                fixups,
                literal_parts: vec![
                    str_lit("mov"),
                    reg(register),
                    str_lit(","),
                    str_lit(format!("{val}")),
                ],
            };

            let instruction = Assembly::new(instruction, op.id).comment(format!(
                "{}:{}:{} -- {:?}",
                source_store.name(op.token.location.file_id),
                op.token.location.line,
                op.token.location.column,
                op.code
            ));
            assembler.push_instr(instruction);
        }
        OpCode::PushStr { id, is_c_str } => todo!(),
        OpCode::ResolvedIdent { module, proc_id } => todo!(),
        OpCode::Return => todo!(),
        OpCode::Rot => todo!(),
        OpCode::ShiftLeft => todo!(),
        OpCode::ShiftRight => todo!(),
        OpCode::Store { width, kind } => todo!(),
        OpCode::Swap => todo!(),
        OpCode::SysCall(_) => todo!(),
        OpCode::UnresolvedIdent { module, proc } => todo!(),
        OpCode::While { body } => todo!(),
    }
}

fn build_assembly_for_block(
    program: &Program,
    proc: &Procedure,
    block: &[Op],
    local_alloc_count: usize,
    interner: &mut Interners,
    source_store: &SourceStorage,
    opt_level: u8,
    assembler: &mut Assembler,
    symbol_tracker: &mut SymbolTracker,
) {
    for op in block {
        compile_single_instruction(
            program,
            proc,
            local_alloc_count,
            op,
            opt_level,
            assembler,
            interner,
            source_store,
            symbol_tracker,
        );
    }
}

fn assemble_procedure(
    program: &Program,
    symbol_tracker: &mut SymbolTracker,
    proc: &Procedure,
    source_store: &SourceStorage,
    interner: &mut Interners,
    out_file: &mut BufWriter<File>,
    opt_level: u8,
) -> Result<()> {
    let name = interner.get_symbol_name(program, proc.id());
    debug!("Compiling {}...", name);
    writeln!(out_file, "{name}:")?;

    let mut assembler = Assembler::new();

    debug!("  Building assembly...");
    let proc_data = proc.kind().get_proc_data();
    build_assembly_for_block(
        program,
        proc,
        proc.body(),
        proc_data.allocs.len(),
        interner,
        source_store,
        opt_level,
        &mut assembler,
        symbol_tracker,
    );

    // Set up our stack frame.
    writeln!(out_file, "    push rbp")?;
    writeln!(out_file, "    mov rsp, rbp")?;
    writeln!(
        out_file,
        "    sub rsp, {}",
        proc_data.total_alloc_size + assembler.used_stack_slots()
    )?;

    if !proc_data.allocs.is_empty() {
        writeln!(out_file, "    ;; Local Allocs")?;

        // Output a list of allocs and their offsets.
        for (&alloc_name, &alloc_id) in &proc_data.allocs {
            let name = interner.resolve_lexeme(alloc_name);
            let alloc_data = proc_data.alloc_size_and_offsets[&alloc_id];
            writeln!(
                out_file,
                "    ;; {alloc_id:?} {name} -- offset: {} -- size: {}",
                alloc_data.offset, alloc_data.size
            )?;
        }
    }

    debug!("  Rendering...");
    for asm in assembler.assembly() {
        write!(out_file, "    ;; Op {}", asm.op_id.0)?;
        if let Some(comment) = &asm.comment {
            writeln!(out_file, " -- {comment}")?;
        } else {
            writeln!(out_file)?;
        }

        asm.render(out_file)?;
    }

    trace!("");

    Ok(())
}

fn assemble_entry(
    program: &Program,
    entry_function: ProcedureId,
    interner: &mut Interners,
    out_file: &mut BufWriter<File>,
) -> Result<()> {
    debug!("Compiling _start...");

    writeln!(out_file, "_start:")?;
    writeln!(out_file, "    pop QWORD [__argc]")?;
    writeln!(out_file, "    mov QWORD [__argv], rsp")?;
    let proc_name = interner.get_symbol_name(program, entry_function);
    writeln!(out_file, "    call {proc_name}")?;

    // Exit syscall
    writeln!(out_file, "    mov RAX, 60")?;
    writeln!(out_file, "    mov RDI, 0")?;
    writeln!(out_file, "    syscall")?;

    writeln!(out_file)?;
    trace!("");

    Ok(())
}

pub(crate) fn compile_program(
    program: &Program,
    entry_function: ProcedureId,
    source_store: &SourceStorage,
    interner: &mut Interners,
    out_file_path: &Path,
    opt_level: u8,
) -> Result<()> {
    let out_file = File::create(out_file_path)
        .with_context(|| eyre!("Failed to create file: {}", out_file_path.display()))?;
    let mut out_file = BufWriter::new(out_file);

    writeln!(&mut out_file, "BITS 64")?;
    writeln!(&mut out_file, "segment .text")?;
    writeln!(&mut out_file, "global _start")?;

    assemble_entry(program, entry_function, interner, &mut out_file)?;

    let mut symbol_tracker = SymbolTracker::default();
    symbol_tracker.use_function(entry_function);

    // Now run the procedure compilation queue.
    while let Some(id) = symbol_tracker.used_function_queue.pop() {
        let proc = program.get_proc(id);

        assemble_procedure(
            program,
            &mut symbol_tracker,
            proc,
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

    // Emit our global memory into the BSS.
    for id in symbol_tracker.used_global_allocs {
        let size = program
            .get_global_alloc(id)
            .expect("ICE: Tried to fetch a non-global alloc proc");
        let name = interner.get_symbol_name(program, id);
        writeln!(&mut out_file, "    __{}: resb {} ; {:?}", name, size, id)?;
    }

    // Finally emit our string literals
    writeln!(&mut out_file, "segment .rodata")?;
    for id in symbol_tracker.used_literals {
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
