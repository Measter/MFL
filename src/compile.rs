use std::{
    fs::File,
    io::{BufWriter, Write},
    path::Path,
};

use codespan_reporting::files::Files;
use color_eyre::eyre::{eyre, Context, Result};

use crate::{
    opcode::{Op, OpCode},
    source_file::SourceStorage,
    MEMORY_CAPACITY,
};

use self::optimizer_passes::PASSES;

mod optimizer_passes;

impl OpCode {
    fn compile_arithmetic_op(
        self,
        big_b: &'static str,
        little_b: &'static str,
    ) -> (&'static str, &'static str) {
        match self {
            OpCode::Add => ("add", big_b),
            OpCode::BitOr => ("or", big_b),
            OpCode::BitAnd => ("and", big_b),
            OpCode::ShiftLeft => ("shl", little_b),
            OpCode::ShiftRight => ("shr", little_b),
            OpCode::Subtract => ("sub", big_b),
            _ => panic!("ICE: Attempted to compile_arithmetic_op a {:?}", self),
        }
    }

    fn compile_compare_op(self) -> &'static str {
        match self {
            OpCode::Equal => "sete",
            OpCode::Greater => "setg",
            OpCode::Less => "setl",
            _ => panic!("ICE: Attempted to compile_compare_op a {:?}", self),
        }
    }
}

fn compile_op(output: &mut impl Write, op: Op) -> Result<()> {
    match op.code {
        OpCode::Add
        | OpCode::Subtract
        | OpCode::BitAnd
        | OpCode::BitOr
        | OpCode::ShiftLeft
        | OpCode::ShiftRight => {
            let (op, b_reg) = op.code.compile_arithmetic_op("rcx", "cl");
            writeln!(output, "    pop rcx")?;
            writeln!(output, "    {} QWORD [rsp], {}", op, b_reg)?;
        }

        OpCode::Push(v) if v < u32::MAX as u64 => {
            writeln!(output, "    push {}", v)?;
        }
        OpCode::Push(v) => {
            writeln!(output, "    mov rax, {}", v)?;
            writeln!(output, "    push rax")?;
        }
        OpCode::Drop => writeln!(output, "    pop rax")?,

        OpCode::Equal => {
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    cmp rax, rbx")?;
            writeln!(output, "    sete r15b")?;
            writeln!(output, "    push r15")?;
        }
        OpCode::Less => {
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    cmp rax, rbx")?;
            writeln!(output, "    setl r15b")?;
            writeln!(output, "    push r15")?;
        }
        OpCode::Greater => {
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    cmp rax, rbx")?;
            writeln!(output, "    setg r15b")?;
            writeln!(output, "    push r15")?;
        }

        OpCode::While { ip } => {
            writeln!(output, ".LBL{}:", ip)?;
        }
        OpCode::Do { end_ip, .. } => {
            writeln!(output, "    pop rax")?;
            writeln!(output, "    test rax, rax")?;
            writeln!(output, "    jz .LBL{}", end_ip)?;
        }
        OpCode::EndWhile {
            condition_ip,
            end_ip,
        } => {
            writeln!(output, "    jmp .LBL{}", condition_ip)?;
            writeln!(output, ".LBL{}:", end_ip)?;
        }

        OpCode::If { end_ip, .. } => {
            writeln!(output, "    pop rax")?;
            writeln!(output, "    test rax, rax")?;
            writeln!(output, "    jz .LBL{}", end_ip)?;
        }
        OpCode::Else { end_ip, else_start } => {
            writeln!(output, "    jmp .LBL{}", end_ip)?;
            writeln!(output, ".LBL{}:", else_start)?;
        }
        OpCode::EndIf { ip } => {
            writeln!(output, ".LBL{}:", ip)?;
        }

        OpCode::Dump => {
            writeln!(output, "    pop rdi")?;
            writeln!(output, "    call dump")?;
        }
        OpCode::Dup => writeln!(output, "    push QWORD [rsp]")?,
        OpCode::DupPair => {
            writeln!(output, "    push QWORD [rsp+8]")?;
            writeln!(output, "    push QWORD [rsp+8]")?;
        }
        OpCode::Over => writeln!(output, "    push QWORD [rsp+8]")?,
        OpCode::Swap => {
            writeln!(output, "    pop rax")?;
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    push rax")?;
            writeln!(output, "    push rbx")?;
        }

        OpCode::Mem { offset: 0 } => writeln!(output, "    push __memory")?,
        OpCode::Mem { offset } => {
            writeln!(output, "    lea rax, [__memory + {}]", offset)?;
            writeln!(output, "    push rax")?;
        }
        OpCode::Load => {
            writeln!(output, "    pop rax")?;
            writeln!(output, "    mov r15b, BYTE [rax]")?;
            writeln!(output, "    push r15")?;
        }
        OpCode::Store => {
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    mov BYTE [rax], bl")?;
        }

        OpCode::SysCall(a @ 0..=6) => {
            for reg in &["rax", "rdi", "rsi", "rdx", "r10", "r8", "r9"][..=a] {
                writeln!(output, "    pop {}", reg)?;
            }

            writeln!(output, "    syscall")?;
        }
        OpCode::SysCall(arg_count) => {
            panic!("ICE: Invalid syscall argument count: {}", arg_count)
        }
        OpCode::End { .. } => {
            panic!("ICE: Encountered OpCode::End")
        }
    }

    Ok(())
}

fn try_optimize(ops: &[Op]) -> (Vec<u8>, &[Op], &[Op]) {
    PASSES.iter().filter_map(|pass| pass(ops)).next().unwrap()
}

pub(crate) fn compile_program(
    program: &[Op],
    source_store: &SourceStorage,
    out_file_path: &Path,
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
    // R15 is used for single-byte handling, so we ideally do not want to touch the upper bytes.
    writeln!(&mut out_file, "    xor r15, r15")?;

    let mut ops = program;
    let mut ip = 0;
    while !ops.is_empty() {
        let (asm, compiled_ops, remaining_ops) = try_optimize(ops);

        for op in compiled_ops {
            let location = source_store.location(op.location.file_id, op.location.source_start)?;
            writeln!(
                &mut out_file,
                ";; IP{} -- {}:{}:{} -- {:?}",
                ip,
                source_store.name(op.location.file_id)?,
                location.line_number,
                location.column_number,
                op.code,
            )?;
            ip += 1;
        }
        out_file.write_all(&asm)?;

        ops = remaining_ops;
    }

    writeln!(&mut out_file, "    mov rax, 60")?;
    writeln!(&mut out_file, "    mov rdi, 0")?;
    writeln!(&mut out_file, "    syscall")?;
    writeln!(&mut out_file, "segment .bss")?;
    writeln!(&mut out_file, "    __memory: resb {}", MEMORY_CAPACITY)?;

    Ok(())
}
