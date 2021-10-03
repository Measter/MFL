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

fn compile_op(output: &mut impl Write, op: Op) -> Result<()> {
    match op.code {
        OpCode::Add => {
            writeln!(output, "    pop rax")?;
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    add rax, rbx")?;
            writeln!(output, "    push rax")?;
        }
        OpCode::Subtract => {
            writeln!(output, "    pop rax")?;
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    sub rbx, rax")?;
            writeln!(output, "    push rbx")?;
        }

        OpCode::BitAnd => {
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    and rax, rbx")?;
            writeln!(output, "    push rax")?;
        }
        OpCode::BitOr => {
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    or rax, rbx")?;
            writeln!(output, "    push rax")?;
        }
        OpCode::ShiftLeft => {
            writeln!(output, "    pop rcx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    shl rax, cl")?;
            writeln!(output, "    push rax")?;
        }
        OpCode::ShiftRight => {
            writeln!(output, "    pop rcx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    shr rax, cl")?;
            writeln!(output, "    push rax")?;
        }

        OpCode::Push(v) => {
            writeln!(output, "    mov rax, {}", v)?;
            writeln!(output, "    push rax")?;
        }
        OpCode::Drop => writeln!(output, "    pop rax")?,

        OpCode::Equal => {
            writeln!(output, "    mov rcx, 0")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    cmp rax, rbx")?;
            writeln!(output, "    sete cl")?;
            writeln!(output, "    push rcx")?;
        }
        OpCode::Less => {
            writeln!(output, "    mov rcx, 0")?;
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    cmp rax, rbx")?;
            writeln!(output, "    setl cl")?;
            writeln!(output, "    push rcx")?;
        }
        OpCode::Greater => {
            writeln!(output, "    mov rcx, 0")?;
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    cmp rax, rbx")?;
            writeln!(output, "    setg cl")?;
            writeln!(output, "    push rcx")?;
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
        OpCode::Dup => {
            writeln!(output, "    mov rax, [rsp]")?;
            writeln!(output, "    push rax")?;
        }
        OpCode::DupPair => {
            writeln!(output, "    mov rax, [rsp]")?;
            writeln!(output, "    mov rbx, [rsp+8]")?;
            writeln!(output, "    push rbx")?;
            writeln!(output, "    push rax")?;
        }
        OpCode::Over => {
            writeln!(output, "    mov rax, QWORD [rsp+8]")?;
            writeln!(output, "    push rax")?;
        }
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
            writeln!(output, "    xor rbx, rbx")?;
            writeln!(output, "    mov bl, BYTE [rax]")?;
            writeln!(output, "    push rbx")?;
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

    for (ip, &op) in program.iter().enumerate() {
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

        compile_op(&mut out_file, op)?;
    }

    writeln!(&mut out_file, "    mov rax, 60")?;
    writeln!(&mut out_file, "    mov rdi, 0")?;
    writeln!(&mut out_file, "    syscall")?;
    writeln!(&mut out_file, "segment .bss")?;
    writeln!(&mut out_file, "    __memory: resb {}", MEMORY_CAPACITY)?;

    Ok(())
}
