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
        match op.code {
            OpCode::Add => {
                writeln!(&mut out_file, "    pop rax")?;
                writeln!(&mut out_file, "    pop rbx")?;
                writeln!(&mut out_file, "    add rax, rbx")?;
                writeln!(&mut out_file, "    push rax")?;
            }
            OpCode::Subtract => {
                writeln!(&mut out_file, "    pop rax")?;
                writeln!(&mut out_file, "    pop rbx")?;
                writeln!(&mut out_file, "    sub rbx, rax")?;
                writeln!(&mut out_file, "    push rbx")?;
            }

            OpCode::Push(v) => {
                writeln!(&mut out_file, "    push {}", v)?;
            }

            OpCode::Equal => {
                writeln!(&mut out_file, "    mov rcx, 0")?;
                writeln!(&mut out_file, "    pop rax")?;
                writeln!(&mut out_file, "    pop rbx")?;
                writeln!(&mut out_file, "    cmp rax, rbx")?;
                writeln!(&mut out_file, "    sete cl")?;
                writeln!(&mut out_file, "    push rcx")?;
            }
            OpCode::Less => {
                writeln!(&mut out_file, "    mov rcx, 0")?;
                writeln!(&mut out_file, "    pop rbx")?;
                writeln!(&mut out_file, "    pop rax")?;
                writeln!(&mut out_file, "    cmp rax, rbx")?;
                writeln!(&mut out_file, "    setl cl")?;
                writeln!(&mut out_file, "    push rcx")?;
            }
            OpCode::Greater => {
                writeln!(&mut out_file, "    mov rcx, 0")?;
                writeln!(&mut out_file, "    pop rbx")?;
                writeln!(&mut out_file, "    pop rax")?;
                writeln!(&mut out_file, "    cmp rax, rbx")?;
                writeln!(&mut out_file, "    setg cl")?;
                writeln!(&mut out_file, "    push rcx")?;
            }

            OpCode::While { ip } => {
                writeln!(&mut out_file, ".LBL{}:", ip)?;
            }
            OpCode::Do { end_ip, .. } => {
                writeln!(&mut out_file, "    pop rax")?;
                writeln!(&mut out_file, "    test rax, rax")?;
                writeln!(&mut out_file, "    jz .LBL{}", end_ip)?;
            }
            OpCode::EndWhile {
                condition_ip,
                end_ip,
            } => {
                writeln!(&mut out_file, "    jmp .LBL{}", condition_ip)?;
                writeln!(&mut out_file, ".LBL{}:", end_ip)?;
            }

            OpCode::If { end_ip, .. } => {
                writeln!(&mut out_file, "    pop rax")?;
                writeln!(&mut out_file, "    test rax, rax")?;
                writeln!(&mut out_file, "    jz .LBL{}", end_ip)?;
            }
            OpCode::Else { end_ip, else_start } => {
                writeln!(&mut out_file, "    jmp .LBL{}", end_ip)?;
                writeln!(&mut out_file, ".LBL{}:", else_start)?;
            }
            OpCode::EndIf { ip } => {
                writeln!(&mut out_file, ".LBL{}:", ip)?;
            }

            OpCode::Dump => {
                writeln!(&mut out_file, "    pop rdi")?;
                writeln!(&mut out_file, "    call dump")?;
            }
            OpCode::Dup => {
                writeln!(&mut out_file, "    pop rax")?;
                writeln!(&mut out_file, "    push rax")?;
                writeln!(&mut out_file, "    push rax")?;
            }
            OpCode::Mem => writeln!(&mut out_file, "    push __memory")?,
        }
    }

    writeln!(&mut out_file, "    mov rax, 60")?;
    writeln!(&mut out_file, "    mov rdi, 0")?;
    writeln!(&mut out_file, "    syscall")?;
    writeln!(&mut out_file, "segment .bss")?;
    writeln!(&mut out_file, "    __memory: resb {}", MEMORY_CAPACITY)?;

    Ok(())
}
