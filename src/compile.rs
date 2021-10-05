use std::{
    fs::File,
    io::{BufWriter, Write},
    path::Path,
};

use codespan_reporting::files::Files;
use color_eyre::eyre::{eyre, Context, Result};

use crate::{
    compile::optimizer_passes::pass_through,
    interners::Interners,
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
            OpCode::Multiply => ("mul", big_b),
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
            OpCode::GreaterEqual => "setge",
            OpCode::Less => "setl",
            OpCode::LessEqual => "setle",
            OpCode::NotEq => "setne",
            _ => panic!("ICE: Attempted to compile_compare_op a {:?}", self),
        }
    }
}

fn compile_op(output: &mut impl Write, op: Op, interner: &Interners) -> Result<()> {
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

        // The multiply operator is dumb :(
        OpCode::Multiply => {
            writeln!(output, "    pop rax")?;
            writeln!(output, "    mul QWORD [rsp]")?;
            writeln!(output, "    mov QWORD [rsp], rax")?;
        }
        OpCode::DivMod => {
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    xor rdx, rdx")?;
            writeln!(output, "    div rbx")?;
            writeln!(output, "    push rax")?;
            writeln!(output, "    push rdx")?;
        }

        OpCode::PushInt(v) => writeln!(output, "    push {}", v)?,
        OpCode::PushStr(id) => {
            let literal = interner.resolve_literal(id);
            let id = id.into_inner().get();

            writeln!(output, "    push {}", literal.len())?;
            writeln!(output, "    push __string_literal{}", id)?;
            // unimplemented!()
        }
        OpCode::Drop => writeln!(output, "    pop rax")?,

        OpCode::Equal
        | OpCode::Less
        | OpCode::LessEqual
        | OpCode::Greater
        | OpCode::GreaterEqual
        | OpCode::NotEq => {
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    pop rax")?;
            writeln!(output, "    cmp rax, rbx")?;
            writeln!(output, "    {} r15b", op.code.compile_compare_op())?;
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
        OpCode::Dup { depth } => {
            writeln!(output, "    push QWORD [rsp + 8*{}]", depth)?;
        }
        OpCode::DupPair => {
            writeln!(output, "    push QWORD [rsp+8]")?;
            writeln!(output, "    push QWORD [rsp+8]")?;
        }
        OpCode::Swap => {
            writeln!(output, "    pop rax")?;
            writeln!(output, "    pop rbx")?;
            writeln!(output, "    push rax")?;
            writeln!(output, "    push rbx")?;
        }

        OpCode::Mem { offset } => writeln!(output, "    push __memory + {}", offset)?,
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
        OpCode::Ident(_) => {
            panic!("ICE: Encountered OpCode::Ident")
        }
        OpCode::Include(_) => {
            panic!("ICE: Encountered OpCode::Include")
        }
    }

    Ok(())
}

fn try_optimize<'a>(interner: &Interners, ops: &'a [Op]) -> (Vec<u8>, &'a [Op], &'a [Op]) {
    PASSES
        .iter()
        .filter_map(|pass| pass(interner, ops))
        .next()
        .unwrap()
}

pub(crate) fn compile_program(
    program: &[Op],
    source_store: &SourceStorage,
    interner: &Interners,
    out_file_path: &Path,
    optimize: bool,
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
        let (asm, compiled_ops, remaining_ops) = if optimize {
            try_optimize(interner, ops)
        } else {
            pass_through(interner, ops).unwrap()
        };

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
    writeln!(&mut out_file, "    __memory: resb {}", MEMORY_CAPACITY)?;

    Ok(())
}
