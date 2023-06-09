BITS 64
segment .text

global _syscall2
_syscall2:
    mov RAX, RDI
    mov EDI, ESI
    syscall

    ret

global _syscall3
_syscall3:
    mov RAX, RDI
    mov EDI, ESI
    mov RSI, RDX
    syscall

    ret

global _syscall4
_syscall4:
    mov RAX, RDI
    mov EDI, ESI
    mov RSI, RDX
    mov RDX, RCX
    syscall

    ret

global _syscall7
_syscall7:
    mov RAX, RDI
    mov RDI, RSI
    mov RSI, RDX
    mov RDX, RCX
    mov R10, R8
    mov R8, R9
    mov R9, [RSP+8]
    syscall

    ret
