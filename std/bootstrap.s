BITS 64
segment .text
extern entry
global _start
_start:
    call entry
    mov RAX, 60
    mov RDI, 0
    syscall

global _syscall3
_syscall3:
    mov RAX, RDI
    mov EDI, ESI
    mov RSI, RDX
    mov RDX, RCX
    syscall

    ret