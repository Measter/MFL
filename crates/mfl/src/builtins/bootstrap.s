BITS 64
segment .text
extern entry
global _start
_start:
    pop RDI
    mov RSI, RSP

    call entry
    mov RAX, 60
    mov RDI, 0
    syscall
