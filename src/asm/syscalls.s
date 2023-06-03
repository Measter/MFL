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


; Input:
;   * RDI: U8 pointer to location string
;   * RSI: Location string length
;   * RDX: Access index
;   * RCX: Array length
global _oob
_oob:
    mov R15, RCX ; Array Length
    mov R14, RDX ; Access index
    mov R13, RSI ; Loc len
    mov R12, RDI ; Loc ptr

    mov RDX, oob_msg_len ; Msg len
    mov RSI, oob_msg ; Msg ptr
    mov RDI, 1   ; Stdout
    mov RAX, 1   ; Write
    syscall

    mov RDX, loc_msg_len ; Msg len
    mov RSI, loc_msg ; Msg ptr
    mov RDI, 1   ; Stdout
    mov RAX, 1   ; Write
    syscall

    mov RDX, R13 ; Msg len
    mov RSI, R12 ; Msg ptr
    mov RDI, 1   ; Stdout
    mov RAX, 1   ; Write
    syscall

    mov RDX, new_line_len ; Msg len
    mov RSI, new_line ; Msg ptr
    mov RDI, 1   ; Stdout
    mov RAX, 1   ; Write
    syscall

    mov RDX, idx_msg_len ; Msg len
    mov RSI, idx_msg ; Msg ptr
    mov RDI, 1   ; Stdout
    mov RAX, 1   ; Write
    syscall

    ; Render idx
    mov RSI, num_buf_end
    mov RAX, R14
    mov R14, 0
    mov R10, 10
    cmp RAX, 0
    ; Is not 0
    jg .loop1_start

    ; Is 0
    mov RDX, 1
    mov byte [RSI], '0'
    jmp .loop1_end
    .loop1_start:
    ; RAX: index
    ; RSI: cur char ptr
    ; R14: cur buffer length
    ; R10: Divisor
    mov RDX, 0
    div R10
    add RDX, '0'
    mov byte [RSI], DL
    sub RSI, 1
    add R14, 1

    cmp RAX, 0
    jg .loop1_start
    mov RDX, R14 
    add RSI, 1

    .loop1_end:
    mov RDI, 1
    mov RAX, 1
    syscall

    mov RDX, new_line_len ; Msg len
    mov RSI, new_line ; Msg ptr
    mov RDI, 1   ; Stdout
    mov RAX, 1   ; Write
    syscall

    mov RDX, len_msg_len ; Msg len
    mov RSI, len_msg ; Msg ptr
    mov RDI, 1   ; Stdout
    mov RAX, 1   ; Write
    syscall

    ; Render array length
    mov RSI, num_buf_end
    mov RAX, R15
    mov R14, 0
    mov R10, 10
    cmp RAX, 0
    ; Is not 0
    jg .loop2_start

    ; Is 0
    mov RDX, 1
    mov byte [RSI], '0'
    jmp .loop2_end
    .loop2_start:
    ; RAX: index
    ; RSI: cur char ptr
    ; R14: cur buffer length
    ; R10: Divisor
    mov RDX, 0
    div R10
    add RDX, '0'
    mov byte [RSI], DL
    sub RSI, 1
    add R14, 1

    cmp RAX, 0
    jg .loop2_start
    mov RDX, R14 
    add RSI, 1

    .loop2_end:
    mov RDI, 1
    mov RAX, 1
    syscall

    mov RDX, new_line_len ; Msg len
    mov RSI, new_line ; Msg ptr
    mov RDI, 1   ; Stdout
    mov RAX, 1   ; Write
    syscall

    mov RAX, 60
    mov RDI, 1
    syscall

segment .data
num_buf times 30 db 0
num_buf_end equ $ - 1
oob_msg db 'Error: Index out of bounds', 10
oob_msg_len equ $ - oob_msg 
loc_msg db 'Location: '
loc_msg_len equ $ - loc_msg
idx_msg db 'Index: '
idx_msg_len equ $ - idx_msg
len_msg db 'Array Length: '
len_msg_len equ $ - len_msg
new_line db 10
new_line_len equ 1