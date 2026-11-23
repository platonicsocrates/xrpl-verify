# Process entry point. No C library: load argc and argv from the initial
# stack, call main, and pass its result to exit(2).
.section .text
.globl _start
_start:
    ld   a0, 0(sp)        # argc
    addi a1, sp, 8        # argv
    call main
    li   a7, 93           # __NR_exit
    ecall
