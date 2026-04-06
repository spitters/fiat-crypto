/* BLS24-509 Fp2 Karatsuba multiplication in x86-64 assembly.
 *
 * Uses CryptOpt-generated fiat_bls24_509_p_mul as subroutine.
 * Keeps Karatsuba intermediates on a MINIMAL stack frame
 * instead of bedrock2's stackalloc pattern.
 *
 * Fp2 = Fp[u]/(u^2+1), so beta = -1.
 * (a0 + a1*u)(b0 + b1*u) = (a0*b0 - a1*b1) + ((a0+a1)(b0+b1) - a0*b0 - a1*b1)*u
 *
 * Algorithm (Karatsuba):
 *   d0 = a0 * b0
 *   d1 = a1 * b1
 *   t  = (a0 + a1)
 *   t2 = (b0 + b1)
 *   cross = t * t2
 *   out.c1 = cross - d0 - d1
 *   out.c0 = d0 - d1   (beta = -1, so d0 + beta*d1 = d0 - d1)
 *
 * Register usage:
 *   rdi = out pointer (preserved across calls)
 *   rsi = inx pointer (preserved)
 *   rdx = iny pointer (preserved, but clobbered by mul -- save to r13)
 *   Stack: 3 Fp temps (d0, d1, t) = 3*64 = 192 bytes
 *   Callee-saved: rbx, r12, r13, r14, r15, rbp
 *
 * Calling convention for fiat_bls24_509_p_mul(out, in0, in1):
 *   rdi=out, rsi=in0, rdx=in1 (SysV AMD64)
 *
 * Fp element = 8 x uint64_t = 64 bytes.
 * Fp2 element = 2 Fp = 128 bytes. c1 is at offset +64.
 */

.intel_syntax noprefix
.text
.globl bls24_Fp2_mul_asm
.type bls24_Fp2_mul_asm, @function
bls24_Fp2_mul_asm:
    /* Prologue: save callee-saved regs, allocate stack for 3 Fp temps */
    push rbx
    push r12
    push r13
    push r14
    push r15
    push rbp

    /* Allocate 3 Fp elements on stack (192 bytes, 64-byte aligned) */
    sub rsp, 192+8    /* +8 for 16-byte alignment (6 pushes = 48, need 48+200=248, 248%16=8) */

    /* Save arguments in callee-saved regs */
    mov r12, rdi      /* r12 = out */
    mov r13, rsi      /* r13 = inx */
    mov r14, rdx      /* r14 = iny */

    /* Stack layout:
     *   [rsp+0]    = d0  (64 bytes)
     *   [rsp+64]   = d1  (64 bytes)
     *   [rsp+128]  = t   (64 bytes)
     */

    /* ================================================ */
    /* Step 1: d0 = a0 * b0                             */
    /* ================================================ */
    lea rdi, [rsp]        /* d0 = output */
    mov rsi, r13          /* a0 = inx */
    mov rdx, r14          /* b0 = iny */
    call fiat_bls24_509_p_mul@PLT

    /* ================================================ */
    /* Step 2: d1 = a1 * b1                             */
    /* ================================================ */
    lea rdi, [rsp+64]     /* d1 = output */
    lea rsi, [r13+64]     /* a1 = inx + 64 */
    lea rdx, [r14+64]     /* b1 = iny + 64 */
    call fiat_bls24_509_p_mul@PLT

    /* ================================================ */
    /* Step 3: t = a0 + a1                              */
    /* ================================================ */
    lea rdi, [rsp+128]    /* t = output */
    mov rsi, r13          /* a0 */
    lea rdx, [r13+64]     /* a1 */
    call bls24_509_add@PLT

    /* ================================================ */
    /* Step 4: out.c1 = b0 + b1                         */
    /* ================================================ */
    lea rdi, [r12+64]     /* out.c1 = output */
    mov rsi, r14          /* b0 */
    lea rdx, [r14+64]     /* b1 */
    call bls24_509_add@PLT

    /* ================================================ */
    /* Step 5: out.c1 = out.c1 * t = (a0+a1)(b0+b1)    */
    /* ================================================ */
    lea rdi, [r12+64]     /* out.c1 = output (in-place) */
    lea rsi, [r12+64]     /* out.c1 = input */
    lea rdx, [rsp+128]    /* t = input */
    call fiat_bls24_509_p_mul@PLT

    /* ================================================ */
    /* Step 6: out.c1 -= d0                             */
    /* ================================================ */
    lea rdi, [r12+64]     /* out.c1 */
    lea rsi, [r12+64]     /* out.c1 */
    lea rdx, [rsp]        /* d0 */
    call bls24_509_sub@PLT

    /* ================================================ */
    /* Step 7: out.c1 -= d1                             */
    /* ================================================ */
    lea rdi, [r12+64]     /* out.c1 */
    lea rsi, [r12+64]     /* out.c1 */
    lea rdx, [rsp+64]     /* d1 */
    call bls24_509_sub@PLT

    /* ================================================ */
    /* Step 8: out.c0 = d0 - d1  (since beta = -1)     */
    /* ================================================ */
    mov rdi, r12          /* out.c0 */
    lea rsi, [rsp]        /* d0 */
    lea rdx, [rsp+64]     /* d1 */
    call bls24_509_sub@PLT

    /* Epilogue */
    add rsp, 192+8
    pop rbp
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret

.size bls24_Fp2_mul_asm, .-bls24_Fp2_mul_asm

/* Prevent executable stack */
.section .note.GNU-stack, "", @progbits
