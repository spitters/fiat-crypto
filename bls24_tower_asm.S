/* BLS24-509 complete tower assembly: Fp2, Fp4, Fp8, Fp24 mul/sqr.
 *
 * Each level uses Karatsuba with a minimal stack frame for temporaries,
 * calling the level below as subroutines.
 * Fp base ops (mul/sqr/add/sub/opp) are extern (bedrock2 or CryptOpt).
 *
 * Element sizes:  Fp=64  Fp2=128  Fp4=256  Fp8=512  Fp24=1536
 * Nonresidues:    Fp2: beta=-1   Fp4: xi=1+u   Fp8: v   Fp24: w (cubic)
 *
 * Calling convention: SysV AMD64 (rdi=out, rsi=in0, rdx=in1)
 * Callee-saved: rbx, r12, r13, r14, r15, rbp
 */

.intel_syntax noprefix
.text

/* ================================================================
   Helper: Fp2_mul_xi  (multiply by xi = 1+u)
   (a+bu)(1+u) = (a-b) + (a+b)u
   Stack: 64 bytes for tmp
   ================================================================ */
.globl bls24_Fp2_mul_xi_asm
.type bls24_Fp2_mul_xi_asm, @function
bls24_Fp2_mul_xi_asm:
    push rbx
    push r12
    sub rsp, 72          /* 64 bytes tmp + 8 alignment */
    mov r12, rdi         /* out */
    mov rbx, rsi         /* x */
    /* tmp = a + b */
    lea rdi, [rsp]
    mov rsi, rbx
    lea rdx, [rbx+64]
    call bls24_509_add@PLT
    /* out.c0 = a - b */
    mov rdi, r12
    mov rsi, rbx
    lea rdx, [rbx+64]
    call bls24_509_sub@PLT
    /* out.c1 = tmp (memcpy 64 bytes) */
    lea rdi, [r12+64]
    lea rsi, [rsp]
    mov ecx, 8
.Lxi_copy:
    mov rax, [rsi]
    mov [rdi], rax
    add rsi, 8
    add rdi, 8
    dec ecx
    jnz .Lxi_copy
    add rsp, 72
    pop r12
    pop rbx
    ret
.size bls24_Fp2_mul_xi_asm, .-bls24_Fp2_mul_xi_asm

/* ================================================================
   Fp2_mul:  3 Fp_mul + 2 Fp_add + 2 Fp_sub + 1 Fp_opp
   Stack: 192 bytes (3 Fp temps: d0, d1, t)
   ================================================================ */
.globl bls24_Fp2_mul_asm
.type bls24_Fp2_mul_asm, @function
bls24_Fp2_mul_asm:
    push rbx
    push r12
    push r13
    push r14
    push r15
    push rbp
    sub rsp, 200         /* 192 + 8 alignment */
    mov r12, rdi         /* out */
    mov r13, rsi         /* inx */
    mov r14, rdx         /* iny */
    /* d0 = a0*b0 */
    lea rdi, [rsp]
    mov rsi, r13
    mov rdx, r14
    call fiat_bls24_509_p_mul@PLT
    /* d1 = a1*b1 */
    lea rdi, [rsp+64]
    lea rsi, [r13+64]
    lea rdx, [r14+64]
    call fiat_bls24_509_p_mul@PLT
    /* t = a0+a1 */
    lea rdi, [rsp+128]
    mov rsi, r13
    lea rdx, [r13+64]
    call bls24_509_add@PLT
    /* out.c1 = b0+b1 */
    lea rdi, [r12+64]
    mov rsi, r14
    lea rdx, [r14+64]
    call bls24_509_add@PLT
    /* out.c1 = (a0+a1)(b0+b1) */
    lea rdi, [r12+64]
    lea rsi, [r12+64]
    lea rdx, [rsp+128]
    call fiat_bls24_509_p_mul@PLT
    /* out.c1 -= d0 */
    lea rdi, [r12+64]
    lea rsi, [r12+64]
    lea rdx, [rsp]
    call bls24_509_sub@PLT
    /* out.c1 -= d1 */
    lea rdi, [r12+64]
    lea rsi, [r12+64]
    lea rdx, [rsp+64]
    call bls24_509_sub@PLT
    /* out.c0 = d0 - d1 (beta=-1) */
    mov rdi, r12
    lea rsi, [rsp]
    lea rdx, [rsp+64]
    call bls24_509_sub@PLT
    add rsp, 200
    pop rbp
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp2_mul_asm, .-bls24_Fp2_mul_asm

/* ================================================================
   Fp2_square:  2 Fp_sqr + 1 Fp_mul + 1 Fp_add + 1 Fp_sub
   Stack: 192 bytes (d0, d1, cross)
   ================================================================ */
.globl bls24_Fp2_square_asm
.type bls24_Fp2_square_asm, @function
bls24_Fp2_square_asm:
    push rbx
    push r12
    push r13
    push rbp
    sub rsp, 200
    mov r12, rdi         /* out */
    mov r13, rsi         /* x */
    /* d0 = a0^2 */
    lea rdi, [rsp]
    mov rsi, r13
    call fiat_bls24_509_p_square@PLT
    /* d1 = a1^2 */
    lea rdi, [rsp+64]
    lea rsi, [r13+64]
    call fiat_bls24_509_p_square@PLT
    /* cross = a0*a1 */
    lea rdi, [rsp+128]
    mov rsi, r13
    lea rdx, [r13+64]
    call fiat_bls24_509_p_mul@PLT
    /* out.c1 = 2*cross */
    lea rdi, [r12+64]
    lea rsi, [rsp+128]
    lea rdx, [rsp+128]
    call bls24_509_add@PLT
    /* out.c0 = d0 - d1 */
    mov rdi, r12
    lea rsi, [rsp]
    lea rdx, [rsp+64]
    call bls24_509_sub@PLT
    add rsp, 200
    pop rbp
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp2_square_asm, .-bls24_Fp2_square_asm

/* ================================================================
   Fp2_add / Fp2_sub / Fp2_opp  (thin wrappers, 2 Fp ops each)
   ================================================================ */
.globl bls24_Fp2_add_asm
.type bls24_Fp2_add_asm, @function
bls24_Fp2_add_asm:
    push rbx
    push r12
    push r13
    mov r12, rdi
    mov r13, rsi
    mov rbx, rdx
    /* c0 */
    mov rdi, r12
    mov rsi, r13
    mov rdx, rbx
    call bls24_509_add@PLT
    /* c1 */
    lea rdi, [r12+64]
    lea rsi, [r13+64]
    lea rdx, [rbx+64]
    call bls24_509_add@PLT
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp2_add_asm, .-bls24_Fp2_add_asm

.globl bls24_Fp2_sub_asm
.type bls24_Fp2_sub_asm, @function
bls24_Fp2_sub_asm:
    push rbx
    push r12
    push r13
    mov r12, rdi
    mov r13, rsi
    mov rbx, rdx
    mov rdi, r12
    mov rsi, r13
    mov rdx, rbx
    call bls24_509_sub@PLT
    lea rdi, [r12+64]
    lea rsi, [r13+64]
    lea rdx, [rbx+64]
    call bls24_509_sub@PLT
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp2_sub_asm, .-bls24_Fp2_sub_asm

/* ================================================================
   Fp4_mul:  3 Fp2_mul + 2 Fp2_add + 2 Fp2_sub + 1 Fp2_mul_xi
   Stack: 384 bytes (3 Fp2 temps)
   ================================================================ */
.globl bls24_Fp4_mul_asm
.type bls24_Fp4_mul_asm, @function
bls24_Fp4_mul_asm:
    push rbx
    push r12
    push r13
    push r14
    push r15
    push rbp
    sub rsp, 392         /* 384 + 8 align */
    mov r12, rdi         /* out */
    mov r13, rsi         /* inx */
    mov r14, rdx         /* iny */
    /* d0 = x.c0 * y.c0 */
    lea rdi, [rsp]
    mov rsi, r13
    mov rdx, r14
    call bls24_Fp2_mul_asm@PLT
    /* d1 = x.c1 * y.c1 */
    lea rdi, [rsp+128]
    lea rsi, [r13+128]
    lea rdx, [r14+128]
    call bls24_Fp2_mul_asm@PLT
    /* t = x.c0 + x.c1 */
    lea rdi, [rsp+256]
    mov rsi, r13
    lea rdx, [r13+128]
    call bls24_Fp2_add_asm@PLT
    /* out.c1 = y.c0 + y.c1 */
    lea rdi, [r12+128]
    mov rsi, r14
    lea rdx, [r14+128]
    call bls24_Fp2_add_asm@PLT
    /* out.c1 = (x.c0+x.c1)(y.c0+y.c1) */
    lea rdi, [r12+128]
    lea rsi, [r12+128]
    lea rdx, [rsp+256]
    call bls24_Fp2_mul_asm@PLT
    /* out.c1 -= d0 */
    lea rdi, [r12+128]
    lea rsi, [r12+128]
    lea rdx, [rsp]
    call bls24_Fp2_sub_asm@PLT
    /* out.c1 -= d1 */
    lea rdi, [r12+128]
    lea rsi, [r12+128]
    lea rdx, [rsp+128]
    call bls24_Fp2_sub_asm@PLT
    /* t = mul_xi(d1) — nonresidue for Fp4 is xi=1+u */
    lea rdi, [rsp+256]
    lea rsi, [rsp+128]
    call bls24_Fp2_mul_xi_asm@PLT
    /* out.c0 = d0 + xi*d1 */
    mov rdi, r12
    lea rsi, [rsp]
    lea rdx, [rsp+256]
    call bls24_Fp2_add_asm@PLT
    add rsp, 392
    pop rbp
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp4_mul_asm, .-bls24_Fp4_mul_asm

/* ================================================================
   Fp4_square:  2 Fp2_sqr + 1 Fp2_mul + 1 Fp2_add + 1 Fp2_mul_xi
   Stack: 384 bytes
   ================================================================ */
.globl bls24_Fp4_square_asm
.type bls24_Fp4_square_asm, @function
bls24_Fp4_square_asm:
    push rbx
    push r12
    push r13
    push rbp
    sub rsp, 392
    mov r12, rdi
    mov r13, rsi
    /* d0 = c0^2 */
    lea rdi, [rsp]
    mov rsi, r13
    call bls24_Fp2_square_asm@PLT
    /* d1 = c1^2 */
    lea rdi, [rsp+128]
    lea rsi, [r13+128]
    call bls24_Fp2_square_asm@PLT
    /* cross = c0*c1 */
    lea rdi, [rsp+256]
    mov rsi, r13
    lea rdx, [r13+128]
    call bls24_Fp2_mul_asm@PLT
    /* out.c1 = 2*cross */
    lea rdi, [r12+128]
    lea rsi, [rsp+256]
    lea rdx, [rsp+256]
    call bls24_Fp2_add_asm@PLT
    /* t = mul_xi(d1) */
    lea rdi, [rsp+256]
    lea rsi, [rsp+128]
    call bls24_Fp2_mul_xi_asm@PLT
    /* out.c0 = d0 + xi*d1 */
    mov rdi, r12
    lea rsi, [rsp]
    lea rdx, [rsp+256]
    call bls24_Fp2_add_asm@PLT
    add rsp, 392
    pop rbp
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp4_square_asm, .-bls24_Fp4_square_asm

/* ================================================================
   Fp4_add / Fp4_sub  (2 Fp2 ops each)
   ================================================================ */
.globl bls24_Fp4_add_asm
.type bls24_Fp4_add_asm, @function
bls24_Fp4_add_asm:
    push rbx
    push r12
    push r13
    mov r12, rdi
    mov r13, rsi
    mov rbx, rdx
    mov rdi, r12
    mov rsi, r13
    mov rdx, rbx
    call bls24_Fp2_add_asm@PLT
    lea rdi, [r12+128]
    lea rsi, [r13+128]
    lea rdx, [rbx+128]
    call bls24_Fp2_add_asm@PLT
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp4_add_asm, .-bls24_Fp4_add_asm

.globl bls24_Fp4_sub_asm
.type bls24_Fp4_sub_asm, @function
bls24_Fp4_sub_asm:
    push rbx
    push r12
    push r13
    mov r12, rdi
    mov r13, rsi
    mov rbx, rdx
    mov rdi, r12
    mov rsi, r13
    mov rdx, rbx
    call bls24_Fp2_sub_asm@PLT
    lea rdi, [r12+128]
    lea rsi, [r13+128]
    lea rdx, [rbx+128]
    call bls24_Fp2_sub_asm@PLT
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp4_sub_asm, .-bls24_Fp4_sub_asm

/* ================================================================
   Fp4_mul_by_v:  (a+bx)*x = b*xi + a*x  =>  out.c0=mul_xi(c1), out.c1=c0
   Stack: 128 bytes (1 Fp2 temp)
   ================================================================ */
.globl bls24_Fp4_mul_by_v_asm
.type bls24_Fp4_mul_by_v_asm, @function
bls24_Fp4_mul_by_v_asm:
    push rbx
    push r12
    sub rsp, 136
    mov r12, rdi
    mov rbx, rsi
    /* tmp = mul_xi(c1) */
    lea rdi, [rsp]
    lea rsi, [rbx+128]
    call bls24_Fp2_mul_xi_asm@PLT
    /* out.c1 = c0 (memcpy 128 bytes) */
    lea rdi, [r12+128]
    mov rsi, rbx
    mov ecx, 16
.Lv_copy:
    mov rax, [rsi]
    mov [rdi], rax
    add rsi, 8
    add rdi, 8
    dec ecx
    jnz .Lv_copy
    /* out.c0 = tmp */
    mov rdi, r12
    lea rsi, [rsp]
    mov ecx, 16
.Lv_copy2:
    mov rax, [rsi]
    mov [rdi], rax
    add rsi, 8
    add rdi, 8
    dec ecx
    jnz .Lv_copy2
    add rsp, 136
    pop r12
    pop rbx
    ret
.size bls24_Fp4_mul_by_v_asm, .-bls24_Fp4_mul_by_v_asm

/* ================================================================
   Fp8_mul:  3 Fp4_mul + 2 Fp4_add + 2 Fp4_sub + 1 Fp4_mul_by_v
   Stack: 768 bytes (3 Fp4 temps)
   ================================================================ */
.globl bls24_Fp8_mul_asm
.type bls24_Fp8_mul_asm, @function
bls24_Fp8_mul_asm:
    push rbx
    push r12
    push r13
    push r14
    push r15
    push rbp
    sub rsp, 776
    mov r12, rdi
    mov r13, rsi
    mov r14, rdx
    /* d0 = x.c0 * y.c0 */
    lea rdi, [rsp]
    mov rsi, r13
    mov rdx, r14
    call bls24_Fp4_mul_asm@PLT
    /* d1 = x.c1 * y.c1 */
    lea rdi, [rsp+256]
    lea rsi, [r13+256]
    lea rdx, [r14+256]
    call bls24_Fp4_mul_asm@PLT
    /* t = x.c0 + x.c1 */
    lea rdi, [rsp+512]
    mov rsi, r13
    lea rdx, [r13+256]
    call bls24_Fp4_add_asm@PLT
    /* out.c1 = y.c0 + y.c1 */
    lea rdi, [r12+256]
    mov rsi, r14
    lea rdx, [r14+256]
    call bls24_Fp4_add_asm@PLT
    /* out.c1 = (x.c0+x.c1)(y.c0+y.c1) */
    lea rdi, [r12+256]
    lea rsi, [r12+256]
    lea rdx, [rsp+512]
    call bls24_Fp4_mul_asm@PLT
    /* out.c1 -= d0 */
    lea rdi, [r12+256]
    lea rsi, [r12+256]
    lea rdx, [rsp]
    call bls24_Fp4_sub_asm@PLT
    /* out.c1 -= d1 */
    lea rdi, [r12+256]
    lea rsi, [r12+256]
    lea rdx, [rsp+256]
    call bls24_Fp4_sub_asm@PLT
    /* t = mul_by_v(d1) — nonresidue for Fp8 */
    lea rdi, [rsp+512]
    lea rsi, [rsp+256]
    call bls24_Fp4_mul_by_v_asm@PLT
    /* out.c0 = d0 + v*d1 */
    mov rdi, r12
    lea rsi, [rsp]
    lea rdx, [rsp+512]
    call bls24_Fp4_add_asm@PLT
    add rsp, 776
    pop rbp
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp8_mul_asm, .-bls24_Fp8_mul_asm

/* ================================================================
   Fp8_square
   ================================================================ */
.globl bls24_Fp8_square_asm
.type bls24_Fp8_square_asm, @function
bls24_Fp8_square_asm:
    push rbx
    push r12
    push r13
    push rbp
    sub rsp, 776
    mov r12, rdi
    mov r13, rsi
    lea rdi, [rsp]
    mov rsi, r13
    call bls24_Fp4_square_asm@PLT
    lea rdi, [rsp+256]
    lea rsi, [r13+256]
    call bls24_Fp4_square_asm@PLT
    lea rdi, [rsp+512]
    mov rsi, r13
    lea rdx, [r13+256]
    call bls24_Fp4_mul_asm@PLT
    lea rdi, [r12+256]
    lea rsi, [rsp+512]
    lea rdx, [rsp+512]
    call bls24_Fp4_add_asm@PLT
    lea rdi, [rsp+512]
    lea rsi, [rsp+256]
    call bls24_Fp4_mul_by_v_asm@PLT
    mov rdi, r12
    lea rsi, [rsp]
    lea rdx, [rsp+512]
    call bls24_Fp4_add_asm@PLT
    add rsp, 776
    pop rbp
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp8_square_asm, .-bls24_Fp8_square_asm

/* Fp8 add/sub */
.globl bls24_Fp8_add_asm
.type bls24_Fp8_add_asm, @function
bls24_Fp8_add_asm:
    push rbx
    push r12
    push r13
    mov r12, rdi
    mov r13, rsi
    mov rbx, rdx
    mov rdi, r12
    mov rsi, r13
    mov rdx, rbx
    call bls24_Fp4_add_asm@PLT
    lea rdi, [r12+256]
    lea rsi, [r13+256]
    lea rdx, [rbx+256]
    call bls24_Fp4_add_asm@PLT
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp8_add_asm, .-bls24_Fp8_add_asm

.globl bls24_Fp8_sub_asm
.type bls24_Fp8_sub_asm, @function
bls24_Fp8_sub_asm:
    push rbx
    push r12
    push r13
    mov r12, rdi
    mov r13, rsi
    mov rbx, rdx
    mov rdi, r12
    mov rsi, r13
    mov rdx, rbx
    call bls24_Fp4_sub_asm@PLT
    lea rdi, [r12+256]
    lea rsi, [r13+256]
    lea rdx, [rbx+256]
    call bls24_Fp4_sub_asm@PLT
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp8_sub_asm, .-bls24_Fp8_sub_asm

/* Fp8 mul_by_w: (a+bv)*v = b*v_nr + a*v => out.c0=mul_by_v(c1), out.c1=c0 */
.globl bls24_Fp8_mul_by_w_asm
.type bls24_Fp8_mul_by_w_asm, @function
bls24_Fp8_mul_by_w_asm:
    push rbx
    push r12
    sub rsp, 264
    mov r12, rdi
    mov rbx, rsi
    lea rdi, [rsp]
    lea rsi, [rbx+256]
    call bls24_Fp4_mul_by_v_asm@PLT
    /* out.c1 = c0 (memcpy 256 bytes) */
    lea rdi, [r12+256]
    mov rsi, rbx
    mov ecx, 32
.Lw_copy:
    mov rax, [rsi]
    mov [rdi], rax
    add rsi, 8
    add rdi, 8
    dec ecx
    jnz .Lw_copy
    /* out.c0 = tmp */
    mov rdi, r12
    lea rsi, [rsp]
    mov ecx, 32
.Lw_copy2:
    mov rax, [rsi]
    mov [rdi], rax
    add rsi, 8
    add rdi, 8
    dec ecx
    jnz .Lw_copy2
    add rsp, 264
    pop r12
    pop rbx
    ret
.size bls24_Fp8_mul_by_w_asm, .-bls24_Fp8_mul_by_w_asm

/* ================================================================
   Fp24_mul:  Karatsuba cubic (6 Fp8_mul + adds/subs + mul_by_w)
   Stack: 3072 bytes (6 Fp8 temps: a0b0, a1b1, a2b2, t0, t1, t2)
   ================================================================ */
.globl bls24_Fp24_mul_asm
.type bls24_Fp24_mul_asm, @function
bls24_Fp24_mul_asm:
    push rbx
    push r12
    push r13
    push r14
    push r15
    push rbp
    sub rsp, 3080        /* 3072 + 8 align */
    mov r12, rdi         /* out */
    mov r13, rsi         /* inx */
    mov r14, rdx         /* iny */
    /* Stack: [0]=a0b0 [512]=a1b1 [1024]=a2b2 [1536]=t0 [2048]=t1 [2560]=t2 */

    /* a0b0 = x.c0 * y.c0 */
    lea rdi, [rsp]
    mov rsi, r13
    mov rdx, r14
    call bls24_Fp8_mul_asm@PLT
    /* a1b1 = x.c1 * y.c1 */
    lea rdi, [rsp+512]
    lea rsi, [r13+512]
    lea rdx, [r14+512]
    call bls24_Fp8_mul_asm@PLT
    /* a2b2 = x.c2 * y.c2 */
    lea rdi, [rsp+1024]
    lea rsi, [r13+1024]
    lea rdx, [r14+1024]
    call bls24_Fp8_mul_asm@PLT

    /* c0 = a0b0 + w*((a1+a2)(b1+b2) - a1b1 - a2b2) */
    lea rdi, [rsp+1536]
    lea rsi, [r13+512]
    lea rdx, [r13+1024]
    call bls24_Fp8_add_asm@PLT
    lea rdi, [rsp+2048]
    lea rsi, [r14+512]
    lea rdx, [r14+1024]
    call bls24_Fp8_add_asm@PLT
    lea rdi, [rsp+1536]
    lea rsi, [rsp+1536]
    lea rdx, [rsp+2048]
    call bls24_Fp8_mul_asm@PLT
    lea rdi, [rsp+1536]
    lea rsi, [rsp+1536]
    lea rdx, [rsp+512]
    call bls24_Fp8_sub_asm@PLT
    lea rdi, [rsp+1536]
    lea rsi, [rsp+1536]
    lea rdx, [rsp+1024]
    call bls24_Fp8_sub_asm@PLT
    lea rdi, [rsp+1536]
    lea rsi, [rsp+1536]
    call bls24_Fp8_mul_by_w_asm@PLT
    mov rdi, r12
    lea rsi, [rsp]
    lea rdx, [rsp+1536]
    call bls24_Fp8_add_asm@PLT

    /* c1 = (a0+a1)(b0+b1) - a0b0 - a1b1 + w*a2b2 */
    lea rdi, [rsp+1536]
    mov rsi, r13
    lea rdx, [r13+512]
    call bls24_Fp8_add_asm@PLT
    lea rdi, [rsp+2048]
    mov rsi, r14
    lea rdx, [r14+512]
    call bls24_Fp8_add_asm@PLT
    lea rdi, [rsp+1536]
    lea rsi, [rsp+1536]
    lea rdx, [rsp+2048]
    call bls24_Fp8_mul_asm@PLT
    lea rdi, [rsp+1536]
    lea rsi, [rsp+1536]
    lea rdx, [rsp]
    call bls24_Fp8_sub_asm@PLT
    lea rdi, [rsp+1536]
    lea rsi, [rsp+1536]
    lea rdx, [rsp+512]
    call bls24_Fp8_sub_asm@PLT
    lea rdi, [rsp+2048]
    lea rsi, [rsp+1024]
    call bls24_Fp8_mul_by_w_asm@PLT
    lea rdi, [r12+512]
    lea rsi, [rsp+1536]
    lea rdx, [rsp+2048]
    call bls24_Fp8_add_asm@PLT

    /* c2 = (a0+a2)(b0+b2) - a0b0 - a2b2 + a1b1 */
    lea rdi, [rsp+1536]
    mov rsi, r13
    lea rdx, [r13+1024]
    call bls24_Fp8_add_asm@PLT
    lea rdi, [rsp+2048]
    mov rsi, r14
    lea rdx, [r14+1024]
    call bls24_Fp8_add_asm@PLT
    lea rdi, [rsp+1536]
    lea rsi, [rsp+1536]
    lea rdx, [rsp+2048]
    call bls24_Fp8_mul_asm@PLT
    lea rdi, [rsp+1536]
    lea rsi, [rsp+1536]
    lea rdx, [rsp]
    call bls24_Fp8_sub_asm@PLT
    lea rdi, [rsp+1536]
    lea rsi, [rsp+1536]
    lea rdx, [rsp+1024]
    call bls24_Fp8_sub_asm@PLT
    lea rdi, [r12+1024]
    lea rsi, [rsp+1536]
    lea rdx, [rsp+512]
    call bls24_Fp8_add_asm@PLT

    add rsp, 3080
    pop rbp
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret
.size bls24_Fp24_mul_asm, .-bls24_Fp24_mul_asm

/* Prevent executable stack */
.section .note.GNU-stack, "", @progbits
