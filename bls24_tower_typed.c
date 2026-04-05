/* BLS24-509 full tower with typed restrict pointers.
   Fp2, Fp4, Fp8, Fp24 operations using struct types.
   Compiled separately from Fp base ops for optimal register allocation.

   NOT formally verified — performance experiment. */

#include <stdint.h>
#include <string.h>

typedef uintptr_t br_word_t;

/* ====================================================================
   Type definitions
   ==================================================================== */
typedef struct { uint64_t v[8]; } Fp;       /* 64 bytes */
typedef struct { Fp c0; Fp c1; } Fp2;       /* 128 bytes */
typedef struct { Fp2 c0; Fp2 c1; } Fp4;     /* 256 bytes */
typedef struct { Fp4 c0; Fp4 c1; } Fp8;     /* 512 bytes */
typedef struct { Fp8 c0; Fp8 c1; Fp8 c2; } Fp24; /* 1536 bytes */

/* ====================================================================
   Extern Fp base ops (from bedrock2 extracted code)
   ==================================================================== */
extern void bls24_509_add(br_word_t, br_word_t, br_word_t);
extern void bls24_509_sub(br_word_t, br_word_t, br_word_t);
extern void bls24_509_mul(br_word_t, br_word_t, br_word_t);
extern void bls24_509_square(br_word_t, br_word_t);
extern void bls24_509_opp(br_word_t, br_word_t);

#define FP(x) ((br_word_t)(x))

/* ====================================================================
   Fp2 = Fp[u]/(u²+1), beta = -1
   ==================================================================== */
void typed_Fp2_add(Fp2 *restrict out, const Fp2 *restrict x, const Fp2 *restrict y) {
    bls24_509_add(FP(&out->c0), FP(&x->c0), FP(&y->c0));
    bls24_509_add(FP(&out->c1), FP(&x->c1), FP(&y->c1));
}
void typed_Fp2_sub(Fp2 *restrict out, const Fp2 *restrict x, const Fp2 *restrict y) {
    bls24_509_sub(FP(&out->c0), FP(&x->c0), FP(&y->c0));
    bls24_509_sub(FP(&out->c1), FP(&x->c1), FP(&y->c1));
}
void typed_Fp2_opp(Fp2 *restrict out, const Fp2 *restrict x) {
    bls24_509_opp(FP(&out->c0), FP(&x->c0));
    bls24_509_opp(FP(&out->c1), FP(&x->c1));
}
/* mul_by_nr(beta=-1): negate first component only */
static inline void typed_Fp2_mul_by_nr(Fp *restrict out, const Fp *restrict x) {
    bls24_509_opp(FP(out), FP(x));
}
/* mul_xi(1+u): (a+bu)(1+u) = (a-b) + (a+b)u */
void typed_Fp2_mul_xi(Fp2 *restrict out, const Fp2 *restrict x) {
    Fp tmp;
    bls24_509_add(FP(&tmp), FP(&x->c0), FP(&x->c1));
    bls24_509_sub(FP(&out->c0), FP(&x->c0), FP(&x->c1));
    out->c1 = tmp;
}
/* Karatsuba mul */
void typed_Fp2_mul(Fp2 *restrict out, const Fp2 *restrict x, const Fp2 *restrict y) {
    Fp d0, d1, t;
    bls24_509_mul(FP(&d0), FP(&x->c0), FP(&y->c0));
    bls24_509_mul(FP(&d1), FP(&x->c1), FP(&y->c1));
    bls24_509_add(FP(&t), FP(&x->c0), FP(&x->c1));
    bls24_509_add(FP(&out->c1), FP(&y->c0), FP(&y->c1));
    bls24_509_mul(FP(&out->c1), FP(&out->c1), FP(&t));
    bls24_509_sub(FP(&out->c1), FP(&out->c1), FP(&d0));
    bls24_509_sub(FP(&out->c1), FP(&out->c1), FP(&d1));
    bls24_509_opp(FP(&t), FP(&d1)); /* beta*d1 = -d1 */
    bls24_509_add(FP(&out->c0), FP(&d0), FP(&t));
}
void typed_Fp2_square(Fp2 *restrict out, const Fp2 *restrict x) {
    Fp d0, d1, cross;
    bls24_509_square(FP(&d0), FP(&x->c0));
    bls24_509_square(FP(&d1), FP(&x->c1));
    bls24_509_mul(FP(&cross), FP(&x->c0), FP(&x->c1));
    bls24_509_add(FP(&out->c1), FP(&cross), FP(&cross));
    bls24_509_opp(FP(&cross), FP(&d1));
    bls24_509_add(FP(&out->c0), FP(&d0), FP(&cross));
}

/* ====================================================================
   Fp4 = Fp2[x]/(x²-xi), xi = 1+u
   ==================================================================== */
void typed_Fp4_add(Fp4 *restrict out, const Fp4 *restrict x, const Fp4 *restrict y) {
    typed_Fp2_add(&out->c0, &x->c0, &y->c0);
    typed_Fp2_add(&out->c1, &x->c1, &y->c1);
}
void typed_Fp4_sub(Fp4 *restrict out, const Fp4 *restrict x, const Fp4 *restrict y) {
    typed_Fp2_sub(&out->c0, &x->c0, &y->c0);
    typed_Fp2_sub(&out->c1, &x->c1, &y->c1);
}
void typed_Fp4_opp(Fp4 *restrict out, const Fp4 *restrict x) {
    typed_Fp2_opp(&out->c0, &x->c0);
    typed_Fp2_opp(&out->c1, &x->c1);
}
/* mul_by_v: (a+bx) * x = b*xi + a*x */
void typed_Fp4_mul_by_v(Fp4 *restrict out, const Fp4 *restrict x) {
    Fp2 tmp;
    typed_Fp2_mul_xi(&tmp, &x->c1);
    out->c1 = x->c0;
    out->c0 = tmp;
}
void typed_Fp4_mul(Fp4 *restrict out, const Fp4 *restrict x, const Fp4 *restrict y) {
    Fp2 d0, d1, t;
    typed_Fp2_mul(&d0, &x->c0, &y->c0);
    typed_Fp2_mul(&d1, &x->c1, &y->c1);
    typed_Fp2_add(&t, &x->c0, &x->c1);
    typed_Fp2_add(&out->c1, &y->c0, &y->c1);
    typed_Fp2_mul(&out->c1, &out->c1, &t);
    typed_Fp2_sub(&out->c1, &out->c1, &d0);
    typed_Fp2_sub(&out->c1, &out->c1, &d1);
    typed_Fp2_mul_xi(&t, &d1); /* nr*d1 */
    typed_Fp2_add(&out->c0, &d0, &t);
}
void typed_Fp4_square(Fp4 *restrict out, const Fp4 *restrict x) {
    Fp2 d0, d1, cross;
    typed_Fp2_square(&d0, &x->c0);
    typed_Fp2_square(&d1, &x->c1);
    typed_Fp2_mul(&cross, &x->c0, &x->c1);
    typed_Fp2_add(&out->c1, &cross, &cross);
    typed_Fp2_mul_xi(&d1, &d1);
    typed_Fp2_add(&out->c0, &d0, &d1);
}

/* ====================================================================
   Fp8 = Fp4[v]/(v²-x), nonresidue = v (the Fp4 variable)
   ==================================================================== */
void typed_Fp8_add(Fp8 *restrict out, const Fp8 *restrict x, const Fp8 *restrict y) {
    typed_Fp4_add(&out->c0, &x->c0, &y->c0);
    typed_Fp4_add(&out->c1, &x->c1, &y->c1);
}
void typed_Fp8_sub(Fp8 *restrict out, const Fp8 *restrict x, const Fp8 *restrict y) {
    typed_Fp4_sub(&out->c0, &x->c0, &y->c0);
    typed_Fp4_sub(&out->c1, &x->c1, &y->c1);
}
void typed_Fp8_opp(Fp8 *restrict out, const Fp8 *restrict x) {
    typed_Fp4_opp(&out->c0, &x->c0);
    typed_Fp4_opp(&out->c1, &x->c1);
}
void typed_Fp8_mul_by_w(Fp8 *restrict out, const Fp8 *restrict x) {
    Fp4 tmp;
    typed_Fp4_mul_by_v(&tmp, &x->c1);
    out->c1 = x->c0;
    out->c0 = tmp;
}
void typed_Fp8_mul(Fp8 *restrict out, const Fp8 *restrict x, const Fp8 *restrict y) {
    Fp4 d0, d1, t;
    typed_Fp4_mul(&d0, &x->c0, &y->c0);
    typed_Fp4_mul(&d1, &x->c1, &y->c1);
    typed_Fp4_add(&t, &x->c0, &x->c1);
    typed_Fp4_add(&out->c1, &y->c0, &y->c1);
    typed_Fp4_mul(&out->c1, &out->c1, &t);
    typed_Fp4_sub(&out->c1, &out->c1, &d0);
    typed_Fp4_sub(&out->c1, &out->c1, &d1);
    typed_Fp4_mul_by_v(&t, &d1);
    typed_Fp4_add(&out->c0, &d0, &t);
}
void typed_Fp8_square(Fp8 *restrict out, const Fp8 *restrict x) {
    Fp4 d0, d1, cross;
    typed_Fp4_square(&d0, &x->c0);
    typed_Fp4_square(&d1, &x->c1);
    typed_Fp4_mul(&cross, &x->c0, &x->c1);
    typed_Fp4_add(&out->c1, &cross, &cross);
    typed_Fp4_mul_by_v(&d1, &d1);
    typed_Fp4_add(&out->c0, &d0, &d1);
}

/* ====================================================================
   Fp24 = Fp8[w]/(w³-v), cubic extension (Karatsuba)
   ==================================================================== */
void typed_Fp24_add(Fp24 *restrict out, const Fp24 *restrict x, const Fp24 *restrict y) {
    typed_Fp8_add(&out->c0, &x->c0, &y->c0);
    typed_Fp8_add(&out->c1, &x->c1, &y->c1);
    typed_Fp8_add(&out->c2, &x->c2, &y->c2);
}
void typed_Fp24_sub(Fp24 *restrict out, const Fp24 *restrict x, const Fp24 *restrict y) {
    typed_Fp8_sub(&out->c0, &x->c0, &y->c0);
    typed_Fp8_sub(&out->c1, &x->c1, &y->c1);
    typed_Fp8_sub(&out->c2, &x->c2, &y->c2);
}
void typed_Fp24_opp(Fp24 *restrict out, const Fp24 *restrict x) {
    typed_Fp8_opp(&out->c0, &x->c0);
    typed_Fp8_opp(&out->c1, &x->c1);
    typed_Fp8_opp(&out->c2, &x->c2);
}
void typed_Fp24_conjugate(Fp24 *restrict out, const Fp24 *restrict x) {
    if (out != x) { out->c0 = x->c0; out->c2 = x->c2; }
    typed_Fp8_opp(&out->c1, &x->c1);
}
/* Cubic Karatsuba: (a0+a1w+a2w²)(b0+b1w+b2w²) */
void typed_Fp24_mul(Fp24 *restrict out, const Fp24 *restrict x, const Fp24 *restrict y) {
    Fp8 a0b0, a1b1, a2b2, t0, t1, t2;
    typed_Fp8_mul(&a0b0, &x->c0, &y->c0);
    typed_Fp8_mul(&a1b1, &x->c1, &y->c1);
    typed_Fp8_mul(&a2b2, &x->c2, &y->c2);
    /* c0 = a0b0 + w*((a1+a2)(b1+b2) - a1b1 - a2b2) */
    typed_Fp8_add(&t0, &x->c1, &x->c2);
    typed_Fp8_add(&t1, &y->c1, &y->c2);
    typed_Fp8_mul(&t0, &t0, &t1);
    typed_Fp8_sub(&t0, &t0, &a1b1);
    typed_Fp8_sub(&t0, &t0, &a2b2);
    typed_Fp8_mul_by_w(&t0, &t0);
    typed_Fp8_add(&out->c0, &a0b0, &t0);
    /* c1 = (a0+a1)(b0+b1) - a0b0 - a1b1 + w*a2b2 */
    typed_Fp8_add(&t0, &x->c0, &x->c1);
    typed_Fp8_add(&t1, &y->c0, &y->c1);
    typed_Fp8_mul(&t0, &t0, &t1);
    typed_Fp8_sub(&t0, &t0, &a0b0);
    typed_Fp8_sub(&t0, &t0, &a1b1);
    typed_Fp8_mul_by_w(&t1, &a2b2);
    typed_Fp8_add(&out->c1, &t0, &t1);
    /* c2 = (a0+a2)(b0+b2) - a0b0 - a2b2 + a1b1 */
    typed_Fp8_add(&t0, &x->c0, &x->c2);
    typed_Fp8_add(&t1, &y->c0, &y->c2);
    typed_Fp8_mul(&t0, &t0, &t1);
    typed_Fp8_sub(&t0, &t0, &a0b0);
    typed_Fp8_sub(&t0, &t0, &a2b2);
    typed_Fp8_add(&out->c2, &t0, &a1b1);
}
/* Fp24 squaring (Chung-Hasan SQR2) */
void typed_Fp24_square(Fp24 *restrict out, const Fp24 *restrict x) {
    Fp8 s0, s1, s2, s3, s4;
    typed_Fp8_square(&s0, &x->c0);
    typed_Fp8_mul(&s1, &x->c0, &x->c1);
    typed_Fp8_add(&s1, &s1, &s1);
    typed_Fp8_sub(&s2, &x->c0, &x->c1);
    typed_Fp8_add(&s2, &s2, &x->c2);
    typed_Fp8_square(&s2, &s2);
    typed_Fp8_mul(&s3, &x->c1, &x->c2);
    typed_Fp8_add(&s3, &s3, &s3);
    typed_Fp8_square(&s4, &x->c2);
    typed_Fp8_mul_by_w(&out->c0, &s3);
    typed_Fp8_add(&out->c0, &s0, &out->c0);
    typed_Fp8_mul_by_w(&out->c1, &s4);
    typed_Fp8_add(&out->c1, &s1, &out->c1);
    typed_Fp8_add(&out->c2, &s1, &s2);
    typed_Fp8_add(&out->c2, &out->c2, &s3);
    typed_Fp8_sub(&out->c2, &out->c2, &s0);
    typed_Fp8_sub(&out->c2, &out->c2, &s4);
}
