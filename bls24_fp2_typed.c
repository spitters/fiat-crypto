/* BLS24-509 Fp2 operations with typed restrict pointers.
   Drop-in replacement for bedrock2-generated Fp2 functions.

   Uses struct types so GCC can do alias analysis.
   Fp base ops remain as uintptr_t (extern, from extracted code). */

#include <stdint.h>
#include <string.h>

typedef uintptr_t br_word_t;

/* Fp element = 8 x uint64_t = 64 bytes */
typedef struct { uint64_t v[8]; } Fp;

/* Fp2 element = 2 Fp = 128 bytes */
typedef struct { Fp c0; Fp c1; } Fp2;

/* Extern Fp base ops (from bedrock2 extracted code, uintptr_t calling convention) */
extern void bls24_509_add(br_word_t out, br_word_t in0, br_word_t in1);
extern void bls24_509_sub(br_word_t out, br_word_t in0, br_word_t in1);
extern void bls24_509_mul(br_word_t out, br_word_t in0, br_word_t in1);
extern void bls24_509_square(br_word_t out, br_word_t in0);
extern void bls24_509_opp(br_word_t out, br_word_t in0);

/* Convenience: call Fp op with Fp* args */
#define FP_ADD(o,a,b)  bls24_509_add((br_word_t)(o),(br_word_t)(a),(br_word_t)(b))
#define FP_SUB(o,a,b)  bls24_509_sub((br_word_t)(o),(br_word_t)(a),(br_word_t)(b))
#define FP_MUL(o,a,b)  bls24_509_mul((br_word_t)(o),(br_word_t)(a),(br_word_t)(b))
#define FP_SQR(o,a)    bls24_509_square((br_word_t)(o),(br_word_t)(a))
#define FP_OPP(o,a)    bls24_509_opp((br_word_t)(o),(br_word_t)(a))

/* ======================================================================
   Fp2 = Fp[u]/(u^2 + 1),  beta = -1
   Element (c0, c1) represents c0 + c1*u
   ====================================================================== */

void typed_Fp2_add(Fp2 *restrict out, const Fp2 *restrict x, const Fp2 *restrict y) {
    FP_ADD(&out->c0, &x->c0, &y->c0);
    FP_ADD(&out->c1, &x->c1, &y->c1);
}

void typed_Fp2_sub(Fp2 *restrict out, const Fp2 *restrict x, const Fp2 *restrict y) {
    FP_SUB(&out->c0, &x->c0, &y->c0);
    FP_SUB(&out->c1, &x->c1, &y->c1);
}

void typed_Fp2_opp(Fp2 *restrict out, const Fp2 *restrict x) {
    FP_OPP(&out->c0, &x->c0);
    FP_OPP(&out->c1, &x->c1);
}

void typed_Fp2_felem_copy(Fp2 *restrict out, const Fp2 *restrict x) {
    *out = *x;  /* struct copy — GCC optimizes to memcpy/movs */
}

/* mul_by_nr: multiply by non-residue beta = -1.
   (c0 + c1*u) * (-1) = -c0 - c1*u.
   But bedrock2 code does: out = -x.c0 only (just the real part negation).
   Actually looking at the code: bls24_Fp2_mul_by_nr(out, x) = bls24_509_opp(out, x)
   This negates only the FIRST Fp component. This is the "multiply by beta" at Fp level. */
void typed_Fp2_mul_by_nr(Fp *restrict out, const Fp *restrict x) {
    FP_OPP(out, x);
}

/* mul_xi: multiply by xi = (1+u).
   (c0 + c1*u)(1 + u) = (c0 - c1) + (c0 + c1)*u
   since u^2 = -1. */
void typed_Fp2_mul_xi(Fp2 *restrict out, const Fp2 *restrict x) {
    Fp tmp;
    FP_ADD(&tmp, &x->c0, &x->c1);     /* tmp = c0 + c1 */
    FP_SUB(&out->c0, &x->c0, &x->c1); /* out.c0 = c0 - c1 */
    out->c1 = tmp;                      /* out.c1 = c0 + c1 */
}

/* Fp2 Karatsuba multiplication:
   (a0 + a1*u)(b0 + b1*u) = (a0*b0 - a1*b1) + (a0*b1 + a1*b0)*u
   Using Karatsuba: d0 = a0*b0, d1 = a1*b1, cross = (a0+a1)(b0+b1) - d0 - d1 */
void typed_Fp2_mul(Fp2 *restrict out, const Fp2 *restrict x, const Fp2 *restrict y) {
    Fp d0, d1, t;
    FP_MUL(&d0, &x->c0, &y->c0);      /* d0 = x0 * y0 */
    FP_MUL(&d1, &x->c1, &y->c1);      /* d1 = x1 * y1 */
    FP_ADD(&t, &x->c0, &x->c1);        /* t = x0 + x1 */
    FP_ADD(&out->c1, &y->c0, &y->c1);  /* out1 = y0 + y1 */
    FP_MUL(&out->c1, &out->c1, &t);    /* out1 = (x0+x1)(y0+y1) */
    FP_SUB(&out->c1, &out->c1, &d0);   /* out1 -= d0 */
    FP_SUB(&out->c1, &out->c1, &d1);   /* out1 -= d1 (= cross term) */
    /* out0 = d0 + beta*d1 = d0 - d1 (since beta = -1) */
    FP_OPP(&t, &d1);                    /* t = -d1 */
    FP_ADD(&out->c0, &d0, &t);          /* out0 = d0 - d1 */
}

/* Fp2 squaring: (a + b*u)^2 = (a^2 - b^2) + 2ab*u
   Karatsuba: d0 = a^2, d1 = b^2, cross = a*b */
void typed_Fp2_square(Fp2 *restrict out, const Fp2 *restrict x) {
    Fp d0, d1, cross;
    FP_SQR(&d0, &x->c0);               /* d0 = x0^2 */
    FP_SQR(&d1, &x->c1);               /* d1 = x1^2 */
    FP_MUL(&cross, &x->c0, &x->c1);    /* cross = x0 * x1 */
    FP_ADD(&out->c1, &cross, &cross);   /* out1 = 2 * x0 * x1 */
    /* out0 = d0 + beta*d1 = d0 - d1 */
    FP_OPP(&cross, &d1);                /* reuse cross = -d1 */
    FP_ADD(&out->c0, &d0, &cross);      /* out0 = d0 - d1 */
}

void typed_Fp2_zero(Fp2 *restrict out) {
    memset(out, 0, sizeof(Fp2));
}

void typed_Fp2_one(Fp2 *restrict out) {
    extern void bls24_509_one(br_word_t);
    bls24_509_one((br_word_t)&out->c0);
    memset(&out->c1, 0, sizeof(Fp));
}
