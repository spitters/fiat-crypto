/* Benchmark: BLS12-377 GLV scalar multiplication cost estimate
 *
 * Measures Fp multiply time and estimates GLV scalar mult time
 * from the operation count:
 *   - 128 iterations (GLV halves the scalar)
 *   - Each iteration: 1 doubling + ~1 conditional addition
 *   - Doubling: 4M + 4S + misc  ≈ 8 Fp mul equiv
 *   - Addition (complete, ladderstep): ~16M
 *   - Average per iter: ~16 Fp mul equiv (50% conditional add)
 *   - Total: ~128 × 16 = 2048 Fp mul + overhead
 */
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <string.h>
#include <stdlib.h>

typedef uintptr_t br_word_t;

/* Include the fiat-crypto BLS12-377 C code */
#include "bls377_pairing.c"

static inline double now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

#define FELEM_BYTES 48  /* 377-bit prime → 6 × 64-bit words = 48 bytes */

/* Complete Jacobian addition for y² = x³ + b (short Weierstrass)
 * Using the ladderstep formula from CurveAdd.v
 * Inputs/outputs: projective Jacobian (X:Y:Z) with Z=0 for identity
 */
static void point_add(uint8_t *out, const uint8_t *p1, const uint8_t *p2) {
    /* This is a simplified version — the actual bedrock2 code uses
       the complete addition formula from ladderstep_body. For benchmarking,
       we count Fp multiplications. */
    uint8_t t0[48], t1[48], t2[48], t3[48], t4[48], t5[48];
    uint8_t t6[48], t7[48], t8[48], t9[48], t10[48], t11[48];
    br_word_t X1 = (br_word_t)p1, Y1 = (br_word_t)(p1+48), Z1 = (br_word_t)(p1+96);
    br_word_t X2 = (br_word_t)p2, Y2 = (br_word_t)(p2+48), Z2 = (br_word_t)(p2+96);
    br_word_t Xo = (br_word_t)out, Yo = (br_word_t)(out+48), Zo = (br_word_t)(out+96);

    /* Complete addition: ~12M + 2S + 6add/sub
       Using the Renes-Costello-Batina complete formula for a=0 */
    bls377_mul((br_word_t)t0, X1, X2);  /* 1 */
    bls377_mul((br_word_t)t1, Y1, Y2);  /* 2 */
    bls377_mul((br_word_t)t2, Z1, Z2);  /* 3 */

    bls377_add((br_word_t)t3, X1, Y1);
    bls377_add((br_word_t)t4, X2, Y2);
    bls377_mul((br_word_t)t3, (br_word_t)t3, (br_word_t)t4);  /* 4 */
    bls377_add((br_word_t)t4, (br_word_t)t0, (br_word_t)t1);
    bls377_sub((br_word_t)t3, (br_word_t)t3, (br_word_t)t4);

    bls377_add((br_word_t)t4, X1, Z1);
    bls377_add((br_word_t)t5, X2, Z2);
    bls377_mul((br_word_t)t4, (br_word_t)t4, (br_word_t)t5);  /* 5 */
    bls377_add((br_word_t)t5, (br_word_t)t0, (br_word_t)t2);
    bls377_sub((br_word_t)t4, (br_word_t)t4, (br_word_t)t5);

    bls377_add((br_word_t)t5, Y1, Z1);
    bls377_add((br_word_t)t6, Y2, Z2);
    bls377_mul((br_word_t)t5, (br_word_t)t5, (br_word_t)t6);  /* 6 */
    bls377_add((br_word_t)t6, (br_word_t)t1, (br_word_t)t2);
    bls377_sub((br_word_t)t5, (br_word_t)t5, (br_word_t)t6);

    /* 3b = 3 for BLS12-377 (b=1) */
    bls377_add((br_word_t)t6, (br_word_t)t2, (br_word_t)t2);
    bls377_add((br_word_t)t6, (br_word_t)t6, (br_word_t)t2);  /* t6 = 3*t2 = 3b*Z1*Z2 */

    bls377_sub((br_word_t)t7, (br_word_t)t1, (br_word_t)t6);
    bls377_add((br_word_t)t8, (br_word_t)t1, (br_word_t)t6);

    bls377_mul((br_word_t)t9, (br_word_t)t3, (br_word_t)t7);  /* 7: partial X3 */

    bls377_mul((br_word_t)t10, (br_word_t)t4, (br_word_t)t8);  /* 8 */
    bls377_sub(Xo, (br_word_t)t9, (br_word_t)t10);  /* X3 (not quite - simplified) */

    /* More multiplications for Y3, Z3... */
    bls377_mul((br_word_t)t9, (br_word_t)t7, (br_word_t)t8);  /* 9 */
    bls377_mul((br_word_t)t10, (br_word_t)t0, (br_word_t)t0); /* 10: sqr */
    bls377_add((br_word_t)t10, (br_word_t)t10, (br_word_t)t10);
    bls377_add((br_word_t)t10, (br_word_t)t10, (br_word_t)t0);
    bls377_mul((br_word_t)t11, (br_word_t)t10, (br_word_t)t6); /* 11 */
    bls377_add(Yo, (br_word_t)t9, (br_word_t)t11);

    bls377_mul((br_word_t)t9, (br_word_t)t5, (br_word_t)t7);  /* 12 */
    bls377_mul((br_word_t)t10, (br_word_t)t4, (br_word_t)t5); /* 13 */
    bls377_sub(Zo, (br_word_t)t10, (br_word_t)t9);
}

int main(void) {
    /* Test vectors: random-looking Fp elements */
    uint64_t a[6] = {0x123456789abcdef0ULL, 0x23456789abcdef01ULL,
                     0x3456789abcdef012ULL, 0x456789abcdef0123ULL,
                     0x56789abcdef01234ULL, 0x06789abcdef01235ULL};
    uint64_t b[6] = {0xfedcba9876543210ULL, 0xedcba98765432100ULL,
                     0xdcba987654321001ULL, 0xcba9876543210012ULL,
                     0xba98765432100123ULL, 0x0a98765432100124ULL};
    uint64_t c[6];

    int iters;
    double start, end;

    /* Warm up */
    for (int i = 0; i < 1000; i++)
        bls377_mul((br_word_t)c, (br_word_t)a, (br_word_t)b);

    /* Benchmark Fp multiply */
    iters = 100000;
    start = now_ns();
    for (int i = 0; i < iters; i++)
        bls377_mul((br_word_t)c, (br_word_t)a, (br_word_t)b);
    end = now_ns();
    double fp_mul_ns = (end - start) / iters;
    printf("Fp multiply:                  %8.1f ns\n", fp_mul_ns);

    /* Benchmark Fp add */
    iters = 1000000;
    start = now_ns();
    for (int i = 0; i < iters; i++)
        bls377_add((br_word_t)c, (br_word_t)a, (br_word_t)b);
    end = now_ns();
    double fp_add_ns = (end - start) / iters;
    printf("Fp add:                       %8.1f ns\n", fp_add_ns);

    /* Benchmark Fp square (= mul for fiat-crypto) */
    iters = 100000;
    start = now_ns();
    for (int i = 0; i < iters; i++)
        bls377_mul((br_word_t)c, (br_word_t)a, (br_word_t)a);
    end = now_ns();
    double fp_sqr_ns = (end - start) / iters;
    printf("Fp square:                    %8.1f ns\n", fp_sqr_ns);

    /* Benchmark point_add (13 mul + several add/sub) */
    uint8_t P1[144], P2[144], P3[144];
    memset(P1, 0x42, 144);
    memset(P2, 0x37, 144);
    iters = 10000;
    start = now_ns();
    for (int i = 0; i < iters; i++)
        point_add(P3, P1, P2);
    end = now_ns();
    double point_add_ns = (end - start) / iters;
    printf("Point add (13M + add/sub):    %8.1f ns\n", point_add_ns);

    /* Estimate GLV scalar mult time */
    printf("\n--- GLV Scalar Multiplication Estimate ---\n");
    printf("Iterations: 128 (BLS12-377 GLV)\n");

    /* Operation counts from the ladderstep complete addition formula:
     * Doubling (a=0): 1M + 5S + 1*3b + 7add ≈ 6M + 8add
     * Addition (a=0): 12M + 2S + 6add ≈ 14M + 6add
     * Per iteration (avg): doubling + 0.5 * addition = 6+7 = 13M
     */
    double est_doubling = 6 * fp_mul_ns + 8 * fp_add_ns;
    double est_addition = 14 * fp_mul_ns + 6 * fp_add_ns;
    double est_per_iter = est_doubling + 0.5 * est_addition;
    double est_total_us = 128 * est_per_iter / 1000.0;

    printf("Est. doubling:                %8.1f ns  (6M + 8add)\n", est_doubling);
    printf("Est. addition:                %8.1f ns  (14M + 6add)\n", est_addition);
    printf("Est. per iteration (avg):     %8.1f ns\n", est_per_iter);
    printf("Est. GLV scalar mult:         %8.1f us  (128 iterations)\n", est_total_us);
    printf("Est. naive scalar mult:       %8.1f us  (253 iterations)\n",
           253 * est_per_iter / 1000.0);
    printf("GLV speedup:                  %8.2fx\n", 253.0 / 128.0);

    printf("\n--- Comparison ---\n");
    printf("arkworks (est.):              ~800-1000 us  (Rust, generic)\n");
    printf("gnark-crypto (est.):          ~500-600 us   (Go+asm)\n");
    printf("blst (est.):                  ~340-380 us   (C/asm, BLS12-381 only)\n");

    return 0;
}
