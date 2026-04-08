/* Benchmark: wNAF GLV vs Binary GLV cost estimation
 *
 * Measures Fp multiply/add time on BLS12-381 and estimates GLV
 * scalar multiplication time for both approaches:
 *
 * Binary GLV (existing, BLS12_GLV_ScalarMultBedrock.v):
 *   128 iterations, each: 1 doubling + 2 conditional additions
 *   Doubling: ~5M+5S ≈ 10 Fp mul equiv
 *   Addition (complete, ladderstep): ~12M+2S ≈ 14 Fp mul equiv
 *   Avg per iter: 10 + 2 * 0.5 * 14 = 24 Fp mul equiv
 *   Total: 128 * 24 = 3072 Fp mul equiv
 *
 * wNAF GLV (new, BLS12_wNAF_GLV chain, w=4):
 *   129 iterations, each: 1 doubling + 2 conditional additions
 *   Non-zero digit probability: 1/(w+1) = 1/5 = 0.2
 *   Avg per iter: 10 + 2 * 0.2 * 14 = 15.6 Fp mul equiv
 *   Total: 129 * 15.6 = 2012 Fp mul equiv
 *   Speedup: 3072/2012 = 1.53x (~35% faster)
 *
 *   (However, wNAF requires precomputation of 4 table entries per
 *    base point: 1 double + 3 additions = ~52 Fp mul equiv each.
 *    Total precomp: 2 * 52 = 104 Fp mul equiv.
 *    Adjusted total: 2012 + 104 = 2116 Fp mul equiv.
 *    Adjusted speedup: 3072/2116 = 1.45x (~31% faster))
 */
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

typedef uintptr_t br_word_t;

/* Include fiat-crypto BLS12-381 C code */
#include "bls12_pairing.c"

static inline double now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

#define WARMUP 1000
#define ITERS 100000

int main(void) {
    /* Measure Fp multiply time */
    uint8_t a[48] = {1}, b[48] = {2}, c[48] = {0};
    double t0, t1;
    int i;

    /* Warmup */
    for (i = 0; i < WARMUP; i++) {
        bls12_mul((br_word_t)c, (br_word_t)a, (br_word_t)b);
    }

    /* Measure Fp mul */
    t0 = now_ns();
    for (i = 0; i < ITERS; i++) {
        bls12_mul((br_word_t)c, (br_word_t)a, (br_word_t)b);
    }
    t1 = now_ns();
    double fp_mul_ns = (t1 - t0) / ITERS;

    /* Measure Fp add */
    for (i = 0; i < WARMUP; i++) {
        bls12_add((br_word_t)c, (br_word_t)a, (br_word_t)b);
    }
    t0 = now_ns();
    for (i = 0; i < ITERS; i++) {
        bls12_add((br_word_t)c, (br_word_t)a, (br_word_t)b);
    }
    t1 = now_ns();
    double fp_add_ns = (t1 - t0) / ITERS;

    /* Measure Fp square (same cost as mul for Montgomery) */
    for (i = 0; i < WARMUP; i++) {
        bls12_square((br_word_t)c, (br_word_t)a);
    }
    t0 = now_ns();
    for (i = 0; i < ITERS; i++) {
        bls12_square((br_word_t)c, (br_word_t)a);
    }
    t1 = now_ns();
    double fp_sqr_ns = (t1 - t0) / ITERS;

    printf("=== BLS12-381 Fp operation timing ===\n");
    printf("Fp mul:    %.1f ns\n", fp_mul_ns);
    printf("Fp sqr:    %.1f ns\n", fp_sqr_ns);
    printf("Fp add:    %.1f ns\n", fp_add_ns);
    printf("mul/add ratio: %.1fx\n\n", fp_mul_ns / fp_add_ns);

    /* Cost model for complete addition (RCB formula, CurveAdd.v):
     * 12M + 2S + 23add/sub
     * We weight S = 0.8M (typical for Montgomery), add = 0.1M */
    double add_cost = 12 * fp_mul_ns + 2 * fp_sqr_ns + 23 * fp_add_ns;

    /* Cost model for doubling (PointDouble.v, dbl-2009-l):
     * 1M + 5S + 8add
     * But with extra three_b mul: 2M + 5S + 8add */
    double dbl_cost = 2 * fp_mul_ns + 5 * fp_sqr_ns + 8 * fp_add_ns;

    printf("=== Estimated curve operation costs ===\n");
    printf("Point addition:  %.0f ns (12M + 2S + 23add)\n", add_cost);
    printf("Point doubling:  %.0f ns (2M + 5S + 8add)\n\n", dbl_cost);

    /* Binary GLV: 128 iters x (1 dbl + 2 * 0.5 cond_add) */
    double binary_glv = 128 * (dbl_cost + 2 * 0.5 * add_cost);
    printf("=== GLV Scalar Multiplication Estimates ===\n");
    printf("Binary GLV (128 iters, p_add=0.5):\n");
    printf("  %.0f ns (%.2f ms)\n\n", binary_glv, binary_glv / 1e6);

    /* wNAF GLV w=4: 129 iters x (1 dbl + 2 * 0.2 cond_add) + precomp */
    double wnaf_precomp = 2 * (dbl_cost + 3 * add_cost);  /* 2 tables of 4 entries */
    double wnaf_loop = 129 * (dbl_cost + 2 * 0.2 * add_cost);
    double wnaf_glv = wnaf_precomp + wnaf_loop;
    printf("wNAF GLV w=4 (129 iters, p_add=0.2, +precomp):\n");
    printf("  precomp: %.0f ns\n", wnaf_precomp);
    printf("  loop:    %.0f ns\n", wnaf_loop);
    printf("  total:   %.0f ns (%.2f ms)\n\n", wnaf_glv, wnaf_glv / 1e6);

    double speedup = binary_glv / wnaf_glv;
    double savings_pct = (1.0 - 1.0/speedup) * 100.0;
    printf("=== Comparison ===\n");
    printf("Speedup:  %.2fx\n", speedup);
    printf("Savings:  %.0f%%\n", savings_pct);
    printf("\nNote: These are operation-count estimates. Actual timings will\n");
    printf("differ due to branch prediction, memory effects, and the cost\n");
    printf("of table lookups + conditional negation in the wNAF variant.\n");

    return 0;
}
