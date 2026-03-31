/*
 * bench_bls377.c -- Benchmark harness for verified BLS12-377 pairing
 *
 * Build:  make
 * Run:    ./bench_bls377
 *
 * This benchmarks the full tower (Fp -> Fp2 -> Fp6 -> Fp12) and the
 * pairing (Miller loop + final exponentiation) using small test values.
 * The test values are NOT on the curve; this measures throughput only.
 */

#define _POSIX_C_SOURCE 199309L   /* clock_gettime */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

#include "bls377_pairing.h"

/*
 * Compilation strategy: all functions in the extraction are static,
 * so we include them all in this translation unit.
 *
 * bls377_stubs.c comes first: it forward-declares the Fp primitives
 * (add, sub, mul, square) and defines the Fp2 bridge functions that
 * the extraction code calls. bls377_pairing.c then provides the Fp
 * implementations and all higher-tower / pairing code.
 */
#include "bls377_stubs.c"
#include "bls377_pairing.c"

/* Timing helper */
static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

/* Field element sizes */
#define FP_BYTES   BLS377_FP_BYTES
#define FP2_BYTES  BLS377_FP2_BYTES
#define FP6_BYTES  BLS377_FP6_BYTES
#define FP12_BYTES BLS377_FP12_BYTES

/* Simple aligned allocation */
static void *alloc_felem(size_t bytes) {
    void *p = aligned_alloc(64, ((bytes + 63) / 64) * 64);
    memset(p, 0, bytes);
    return p;
}

/* Set a field element to a small value (for testing) */
static void set_small(uintptr_t p, uint64_t val) {
    uint64_t *words = (uint64_t *)p;
    words[0] = val;
    for (int i = 1; i < 6; i++) words[i] = 0;
}

#define BENCH(name, call, iters) do { \
    /* warmup */ \
    for (int _w = 0; _w < 100; _w++) { call; } \
    double _start = get_time_ns(); \
    for (int _i = 0; _i < (iters); _i++) { call; } \
    double _elapsed = get_time_ns() - _start; \
    printf("%-35s %10.1f ns/op  (%d iters)\n", name, _elapsed / (iters), (iters)); \
} while(0)

#define BENCH_US(name, call, iters) do { \
    /* warmup */ \
    for (int _w = 0; _w < 10; _w++) { call; } \
    double _start = get_time_ns(); \
    for (int _i = 0; _i < (iters); _i++) { call; } \
    double _elapsed = get_time_ns() - _start; \
    printf("%-35s %10.1f us/op  (%d iters)\n", name, _elapsed / (iters) / 1000.0, (iters)); \
} while(0)

int main(void) {
    /* Fp elements */
    uintptr_t a = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t b = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t c = (uintptr_t)alloc_felem(FP_BYTES);

    /* Fp2 elements */
    uintptr_t a2 = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t b2 = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t c2 = (uintptr_t)alloc_felem(FP2_BYTES);

    /* Fp6 elements */
    uintptr_t a6 = (uintptr_t)alloc_felem(FP6_BYTES);
    uintptr_t b6 = (uintptr_t)alloc_felem(FP6_BYTES);
    uintptr_t c6 = (uintptr_t)alloc_felem(FP6_BYTES);

    /* Fp12 elements */
    uintptr_t a12 = (uintptr_t)alloc_felem(FP12_BYTES);
    uintptr_t b12 = (uintptr_t)alloc_felem(FP12_BYTES);
    uintptr_t c12 = (uintptr_t)alloc_felem(FP12_BYTES);

    /* Pairing inputs: P = (p_x, p_y) on G1, Q = (q_x, q_y) on G2 */
    uintptr_t p_x  = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t p_y  = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t q_x  = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t q_y  = (uintptr_t)alloc_felem(FP2_BYTES);

    /* Frobenius constants */
    uintptr_t g1p2  = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t g2p2  = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t wfp2  = (uintptr_t)alloc_felem(FP2_BYTES);

    /* Initialize Fp elements with non-zero values */
    set_small(a, 7);
    set_small(b, 13);

    /* Initialize Fp2 elements */
    set_small(a2, 7);
    set_small(a2 + FP_BYTES, 3);
    set_small(b2, 13);
    set_small(b2 + FP_BYTES, 5);

    /* Initialize Fp6/Fp12 from Fp2 */
    memcpy((void*)a6, (void*)a2, FP2_BYTES);
    memcpy((void*)(a6 + FP2_BYTES), (void*)b2, FP2_BYTES);
    set_small(a6 + 2*FP2_BYTES, 11);
    set_small(a6 + 2*FP2_BYTES + FP_BYTES, 2);
    memcpy((void*)b6, (void*)b2, FP2_BYTES);
    set_small(b6 + FP2_BYTES, 17);
    set_small(b6 + 2*FP2_BYTES, 19);
    memcpy((void*)a12, (void*)a6, FP6_BYTES);
    memcpy((void*)(a12 + FP6_BYTES), (void*)b6, FP6_BYTES);
    memcpy((void*)b12, (void*)a12, FP12_BYTES);

    /* Initialize pairing inputs (small test values) */
    set_small(p_x, 1);
    set_small(p_y, 2);
    set_small(q_x, 3);
    set_small(q_x + FP_BYTES, 4);
    set_small(q_y, 5);
    set_small(q_y + FP_BYTES, 6);

    /* Load Frobenius constants */
    bls377_load_gamma1_p2(g1p2);
    bls377_load_gamma2_p2(g2p2);
    bls377_load_w_frob_p2_c1(wfp2);

    printf("=== BLS12-377 fiat-crypto/bedrock2 benchmarks ===\n");
    printf("    (verified C from Rocq extraction)\n\n");

    /* --- Fp operations --- */
    printf("--- Fp (384-bit prime field) ---\n");
    BENCH("Fp add",       bls377_add(c, a, b),    1000000);
    BENCH("Fp sub",       bls377_sub(c, a, b),    1000000);
    BENCH("Fp mul",       bls377_mul(c, a, b),    1000000);
    BENCH("Fp square",    bls377_square(c, a),    1000000);
    printf("\n");

    /* --- Fp2 operations --- */
    printf("--- Fp2 (quadratic extension, beta=-5) ---\n");
    BENCH("Fp2 add",      bls377_Fp2_add(c2, a2, b2),   1000000);
    BENCH("Fp2 sub",      bls377_Fp2_sub(c2, a2, b2),   1000000);
    BENCH("Fp2 mul",      bls377_Fp2_mul(c2, a2, b2),   500000);
    BENCH("Fp2 square",   bls377_Fp2_square(c2, a2),    500000);
    BENCH("Fp2 inv",      bls377_Fp2_inv(c2, a2),       10000);
    BENCH("Fp2 mul_xi",   bls377_Fp2_mul_xi(c2, a2),    1000000);
    BENCH("Fp2 conjugate", bls377_Fp2_conjugate(c2, a2), 1000000);
    printf("\n");

    /* --- Fp6 operations --- */
    printf("--- Fp6 (cubic extension over Fp2) ---\n");
    BENCH("Fp6 add",      bls377_Fp6_add(c6, a6, b6),   500000);
    BENCH("Fp6 sub",      bls377_Fp6_sub(c6, a6, b6),   500000);
    BENCH("Fp6 mul",      bls377_Fp6_mul(c6, a6, b6),   100000);
    BENCH("Fp6 square",   bls377_Fp6_square(c6, a6),    100000);
    BENCH("Fp6 inv",      bls377_Fp6_inv(c6, a6),       10000);
    BENCH("Fp6 mul_fp2",  bls377_Fp6_mul_fp2(c6, a6, a2), 200000);
    printf("\n");

    /* --- Fp12 operations --- */
    printf("--- Fp12 (quadratic extension over Fp6) ---\n");
    BENCH("Fp12 add",     bls377_Fp12_add(c12, a12, b12),  200000);
    BENCH("Fp12 sub",     bls377_Fp12_sub(c12, a12, b12),  200000);
    BENCH("Fp12 mul",     bls377_Fp12_mul(c12, a12, b12),  50000);
    BENCH("Fp12 square",  bls377_Fp12_square(c12, a12),    50000);
    BENCH("Fp12 inv",     bls377_Fp12_inv(c12, a12),       5000);
    BENCH("Fp12 conjugate", bls377_Fp12_conjugate(c12, a12), 500000);
    printf("\n");

    /* --- Frobenius operations --- */
    printf("--- Frobenius endomorphisms ---\n");
    BENCH("Fp6 frobenius_p2",  bls377_Fp6_frobenius_p2(c6, a6, g1p2, g2p2), 100000);
    BENCH("Fp12 frobenius_p2", bls377_Fp12_frobenius_p2(c12, a12, g1p2, g2p2, wfp2), 50000);
    printf("\n");

    /* --- Pairing operations (the main event) --- */
    printf("--- Pairing: naive (h3 binary exp) ---\n");
    BENCH_US("Miller loop",           bls377_miller_loop(c12, p_x, p_y, q_x, q_y), 1000);
    BENCH_US("Final exp (naive)",     bls377_final_exp(c12, a12, g1p2, g2p2, wfp2), 1000);
    BENCH_US("Full pairing (naive)",  bls377_pairing(c12, p_x, p_y, q_x, q_y), 1000);
    printf("\n");

    printf("--- Pairing: DSD optimized ---\n");
    BENCH_US("Fp12 pow_u",            bls377_Fp12_pow_u(c12, a12), 10000);
    BENCH_US("Final exp (DSD)",       bls377_final_exp_dsd(c12, a12, g1p2, g2p2, wfp2), 1000);
    BENCH_US("Full pairing (DSD)",    bls377_pairing_dsd(c12, p_x, p_y, q_x, q_y), 1000);
    printf("\n");

    /* --- Summary for comparison --- */
    printf("=== Comparison targets (unverified, from eccbench) ===\n");
    printf("  gnark-crypto (Go):    0.92 ms full pairing\n");
    printf("  kilic (Go):           0.99 ms full pairing\n");
    printf("  Constantine (Nim):    1.12 ms full pairing\n");
    printf("  arkworks (Rust):      1.58 ms full pairing\n");
    printf("  libff (C++):          3.80 ms full pairing\n");
    printf("\n");

    /* Cleanup */
    free((void*)a); free((void*)b); free((void*)c);
    free((void*)a2); free((void*)b2); free((void*)c2);
    free((void*)a6); free((void*)b6); free((void*)c6);
    free((void*)a12); free((void*)b12); free((void*)c12);
    free((void*)p_x); free((void*)p_y);
    free((void*)q_x); free((void*)q_y);
    free((void*)g1p2); free((void*)g2p2); free((void*)wfp2);
    return 0;
}
