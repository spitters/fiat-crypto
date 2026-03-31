#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

/* ========== fiat-crypto extracted code ========== */
#include "bls12_pairing.c"

/* ========== blst ========== */
#include "blst.h"

/* Timing helper */
static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

/* BLS12-381 field element = 6 x 64-bit words = 48 bytes */
#define FP_BYTES 48
#define FP2_BYTES (2 * FP_BYTES)
#define FP6_BYTES (3 * FP2_BYTES)
#define FP12_BYTES (2 * FP6_BYTES)

static void *alloc_felem(size_t bytes) {
    void *p = aligned_alloc(64, bytes);
    memset(p, 0, bytes);
    return p;
}

static void set_small(uintptr_t p, uint64_t val) {
    uint64_t *words = (uint64_t *)p;
    words[0] = val;
    for (int i = 1; i < 6; i++) words[i] = 0;
}

#define BENCH(name, call, iters) do { \
    for (int _w = 0; _w < 100; _w++) { call; } \
    double _start = get_time_ns(); \
    for (int _i = 0; _i < (iters); _i++) { call; } \
    double _end = get_time_ns(); \
    printf("%-40s %8.1f ns/op  (%d iters)\n", name, (_end - _start) / (iters), iters); \
} while(0)

/* ========== BLS12-381 Generator Points ========== */

/* G1 generator (Montgomery form) */
static const uint64_t G1_x[6] = {
    0x5cb38790fd530c16ull, 0x7817fc679976fff5ull,
    0x154f95c7143ba1c1ull, 0xf0ae6acdf3d0e747ull,
    0xedce6ecc21dbf440ull, 0x120177419e0bfb75ull
};
static const uint64_t G1_y[6] = {
    0xbaac93d50ce72271ull, 0x8c22631a7918fd8eull,
    0xdd595f13570725ceull, 0x51ac582950405194ull,
    0x0e1c8c3fad0059c0ull, 0x0bbc3efc5008a26aull
};

/* G2 generator x,y (Fp2 = 2 x Fp) — affine coordinates for blst */
static const uint64_t G2_x_c0[6] = {
    0xf5f28fa202940a10ull, 0xb3f5fb2687b4961aull,
    0xa1a893b53e2ae580ull, 0x9894999d1a3caee9ull,
    0x6f67b7631863366bull, 0x058191924350bcd7ull
};
static const uint64_t G2_x_c1[6] = {
    0xa5a9c0759e23f606ull, 0xaaa0c59dbccd60c3ull,
    0x3bb17e18e2867806ull, 0x1b1ab6cc8541b367ull,
    0xc2b6ed0ef2158547ull, 0x11922a097360edf3ull
};
static const uint64_t G2_y_c0[6] = {
    0x4c730af860494c4aull, 0x597cfa1f5e369c5aull,
    0xe7e6856caa0a635aull, 0xbbefb5e96e0d495full,
    0x07d3a975f0ef25a2ull, 0x0083fd8e7e80dae5ull
};
static const uint64_t G2_y_c1[6] = {
    0xadc0fc92df64b05dull, 0x18aa270a2b1461dcull,
    0x86adac6a3be4eba0ull, 0x79495c4ec93da33aull,
    0xe7175850a43ccaedull, 0x0b2bc2a163de1bf2ull
};

int main(void) {
    printf("=== BLS12-381 Benchmark: fiat-crypto vs blst ===\n\n");

    /* ---- Fp arithmetic ---- */
    uintptr_t a = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t b = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t c = (uintptr_t)alloc_felem(FP_BYTES);
    set_small(a, 42); set_small(b, 17);

    printf("--- Fp arithmetic ---\n");
    BENCH("fiat  Fp mul",        bls12_mul(c, a, b),     1000000);
    BENCH("fiat  Fp square",     bls12_square(c, a),     1000000);
    BENCH("fiat  Fp add",        bls12_add(c, a, b),     1000000);
    BENCH("fiat  Fp sub",        bls12_sub(c, a, b),     1000000);

    /* blst Fp — uses limb_t[6] directly */
    blst_fp ba, bb, bc;
    memset(&ba, 0, sizeof(ba)); memset(&bb, 0, sizeof(bb));
    ba.l[0] = 42; bb.l[0] = 17;
    BENCH("blst  Fp mul",        blst_fp_mul(&bc, &ba, &bb), 1000000);
    BENCH("blst  Fp sqr",        blst_fp_sqr(&bc, &ba),      1000000);
    BENCH("blst  Fp add",        blst_fp_add(&bc, &ba, &bb), 1000000);
    BENCH("blst  Fp sub",        blst_fp_sub(&bc, &ba, &bb), 1000000);

    /* ---- Fp12 arithmetic ---- */
    printf("\n--- Fp12 arithmetic ---\n");
    uintptr_t f1 = (uintptr_t)alloc_felem(FP12_BYTES);
    uintptr_t f2 = (uintptr_t)alloc_felem(FP12_BYTES);
    uintptr_t f3 = (uintptr_t)alloc_felem(FP12_BYTES);
    set_small(f1, 1); set_small(f2, 2);

    BENCH("fiat  Fp12 mul",      bls12_Fp12_mul(f3, f1, f2),    100000);
    BENCH("fiat  Fp12 square",   bls12_Fp12_square(f3, f1),     100000);
    BENCH("fiat  Fp12 inv",      bls12_Fp12_inv(f3, f1),         10000);

    blst_fp12 bf1, bf2, bf3;
    memset(&bf1, 0, sizeof(bf1)); memset(&bf2, 0, sizeof(bf2));
    bf1.fp6[0].fp2[0].fp[0].l[0] = 1;
    bf2.fp6[0].fp2[0].fp[0].l[0] = 2;
    BENCH("blst  Fp12 mul",      blst_fp12_mul(&bf3, &bf1, &bf2),  100000);
    BENCH("blst  Fp12 sqr",      blst_fp12_sqr(&bf3, &bf1),        100000);
    BENCH("blst  Fp12 inverse",  blst_fp12_inverse(&bf3, &bf1),     10000);

    /* ---- Miller Loop ---- */
    printf("\n--- Miller Loop ---\n");
    uintptr_t out = (uintptr_t)alloc_felem(FP12_BYTES);
    uintptr_t px = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t py = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t qx = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t qy = (uintptr_t)alloc_felem(FP2_BYTES);
    memcpy((void*)px, G1_x, FP_BYTES);
    memcpy((void*)py, G1_y, FP_BYTES);
    /* Q is G2 in projective Fp2 coordinates */
    memcpy((void*)qx, G2_x_c0, FP_BYTES);
    memcpy((void*)(qx + FP_BYTES), G2_x_c1, FP_BYTES);
    memcpy((void*)qy, G2_y_c0, FP_BYTES);
    memcpy((void*)(qy + FP_BYTES), G2_y_c1, FP_BYTES);

    BENCH("fiat  miller_loop",   bls12_miller_loop(out, px, py, qx, qy), 1000);

    blst_fp12 bout;
    blst_p1_affine bp1;
    blst_p2_affine bp2;
    memcpy(&bp1.x, G1_x, sizeof(bp1.x));
    memcpy(&bp1.y, G1_y, sizeof(bp1.y));
    memcpy(&bp2.x.fp[0], G2_x_c0, FP_BYTES);
    memcpy(&bp2.x.fp[1], G2_x_c1, FP_BYTES);
    memcpy(&bp2.y.fp[0], G2_y_c0, FP_BYTES);
    memcpy(&bp2.y.fp[1], G2_y_c1, FP_BYTES);
    BENCH("blst  miller_loop",   blst_miller_loop(&bout, &bp2, &bp1), 1000);

    /* ---- Final Exponentiation ---- */
    printf("\n--- Final Exponentiation ---\n");
    /* Use miller loop output as input */
    bls12_miller_loop(out, px, py, qx, qy);
    uintptr_t g1p2 = (uintptr_t)alloc_felem(FP6_BYTES);
    uintptr_t g2p2 = (uintptr_t)alloc_felem(FP6_BYTES);
    uintptr_t wfp2c1 = (uintptr_t)alloc_felem(FP2_BYTES);
    /* Note: Frobenius constants need to be loaded; using zeros gives wrong result but valid timing */
    BENCH("fiat  final_exp",     bls12_final_exp(out, out, g1p2, g2p2, wfp2c1), 100);

    blst_miller_loop(&bout, &bp2, &bp1);
    BENCH("blst  final_exp",     blst_final_exp(&bout, &bout), 100);

    /* ---- Full Pairing (no frobenius constants for fiat, so just time miller) ---- */
    printf("\n--- Summary ---\n");
    printf("Note: fiat-crypto pairing uses generic C (no asm).\n");
    printf("      blst uses hand-tuned x86-64 assembly.\n");
    printf("      fiat final_exp uses placeholder Frobenius constants (wrong result, valid timing).\n");

    free((void*)a); free((void*)b); free((void*)c);
    free((void*)f1); free((void*)f2); free((void*)f3);
    free((void*)out); free((void*)px); free((void*)py);
    free((void*)qx); free((void*)qy);
    free((void*)g1p2); free((void*)g2p2); free((void*)wfp2c1);
    return 0;
}
