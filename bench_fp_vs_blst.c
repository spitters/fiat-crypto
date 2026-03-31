#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

/* fiat-crypto Fp only (from word-by-word Montgomery) */
#include "src/ExtractionOCaml/bls12_64.c"

/* blst */
#include "blst.h"

static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

#define BENCH(name, call, iters) do { \
    for (int _w = 0; _w < 100; _w++) { call; } \
    double _start = get_time_ns(); \
    for (int _i = 0; _i < (iters); _i++) { call; } \
    double _end = get_time_ns(); \
    printf("%-40s %8.1f ns/op  (%d iters)\n", name, (_end - _start) / (iters), iters); \
} while(0)

int main(void) {
    printf("=== BLS12-381 Fp Benchmark: fiat-crypto vs blst ===\n\n");

    /* fiat-crypto uses uint64_t[6] */
    uint64_t fa[6] = {0x1234567890abcdefull, 0xfedcba9876543210ull, 0x1111111111111111ull, 0x2222222222222222ull, 0x3333333333333333ull, 0x0444444444444444ull};
    uint64_t fb[6] = {0xabcdef0123456789ull, 0x9876543210fedcbaull, 0x5555555555555555ull, 0x6666666666666666ull, 0x7777777777777777ull, 0x0888888888888888ull};
    uint64_t fc[6];

    printf("--- fiat-crypto (pure C, word-by-word Montgomery) ---\n");
    BENCH("fiat  Fp mul",    fiat_bls12_mul(fc, fa, fb),    1000000);
    BENCH("fiat  Fp square", fiat_bls12_square(fc, fa),     1000000);
    BENCH("fiat  Fp add",    fiat_bls12_add(fc, fa, fb),    1000000);
    BENCH("fiat  Fp sub",    fiat_bls12_sub(fc, fa, fb),    1000000);

    /* blst uses blst_fp which is also uint64_t[6] */
    blst_fp ba, bb, bc;
    memcpy(&ba, fa, 48);
    memcpy(&bb, fb, 48);

    printf("\n--- blst (hand-tuned x86-64 assembly) ---\n");
    BENCH("blst  Fp mul",    blst_fp_mul(&bc, &ba, &bb),    1000000);
    BENCH("blst  Fp sqr",    blst_fp_sqr(&bc, &ba),         1000000);
    BENCH("blst  Fp add",    blst_fp_add(&bc, &ba, &bb),    1000000);
    BENCH("blst  Fp sub",    blst_fp_sub(&bc, &ba, &bb),    1000000);

    /* Fp12 — blst only */
    printf("\n--- blst Fp12 (for reference) ---\n");
    blst_fp12 bf1, bf2, bf3;
    memset(&bf1, 0, sizeof(bf1)); memset(&bf2, 0, sizeof(bf2));
    bf1.fp6[0].fp2[0].fp[0].l[0] = 1;
    bf2.fp6[0].fp2[0].fp[0].l[0] = 2;
    BENCH("blst  Fp12 mul",     blst_fp12_mul(&bf3, &bf1, &bf2),  100000);
    BENCH("blst  Fp12 sqr",     blst_fp12_sqr(&bf3, &bf1),        100000);

    /* Miller loop — blst only */
    printf("\n--- blst pairing operations ---\n");
    blst_p1_affine bp1;
    blst_p2_affine bp2;
    blst_fp12 bout;
    /* Use generator points */
    memset(&bp1, 0, sizeof(bp1)); bp1.x.l[0] = 1;
    memset(&bp2, 0, sizeof(bp2)); bp2.x.fp[0].l[0] = 1;
    BENCH("blst  miller_loop",  blst_miller_loop(&bout, &bp2, &bp1), 1000);
    BENCH("blst  final_exp",    blst_final_exp(&bout, &bout),         100);

    printf("\n--- Ratio ---\n");
    /* Re-run for ratio calculation */
    double s1, e1, s2, e2;
    int N = 1000000;

    s1 = get_time_ns();
    for (int i = 0; i < N; i++) fiat_bls12_mul(fc, fa, fb);
    e1 = get_time_ns();

    s2 = get_time_ns();
    for (int i = 0; i < N; i++) blst_fp_mul(&bc, &ba, &bb);
    e2 = get_time_ns();

    double fiat_ns = (e1 - s1) / N;
    double blst_ns = (e2 - s2) / N;
    printf("Fp mul:  fiat=%.1f ns, blst=%.1f ns, ratio=%.2fx\n",
           fiat_ns, blst_ns, fiat_ns / blst_ns);

    return 0;
}
