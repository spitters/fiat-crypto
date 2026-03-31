#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

/* fiat-crypto BLS12-377 pairing (self-contained) */
#include "bls377_pairing.c"

/* blst BLS12-381 */
#include "blst.h"

static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

#define FP_BYTES 48
#define FP2_BYTES (2*FP_BYTES)
#define FP6_BYTES (3*FP2_BYTES)
#define FP12_BYTES (2*FP6_BYTES)

static void *ae(size_t n) { void *p = aligned_alloc(64, n); memset(p,0,n); return p; }

#define BENCH(name, call, iters) do { \
    for (int _w = 0; _w < 100; _w++) { call; } \
    double _s = get_time_ns(); \
    for (int _i = 0; _i < (iters); _i++) { call; } \
    double _e = get_time_ns(); \
    printf("%-45s %8.1f ns/op\n", name, (_e - _s) / (iters)); \
} while(0)

int main(void) {
    printf("====================================================================\n");
    printf("  fiat-crypto (bedrock2, pure C) vs blst (hand-tuned x86-64 asm)\n");
    printf("  fiat uses BLS12-377 (same 384-bit limbs as BLS12-381)\n");
    printf("====================================================================\n\n");

    uintptr_t a = (uintptr_t)ae(FP_BYTES);
    uintptr_t b = (uintptr_t)ae(FP_BYTES);
    uintptr_t c = (uintptr_t)ae(FP_BYTES);
    ((uint64_t*)a)[0] = 42; ((uint64_t*)b)[0] = 17;

    blst_fp ba, bb, bc;
    memset(&ba,0,sizeof(ba)); memset(&bb,0,sizeof(bb));
    ba.l[0] = 42; bb.l[0] = 17;

    printf("--- Fp (384-bit Montgomery) ---\n");
    BENCH("fiat   Fp mul",    bls377_mul(c, a, b),           1000000);
    BENCH("blst   Fp mul",    blst_fp_mul(&bc, &ba, &bb),    1000000);
    BENCH("fiat   Fp square", bls377_square(c, a),            1000000);
    BENCH("blst   Fp sqr",    blst_fp_sqr(&bc, &ba),         1000000);
    BENCH("fiat   Fp add",    bls377_add(c, a, b),            1000000);
    BENCH("blst   Fp add",    blst_fp_add(&bc, &ba, &bb),    1000000);
    BENCH("fiat   Fp sub",    bls377_sub(c, a, b),            1000000);
    BENCH("blst   Fp sub",    blst_fp_sub(&bc, &ba, &bb),    1000000);

    printf("\n--- Fp12 ---\n");
    uintptr_t f1 = (uintptr_t)ae(FP12_BYTES);
    uintptr_t f2 = (uintptr_t)ae(FP12_BYTES);
    uintptr_t f3 = (uintptr_t)ae(FP12_BYTES);
    ((uint64_t*)f1)[0] = 1; ((uint64_t*)f2)[0] = 2;

    blst_fp12 bf1, bf2, bf3;
    memset(&bf1,0,sizeof(bf1)); memset(&bf2,0,sizeof(bf2));
    bf1.fp6[0].fp2[0].fp[0].l[0] = 1;
    bf2.fp6[0].fp2[0].fp[0].l[0] = 2;

    BENCH("fiat   Fp12 mul",    bls377_Fp12_mul(f3, f1, f2),       100000);
    BENCH("blst   Fp12 mul",    blst_fp12_mul(&bf3, &bf1, &bf2),   100000);
    BENCH("fiat   Fp12 square", bls377_Fp12_square(f3, f1),        100000);
    BENCH("blst   Fp12 sqr",    blst_fp12_sqr(&bf3, &bf1),        100000);
    BENCH("fiat   Fp12 inv",    bls377_Fp12_inv(f3, f1),           10000);
    BENCH("blst   Fp12 inv",    blst_fp12_inverse(&bf3, &bf1),     10000);

    printf("\n--- Pairing components (blst only — BLS12-381) ---\n");
    blst_p1_affine bp1; blst_p2_affine bp2; blst_fp12 bout;
    memset(&bp1,0,sizeof(bp1)); bp1.x.l[0]=1; bp1.y.l[0]=1;
    memset(&bp2,0,sizeof(bp2)); bp2.x.fp[0].l[0]=1; bp2.y.fp[0].l[0]=1;
    BENCH("blst   miller_loop",   blst_miller_loop(&bout, &bp2, &bp1), 1000);
    BENCH("blst   final_exp",     blst_final_exp(&bout, &bout),         100);

    printf("\n--- Summary ---\n");
    /* Compute ratios */
    int N = 1000000;
    double s, e;
    s = get_time_ns(); for (int i=0;i<N;i++) bls377_mul(c,a,b); e = get_time_ns();
    double fiat_mul = (e-s)/N;
    s = get_time_ns(); for (int i=0;i<N;i++) blst_fp_mul(&bc,&ba,&bb); e = get_time_ns();
    double blst_mul = (e-s)/N;

    N = 100000;
    s = get_time_ns(); for (int i=0;i<N;i++) bls377_Fp12_mul(f3,f1,f2); e = get_time_ns();
    double fiat_f12 = (e-s)/N;
    s = get_time_ns(); for (int i=0;i<N;i++) blst_fp12_mul(&bf3,&bf1,&bf2); e = get_time_ns();
    double blst_f12 = (e-s)/N;

    printf("Fp mul:   fiat=%.1f ns, blst=%.1f ns  → fiat/blst = %.2fx\n", fiat_mul, blst_mul, fiat_mul/blst_mul);
    printf("Fp12 mul: fiat=%.1f ns, blst=%.1f ns  → fiat/blst = %.2fx\n", fiat_f12, blst_f12, fiat_f12/blst_f12);

    free((void*)a); free((void*)b); free((void*)c);
    free((void*)f1); free((void*)f2); free((void*)f3);
    return 0;
}
