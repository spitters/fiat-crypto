/* Final benchmark: fiat-crypto (all optimizations) vs blst
 *
 * Configurations:
 * 1. Baseline: fiat-crypto generated C, naive h3
 * 2. Optimized: copy elimination + DSD + cyclotomic squaring
 * 3. blst: hand-optimized asm reference
 */
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

/* blst */
#include "blst.h"

static inline double now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}
#define BENCH(name, code, iters) do { \
    for (int _w = 0; _w < 10; _w++) { code; } \
    double _start = now_ns(); \
    for (int _i = 0; _i < (iters); _i++) { code; } \
    double _end = now_ns(); \
    printf("%-55s %10.0f ns  (%d iters)\n", name, (_end - _start) / (iters), iters); \
} while(0)

/* Fp2 stubs for fiat-crypto */
static void bls12_Fp2_felem_copy(uintptr_t out, uintptr_t in);
static void bls12_Fp2_add(uintptr_t out, uintptr_t a, uintptr_t b);
static void bls12_Fp2_sub(uintptr_t out, uintptr_t a, uintptr_t b);
static void bls12_Fp2_mul(uintptr_t out, uintptr_t a, uintptr_t b);
static void bls12_Fp2_square(uintptr_t out, uintptr_t a);
static void bls12_Fp2_opp(uintptr_t out, uintptr_t a);
static void bls12_Fp2_inv(uintptr_t out, uintptr_t a);
static void bls12_opp(uintptr_t out, uintptr_t a);
static void bls12_from_word(uintptr_t out, uintptr_t v);

/* Include fiat-crypto pairing (with copy elimination applied) */
#include "/tmp/bls12_opt.c"

/* Include DSD + cyclotomic squaring */
#include "bls12_optimized.c"

/* Fp2 implementations */
static void bls12_Fp2_felem_copy(uintptr_t out, uintptr_t in) {
    __builtin_memcpy((void*)out, (void*)in, 96);
}
static void bls12_Fp2_add(uintptr_t out, uintptr_t a, uintptr_t b) {
    bls12_add(out, a, b); bls12_add(out+48, a+48, b+48);
}
static void bls12_Fp2_sub(uintptr_t out, uintptr_t a, uintptr_t b) {
    bls12_sub(out, a, b); bls12_sub(out+48, a+48, b+48);
}
static void bls12_Fp2_mul(uintptr_t out, uintptr_t a, uintptr_t b) {
    uint8_t v0[48], v1[48], t0[48], t1[48];
    bls12_mul((uintptr_t)v0, a, b);
    bls12_mul((uintptr_t)v1, a+48, b+48);
    bls12_sub(out, (uintptr_t)v0, (uintptr_t)v1);
    bls12_add((uintptr_t)t0, a, a+48);
    bls12_add((uintptr_t)t1, b, b+48);
    bls12_mul(out+48, (uintptr_t)t0, (uintptr_t)t1);
    bls12_sub(out+48, out+48, (uintptr_t)v0);
    bls12_sub(out+48, out+48, (uintptr_t)v1);
}
static void bls12_Fp2_square(uintptr_t out, uintptr_t a) {
    uint8_t sum[48], diff[48], prod[48];
    bls12_add((uintptr_t)sum, a, a+48);
    bls12_sub((uintptr_t)diff, a, a+48);
    bls12_mul(out, (uintptr_t)sum, (uintptr_t)diff);
    bls12_mul((uintptr_t)prod, a, a+48);
    bls12_add(out+48, (uintptr_t)prod, (uintptr_t)prod);
}
static void bls12_Fp2_opp(uintptr_t out, uintptr_t a) {
    uint8_t z[48]; __builtin_memset(z, 0, 48);
    bls12_sub(out, (uintptr_t)z, a);
    bls12_sub(out+48, (uintptr_t)z, a+48);
}
static void bls12_Fp2_inv(uintptr_t out, uintptr_t a) {
    bls12_Fp2_felem_copy(out, a); /* placeholder */
}
static void bls12_opp(uintptr_t out, uintptr_t a) {
    uint8_t z[48]; __builtin_memset(z, 0, 48);
    bls12_sub(out, (uintptr_t)z, a);
}
static void bls12_from_word(uintptr_t out, uintptr_t v) {
    __builtin_memset((void*)out, 0, 48);
}

int main(void) {
    printf("=== BLS12-381 Pairing Benchmark: fiat-crypto vs blst ===\n\n");

    /* --- Fp level --- */
    uint64_t a[6] = {0x1234567890abcdef, 0xfedcba0987654321, 0x1111111111111111,
                     0x2222222222222222, 0x3333333333333333, 0x0444444444444444};
    uint64_t b[6], c[6];
    memcpy(b, a, 48); b[0] ^= 0xff;

    blst_fp ba, bb, bc;
    memcpy(&ba, a, 48); memcpy(&bb, b, 48);

    printf("--- Fp operations ---\n");
    BENCH("fiat   Fp mul",       bls12_mul((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 2000000);
    BENCH("blst   Fp mul",       blst_fp_mul(&bc, &ba, &bb), 2000000);
    BENCH("fiat   Fp sqr",       bls12_square((uintptr_t)c, (uintptr_t)a), 2000000);
    BENCH("blst   Fp sqr",       blst_fp_sqr(&bc, &ba), 2000000);

    /* --- Fp12 level --- */
    uint8_t f12a[576], f12b[576];
    memset(f12a, 0x11, 576); memset(f12b, 0x22, 576);

    blst_fp12 bf1, bf2, bf3;
    memset(&bf1, 0x11, sizeof(bf1)); memset(&bf2, 0x22, sizeof(bf2));

    printf("\n--- Fp12 operations ---\n");
    BENCH("fiat   Fp12 mul",     bls12_Fp12_mul((uintptr_t)f12b, (uintptr_t)f12a, (uintptr_t)f12b), 100000);
    BENCH("blst   Fp12 mul",     blst_fp12_mul(&bf3, &bf1, &bf2), 100000);
    BENCH("fiat   Fp12 sqr",     bls12_Fp12_square((uintptr_t)f12b, (uintptr_t)f12a), 200000);
    BENCH("blst   Fp12 sqr",     blst_fp12_sqr(&bf3, &bf1), 200000);
    BENCH("fiat   Fp12 cyc_sqr", bls12_Fp12_cyc_square((uintptr_t)f12b, (uintptr_t)f12a), 200000);

    /* --- Final exponentiation hard part --- */
    printf("\n--- Final exponentiation (hard part) ---\n");
    BENCH("fiat   naive h3 (1268-bit)",
        bls12_final_exp((uintptr_t)f12b, (uintptr_t)f12a,
            (uintptr_t)f12a, (uintptr_t)f12a, (uintptr_t)f12a), 50);
    BENCH("fiat   DSD (HHT, cyc sqr)",
        bls12_final_exp_hard_dsd((uintptr_t)f12b, (uintptr_t)f12a,
            (uintptr_t)f12a, (uintptr_t)f12a, (uintptr_t)f12a,
            (uintptr_t)f12a, (uintptr_t)f12a, (uintptr_t)f12a), 200);
    BENCH("blst   final_exp",
        blst_final_exp(&bf3, &bf1), 200);

    /* --- Full pairing (blst only — fiat needs real curve points) --- */
    printf("\n--- Full pairing (blst) ---\n");
    blst_p1_affine p1; blst_p2_affine p2;
    /* Use generator points */
    blst_p1_affine_generator();
    blst_p2_affine_generator();
    memcpy(&p1, blst_p1_affine_generator(), sizeof(p1));
    memcpy(&p2, blst_p2_affine_generator(), sizeof(p2));

    blst_fp12 pairing_result;
    BENCH("blst   miller_loop",  blst_miller_loop(&pairing_result, &p2, &p1), 1000);
    BENCH("blst   final_exp",    blst_final_exp(&bf3, &pairing_result), 500);
    BENCH("blst   full pairing", { blst_miller_loop(&pairing_result, &p2, &p1); blst_final_exp(&bf3, &pairing_result); }, 500);

    printf("\n--- Summary ---\n");
    printf("fiat-crypto: DSD + cyclotomic squaring + copy elimination\n");
    printf("blst: hand-optimized x86-64 asm (v0.3.16)\n");

    return 0;
}
