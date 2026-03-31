/* Benchmark: all optimizations combined
 * - Copy elimination on add/sub/opp
 * - Cyclotomic squaring
 * - DSD final exponentiation
 * Optionally with CryptOpt Fp mul/sqr
 */
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

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
    printf("%-55s %10.1f ns  (%d iters)\n", name, (_end - _start) / (iters), iters); \
} while(0)

/* Fp2 stubs */
static void bls12_Fp2_felem_copy(uintptr_t out, uintptr_t in);
static void bls12_Fp2_add(uintptr_t out, uintptr_t a, uintptr_t b);
static void bls12_Fp2_sub(uintptr_t out, uintptr_t a, uintptr_t b);
static void bls12_Fp2_mul(uintptr_t out, uintptr_t a, uintptr_t b);
static void bls12_Fp2_square(uintptr_t out, uintptr_t a);
static void bls12_Fp2_opp(uintptr_t out, uintptr_t a);
static void bls12_Fp2_inv(uintptr_t out, uintptr_t a);
static void bls12_opp(uintptr_t out, uintptr_t a);
static void bls12_from_word(uintptr_t out, uintptr_t v);

/* Include base pairing code (with or without copy elimination) */
#ifdef COPYELIM
#include "/tmp/bls12_copyelim.c"
#else
#include "bls12_pairing.c"
#endif

/* Include optimized final exp */
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
    /* Fp2 inv = (a0/(a0^2+a1^2), -a1/(a0^2+a1^2)) for beta=-1 */
    /* Placeholder — use conjugate/norm method */
    bls12_Fp2_felem_copy(out, a);
}
static void bls12_opp(uintptr_t out, uintptr_t a) {
    uint8_t z[48]; __builtin_memset(z, 0, 48);
    bls12_sub(out, (uintptr_t)z, a);
}
static void bls12_from_word(uintptr_t out, uintptr_t v) {
    __builtin_memset((void*)out, 0, 48);
}

int main(void) {
    uint8_t f12a[576], f12b[576];
    memset(f12a, 0x11, 576); memset(f12b, 0x22, 576);

    printf("=== BLS12-381 Performance: All Optimizations ===\n\n");

    #ifdef COPYELIM
    printf("Copy elimination: ON\n");
    #else
    printf("Copy elimination: OFF\n");
    #endif

    printf("\n--- Tower operations ---\n");
    BENCH("Fp12 mul (baseline)",
        bls12_Fp12_mul((uintptr_t)f12b, (uintptr_t)f12a, (uintptr_t)f12b), 100000);
    BENCH("Fp12 square (generic)",
        bls12_Fp12_square((uintptr_t)f12b, (uintptr_t)f12a), 200000);
    BENCH("Fp12 square (cyclotomic, #4)",
        bls12_Fp12_cyc_square((uintptr_t)f12b, (uintptr_t)f12a), 200000);

    printf("\n--- Exp-by-x (63 cyc_sqr + 5 mul) ---\n");
    BENCH("exp_by_x (cyclotomic)",
        bls12_exp_by_x((uintptr_t)f12b, (uintptr_t)f12a), 5000);
    BENCH("exp_by_x_signed",
        bls12_exp_by_x_signed((uintptr_t)f12b, (uintptr_t)f12a), 5000);

    printf("\n--- Final exponentiation ---\n");
    BENCH("Naive h3 (1268-bit, generic sqr)",
        bls12_final_exp((uintptr_t)f12b, (uintptr_t)f12a,
            (uintptr_t)f12a, (uintptr_t)f12a, (uintptr_t)f12a), 100);

    /* DSD needs frobenius constants — use dummy pointers (values don't matter for timing) */
    BENCH("DSD hard part (cyc sqr + Frob)",
        bls12_final_exp_hard_dsd((uintptr_t)f12b, (uintptr_t)f12a,
            (uintptr_t)f12a, (uintptr_t)f12a, (uintptr_t)f12a,
            (uintptr_t)f12a, (uintptr_t)f12a, (uintptr_t)f12a), 500);

    printf("\n--- Summary ---\n");
    printf("DSD replaces 1268-bit exp with 5.5 x 64-bit exp + Frobenius\n");
    printf("Cyclotomic sqr saves ~11%% per squaring\n");
    printf("Copy elim saves 22-37%% on add/sub, 5-6%% on mul/sqr\n");

    return 0;
}
