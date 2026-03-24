#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

/* Include the extracted code */
#include "bls377_pairing.c"

/* Timing helper */
static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

/* BLS12-377 field element = 6 x 64-bit words = 48 bytes */
#define FP_BYTES 48
#define FP2_BYTES (2 * FP_BYTES)
#define FP6_BYTES (3 * FP2_BYTES)
#define FP12_BYTES (2 * FP6_BYTES)

/* Simple aligned allocation */
static void *alloc_felem(size_t bytes) {
    void *p = aligned_alloc(64, bytes);
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
    printf("%-30s %8.1f ns/op  (%d iters)\n", name, _elapsed / (iters), (iters)); \
} while(0)

int main(void) {
    uintptr_t a = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t b = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t c = (uintptr_t)alloc_felem(FP_BYTES);

    uintptr_t a2 = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t b2 = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t c2 = (uintptr_t)alloc_felem(FP2_BYTES);

    uintptr_t a6 = (uintptr_t)alloc_felem(FP6_BYTES);
    uintptr_t b6 = (uintptr_t)alloc_felem(FP6_BYTES);
    uintptr_t c6 = (uintptr_t)alloc_felem(FP6_BYTES);

    uintptr_t a12 = (uintptr_t)alloc_felem(FP12_BYTES);
    uintptr_t b12 = (uintptr_t)alloc_felem(FP12_BYTES);
    uintptr_t c12 = (uintptr_t)alloc_felem(FP12_BYTES);

    /* Initialize with non-zero values */
    set_small(a, 7);
    set_small(b, 13);
    set_small(a2, 7);
    set_small(a2 + FP_BYTES, 3);
    set_small(b2, 13);
    set_small(b2 + FP_BYTES, 5);

    /* Copy to Fp6/Fp12 */
    memcpy((void*)a6, (void*)a2, FP2_BYTES);
    memcpy((void*)(a6 + FP2_BYTES), (void*)b2, FP2_BYTES);
    memcpy((void*)b6, (void*)b2, FP2_BYTES);
    memcpy((void*)a12, (void*)a6, FP6_BYTES);
    memcpy((void*)(a12 + FP6_BYTES), (void*)a6, FP6_BYTES);
    memcpy((void*)b12, (void*)a12, FP12_BYTES);

    printf("=== BLS12-377 fiat-crypto/bedrock2 benchmarks ===\n\n");

    /* Fp operations */
    BENCH("Fp mul",    bls377_mul(c, a, b), 1000000);
    BENCH("Fp square", bls377_square(c, a), 1000000);
    BENCH("Fp add",    bls377_add(c, a, b), 1000000);
    BENCH("Fp sub",    bls377_sub(c, a, b), 1000000);

    /* Fp2 operations (via Fp6 layer which calls Fp) */
    /* Note: Fp2 add/sub/mul are inside Fp6 functions, not directly callable.
       We benchmark through Fp6 operations instead. */

    /* Fp6 operations */
    BENCH("Fp6 mul",    bls377_Fp6_mul(c6, a6, b6), 100000);
    BENCH("Fp6 square", bls377_Fp6_square(c6, a6),  100000);
    BENCH("Fp6 inv",    bls377_Fp6_inv(c6, a6),     10000);

    /* Fp12 operations */
    BENCH("Fp12 mul",    bls377_Fp12_mul(c12, a12, b12), 100000);
    BENCH("Fp12 square", bls377_Fp12_square(c12, a12),   100000);
    BENCH("Fp12 inv",    bls377_Fp12_inv(c12, a12),      10000);

    /* Mul_xi */
    BENCH("Fp2 mul_xi",  bls377_Fp2_mul_xi(c2, a2), 1000000);

    printf("\n=== Done ===\n");

    free((void*)a); free((void*)b); free((void*)c);
    free((void*)a2); free((void*)b2); free((void*)c2);
    free((void*)a6); free((void*)b6); free((void*)c6);
    free((void*)a12); free((void*)b12); free((void*)c12);
    return 0;
}
