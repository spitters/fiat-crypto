/* Benchmark: baseline vs always_inline + uninitialized stack */
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
    printf("%-50s %8.1f ns  (%d iters)\n", name, (_end - _start) / (iters), iters); \
} while(0)

/* Choose which version to include via -DOPTIMIZED */
#ifdef OPTIMIZED
#include "/tmp/bls12_pairing_opt.c"
#else
#include "bls12_pairing.c"
#endif

/* Include Fp2 ops */
#include "/tmp/fp2_ops.c"

int main(void) {
    uint8_t fp2a[96], fp2b[96], fp2c[96];
    uint8_t f12a[576], f12b[576];
    memset(fp2a, 0x42, 96); memset(fp2b, 0x37, 96);
    memset(f12a, 0x11, 576); memset(f12b, 0x22, 576);

    #ifdef OPTIMIZED
    printf("=== OPTIMIZED (always_inline + uninitialized stack) ===\n");
    #else
    printf("=== BASELINE ===\n");
    #endif

    uint64_t a[6] = {0x1234, 0x5678, 0x9abc, 0xdef0, 0x1111, 0x0222};
    uint64_t b[6] = {0xabcd, 0xef01, 0x2345, 0x6789, 0x3333, 0x0444};
    uint64_t c[6];

    BENCH("Fp mul",          bls12_mul((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 2000000);
    BENCH("Fp2 mul",         bls12_Fp2_mul((uintptr_t)fp2c, (uintptr_t)fp2a, (uintptr_t)fp2b), 1000000);
    BENCH("Fp6 mul",         bls12_Fp6_mul((uintptr_t)f12a, (uintptr_t)f12a, (uintptr_t)f12b), 200000);
    BENCH("Fp12 mul",        bls12_Fp12_mul((uintptr_t)f12b, (uintptr_t)f12a, (uintptr_t)f12b), 100000);
    BENCH("Fp12 square",     bls12_Fp12_square((uintptr_t)f12b, (uintptr_t)f12a), 200000);

    return 0;
}
