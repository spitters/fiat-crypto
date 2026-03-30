/* Benchmark: DSD final exp + CryptOpt Fp mul/sqr for BLS12-381 pairing */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

/* Include the pairing C code */
#include "bls12_pairing.c"

/* CryptOpt assembly functions */
extern void fiat_bls12_381_p_mul(uint64_t out[6], const uint64_t a[6], const uint64_t b[6]);
extern void fiat_bls12_381_p_square(uint64_t out[6], const uint64_t a[6]);

/* Wrappers that match the bls12_pairing.c signature (br_word_t = uintptr_t) */
static void bls12_mul_cryptopt(br_word_t out, br_word_t a, br_word_t b) {
    fiat_bls12_381_p_mul((uint64_t*)out, (const uint64_t*)a, (const uint64_t*)b);
}
static void bls12_square_cryptopt(br_word_t out, br_word_t a) {
    fiat_bls12_381_p_square((uint64_t*)out, (const uint64_t*)a);
}

/* Timing macro */
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
    printf("%-45s %8.1f ns/op  (%d iters)\n", name, (_end - _start) / (iters), iters); \
} while(0)

int main(void) {
    /* Allocate test data */
    uint64_t fp_a[6], fp_b[6], fp_c[6];
    for (int i = 0; i < 6; i++) { fp_a[i] = 0x1234567890abcdef + i; fp_b[i] = 0xfedcba0987654321 + i; }

    printf("=== BLS12-381 Fp mul/sqr ===\n");
    BENCH("fiat-crypto Fp mul (C)",   bls12_mul((uintptr_t)fp_c, (uintptr_t)fp_a, (uintptr_t)fp_b), 1000000);
    BENCH("CryptOpt Fp mul (asm)",    bls12_mul_cryptopt((uintptr_t)fp_c, (uintptr_t)fp_a, (uintptr_t)fp_b), 1000000);
    BENCH("fiat-crypto Fp sqr (C)",   bls12_square((uintptr_t)fp_c, (uintptr_t)fp_a), 1000000);
    BENCH("CryptOpt Fp sqr (asm)",    bls12_square_cryptopt((uintptr_t)fp_c, (uintptr_t)fp_a), 1000000);

    return 0;
}
