/* Benchmark: BLS12-377 Fp mul/sqr with CryptOpt assembly vs fiat-crypto C
 * Build: see Makefile.bench377 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

/* Include the pairing C code (defines bls377_mul, bls377_square) */
static const uint64_t BLS377_P[6] = {
    0x8508c00000000001ULL, 0x170b5d4430000000ULL,
    0x1ef3622fba094800ULL, 0x1a22d9f300f5138fULL,
    0xc63b05c06ca1493bULL, 0x01ae3a4617c510eaULL
};
static const uint64_t BLS377_R[6] = {
    0x7d1c7fffffffd3b1ULL, 0x5e941d24c60ba5e9ULL,
    0x54894ed68a3d2a2eULL, 0x547f52db80ceae5cULL,
    0xd6c3bc1926ff4de3ULL, 0x01660e3656e542d7ULL
};
typedef uintptr_t br_word_t;
void bls377_add(br_word_t out, br_word_t in0, br_word_t in1);
static void bls377_sub(br_word_t out, br_word_t in0, br_word_t in1);
void bls377_opp(br_word_t out, br_word_t x) {
    static uint64_t zero[6] = {0};
    bls377_sub(out, (br_word_t)zero, x);
}
void bls377_from_word(br_word_t out, br_word_t w) {
    uint64_t *o = (uint64_t *)out;
    if (w == 0) memset(o, 0, 48);
    else if (w == 1) memcpy(o, BLS377_R, 48);
    else {
        memcpy(o, BLS377_R, 48);
        for (br_word_t i = 1; i < w; i++)
            bls377_add(out, out, (br_word_t)BLS377_R);
    }
}

#include "bls377_pairing.c"

/* CryptOpt assembly functions */
extern void fiat_bls12_377_p_mul(uint64_t out[6], const uint64_t a[6], const uint64_t b[6]);
extern void fiat_bls12_377_p_square(uint64_t out[6], const uint64_t a[6]);

/* Wrappers matching br_word_t interface */
static void bls377_mul_cryptopt(br_word_t out, br_word_t a, br_word_t b) {
    fiat_bls12_377_p_mul((uint64_t*)out, (const uint64_t*)a, (const uint64_t*)b);
}
static void bls377_square_cryptopt(br_word_t out, br_word_t a) {
    fiat_bls12_377_p_square((uint64_t*)out, (const uint64_t*)a);
}

/* Timing */
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
    uint64_t fp_a[6], fp_b[6], fp_c[6];
    for (int i = 0; i < 6; i++) {
        fp_a[i] = 0x1234567890abcdef + i;
        fp_b[i] = 0xfedcba0987654321 + i;
    }

    printf("=== BLS12-377 Fp mul/sqr: fiat-crypto C vs CryptOpt asm ===\n\n");

    BENCH("fiat-crypto Fp mul (C)",   bls377_mul((uintptr_t)fp_c, (uintptr_t)fp_a, (uintptr_t)fp_b), 1000000);
    BENCH("CryptOpt   Fp mul (asm)",  bls377_mul_cryptopt((uintptr_t)fp_c, (uintptr_t)fp_a, (uintptr_t)fp_b), 1000000);
    BENCH("fiat-crypto Fp sqr (C)",   bls377_square((uintptr_t)fp_c, (uintptr_t)fp_a), 1000000);
    BENCH("CryptOpt   Fp sqr (asm)",  bls377_square_cryptopt((uintptr_t)fp_c, (uintptr_t)fp_a), 1000000);

    /* Verify correctness: both should produce the same result */
    uint64_t c_result[6], asm_result[6];
    bls377_mul((uintptr_t)c_result, (uintptr_t)fp_a, (uintptr_t)fp_b);
    bls377_mul_cryptopt((uintptr_t)asm_result, (uintptr_t)fp_a, (uintptr_t)fp_b);
    int match = (memcmp(c_result, asm_result, 48) == 0);
    printf("\nCorrectness check (mul): %s\n", match ? "PASS" : "FAIL");

    bls377_square((uintptr_t)c_result, (uintptr_t)fp_a);
    bls377_square_cryptopt((uintptr_t)asm_result, (uintptr_t)fp_a);
    match = (memcmp(c_result, asm_result, 48) == 0);
    printf("Correctness check (sqr): %s\n", match ? "PASS" : "FAIL");

    return 0;
}
