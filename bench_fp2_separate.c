/* A/B benchmark with SEPARATE compilation.
   Fp ops in one .o, typed Fp2 ops in another .o.
   This is the key test: does separate compilation help? */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

typedef uintptr_t br_word_t;

/* Forward-declare bedrock2 Fp2 ops (from pairing .o) */
extern void bls24_Fp2_mul(br_word_t out, br_word_t inx, br_word_t iny);
extern void bls24_Fp2_square(br_word_t out, br_word_t x);
extern void bls24_Fp2_add(br_word_t out, br_word_t inx, br_word_t iny);
extern void bls24_Fp2_sub(br_word_t out, br_word_t inx, br_word_t iny);
extern void bls24_509_mul(br_word_t out, br_word_t in0, br_word_t in1);

/* Forward-declare typed Fp2 ops (from bls24_fp2_typed.o) */
typedef struct { uint64_t v[8]; } Fp;
typedef struct { Fp c0; Fp c1; } Fp2;
extern void typed_Fp2_mul(Fp2 *restrict out, const Fp2 *restrict x, const Fp2 *restrict y);
extern void typed_Fp2_square(Fp2 *restrict out, const Fp2 *restrict x);
extern void typed_Fp2_add(Fp2 *restrict out, const Fp2 *restrict x, const Fp2 *restrict y);
extern void typed_Fp2_sub(Fp2 *restrict out, const Fp2 *restrict x, const Fp2 *restrict y);

static double get_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

#define BENCH(name, call, iters) do { \
    for (int _w = 0; _w < 200; _w++) { call; } \
    double _s = get_ns(); \
    for (int _i = 0; _i < (iters); _i++) { call; } \
    printf("  %-42s %8.1f ns\n", name, (get_ns()-_s)/(iters)); \
} while(0)

int main(void) {
    uint8_t __attribute__((aligned(64))) a[128]={0}, b[128]={0}, c[128]={0};
    br_word_t ap=(br_word_t)a, bp=(br_word_t)b, cp=(br_word_t)c;
    Fp2 *at=(Fp2*)a, *bt=(Fp2*)b, *ct=(Fp2*)c;

    ((uint64_t*)a)[0]=7; ((uint64_t*)a)[8]=3;
    ((uint64_t*)b)[0]=13; ((uint64_t*)b)[8]=5;

    int N = 500000;

    printf("=== Fp2: bedrock2 vs SEPARATELY-COMPILED typed ===\n\n");

    printf("Fp2 mul:\n");
    BENCH("bedrock2 (uintptr_t + stackalloc):", bls24_Fp2_mul(cp, ap, bp), N);
    BENCH("typed (restrict, separate .o):", typed_Fp2_mul(ct, at, bt), N);

    printf("\nFp2 square:\n");
    BENCH("bedrock2 (uintptr_t + stackalloc):", bls24_Fp2_square(cp, ap), N);
    BENCH("typed (restrict, separate .o):", typed_Fp2_square(ct, at), N);

    printf("\nFp2 add:\n");
    BENCH("bedrock2 (copy-elim'd):", bls24_Fp2_add(cp, ap, bp), N);
    BENCH("typed (restrict, separate .o):", typed_Fp2_add(ct, at, bt), N);

    printf("\nFp2 sub:\n");
    BENCH("bedrock2 (copy-elim'd):", bls24_Fp2_sub(cp, ap, bp), N);
    BENCH("typed (restrict, separate .o):", typed_Fp2_sub(ct, at, bt), N);

    printf("\nFp mul (reference):\n");
    BENCH("bedrock2 Fp mul:", bls24_509_mul(cp, ap, bp), N);

    return 0;
}
