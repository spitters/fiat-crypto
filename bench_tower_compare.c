/* Full tower A/B: bedrock2 vs typed-struct at every level */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
typedef uintptr_t br_word_t;

/* bedrock2 tower ops (from pairing .o) */
extern void bls24_Fp2_mul(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp2_square(br_word_t, br_word_t);
extern void bls24_Fp2_add(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp2_sub(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp4_mul(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp4_square(br_word_t, br_word_t);
extern void bls24_Fp4_add(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp4_sub(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp8_mul(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp8_square(br_word_t, br_word_t);
extern void bls24_Fp8_add(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp8_sub(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp24_mul(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp24_square(br_word_t, br_word_t);
extern void bls24_Fp24_add(br_word_t, br_word_t, br_word_t);
extern void bls24_Fp24_sub(br_word_t, br_word_t, br_word_t);
extern void bls24_509_mul(br_word_t, br_word_t, br_word_t);

/* typed tower ops (from tower_typed .o) */
typedef struct { uint64_t v[8]; } Fp;
typedef struct { Fp c0; Fp c1; } Fp2;
typedef struct { Fp2 c0; Fp2 c1; } Fp4;
typedef struct { Fp4 c0; Fp4 c1; } Fp8;
typedef struct { Fp8 c0; Fp8 c1; Fp8 c2; } Fp24;
extern void typed_Fp2_mul(Fp2*, const Fp2*, const Fp2*);
extern void typed_Fp2_square(Fp2*, const Fp2*);
extern void typed_Fp2_add(Fp2*, const Fp2*, const Fp2*);
extern void typed_Fp2_sub(Fp2*, const Fp2*, const Fp2*);
extern void typed_Fp4_mul(Fp4*, const Fp4*, const Fp4*);
extern void typed_Fp4_square(Fp4*, const Fp4*);
extern void typed_Fp4_add(Fp4*, const Fp4*, const Fp4*);
extern void typed_Fp4_sub(Fp4*, const Fp4*, const Fp4*);
extern void typed_Fp8_mul(Fp8*, const Fp8*, const Fp8*);
extern void typed_Fp8_square(Fp8*, const Fp8*);
extern void typed_Fp8_add(Fp8*, const Fp8*, const Fp8*);
extern void typed_Fp8_sub(Fp8*, const Fp8*, const Fp8*);
extern void typed_Fp24_mul(Fp24*, const Fp24*, const Fp24*);
extern void typed_Fp24_square(Fp24*, const Fp24*);
extern void typed_Fp24_add(Fp24*, const Fp24*, const Fp24*);
extern void typed_Fp24_sub(Fp24*, const Fp24*, const Fp24*);

static double get_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}
#define BENCH(name, call, iters) do { \
    for (int _w = 0; _w < 100; _w++) { call; } \
    double _s = get_ns(); \
    for (int _i = 0; _i < (iters); _i++) { call; } \
    double _e = (get_ns()-_s)/(iters); \
    printf("  %-45s %10.1f ns\n", name, _e); \
} while(0)

int main(void) {
    uint8_t __attribute__((aligned(64))) a24[1536]={0}, b24[1536]={0}, c24[1536]={0};
    /* Init with small values */
    ((uint64_t*)a24)[0]=7; ((uint64_t*)a24)[8]=3; ((uint64_t*)a24)[16]=11;
    ((uint64_t*)b24)[0]=13; ((uint64_t*)b24)[8]=5; ((uint64_t*)b24)[16]=17;

    br_word_t a=(br_word_t)a24, b=(br_word_t)b24, c=(br_word_t)c24;
    Fp24 *at=(Fp24*)a24, *bt=(Fp24*)b24, *ct=(Fp24*)c24;

    printf("=== Full tower: bedrock2 vs typed-struct (separate .o) ===\n\n");

    printf("%-47s %10s\n", "Operation", "Time");
    printf("%-47s %10s\n", "---------", "----");

    BENCH("Fp mul (reference):",                bls24_509_mul(c,a,b), 500000);
    printf("\n");

    BENCH("Fp2 mul  [bedrock2]:",               bls24_Fp2_mul(c,a,b), 300000);
    BENCH("Fp2 mul  [typed]:",                  typed_Fp2_mul((Fp2*)ct,(Fp2*)at,(Fp2*)bt), 300000);
    BENCH("Fp2 sqr  [bedrock2]:",               bls24_Fp2_square(c,a), 300000);
    BENCH("Fp2 sqr  [typed]:",                  typed_Fp2_square((Fp2*)ct,(Fp2*)at), 300000);
    BENCH("Fp2 add  [bedrock2]:",               bls24_Fp2_add(c,a,b), 1000000);
    BENCH("Fp2 add  [typed]:",                  typed_Fp2_add((Fp2*)ct,(Fp2*)at,(Fp2*)bt), 1000000);
    printf("\n");

    BENCH("Fp4 mul  [bedrock2]:",               bls24_Fp4_mul(c,a,b), 100000);
    BENCH("Fp4 mul  [typed]:",                  typed_Fp4_mul((Fp4*)ct,(Fp4*)at,(Fp4*)bt), 100000);
    BENCH("Fp4 sqr  [bedrock2]:",               bls24_Fp4_square(c,a), 100000);
    BENCH("Fp4 sqr  [typed]:",                  typed_Fp4_square((Fp4*)ct,(Fp4*)at), 100000);
    BENCH("Fp4 add  [bedrock2]:",               bls24_Fp4_add(c,a,b), 500000);
    BENCH("Fp4 add  [typed]:",                  typed_Fp4_add((Fp4*)ct,(Fp4*)at,(Fp4*)bt), 500000);
    printf("\n");

    BENCH("Fp8 mul  [bedrock2]:",               bls24_Fp8_mul(c,a,b), 50000);
    BENCH("Fp8 mul  [typed]:",                  typed_Fp8_mul((Fp8*)ct,(Fp8*)at,(Fp8*)bt), 50000);
    BENCH("Fp8 sqr  [bedrock2]:",               bls24_Fp8_square(c,a), 50000);
    BENCH("Fp8 sqr  [typed]:",                  typed_Fp8_square((Fp8*)ct,(Fp8*)at), 50000);
    BENCH("Fp8 add  [bedrock2]:",               bls24_Fp8_add(c,a,b), 300000);
    BENCH("Fp8 add  [typed]:",                  typed_Fp8_add((Fp8*)ct,(Fp8*)at,(Fp8*)bt), 300000);
    printf("\n");

    BENCH("Fp24 mul [bedrock2]:",               bls24_Fp24_mul(c,a,b), 10000);
    BENCH("Fp24 mul [typed]:",                  typed_Fp24_mul(ct,at,bt), 10000);
    BENCH("Fp24 sqr [bedrock2]:",               bls24_Fp24_square(c,a), 10000);
    BENCH("Fp24 sqr [typed]:",                  typed_Fp24_square(ct,at), 10000);
    BENCH("Fp24 add [bedrock2]:",               bls24_Fp24_add(c,a,b), 100000);
    BENCH("Fp24 add [typed]:",                  typed_Fp24_add(ct,at,bt), 100000);

    return 0;
}
