/* Direct A/B comparison: bedrock2 Fp2_mul vs typed Fp2_mul.
   Compile: gcc -O3 -march=native -w -o bench_fp2_cmp bench_fp2_compare.c */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

typedef uintptr_t br_word_t;

/* === Fp base ops: extracted from bedrock2 (keep in separate compilation unit) === */
/* We include the full file, but only benchmark Fp2 ops */
#include "bls24_509_pairing.c"

/* Provide missing stubs */
void bls24_509_zero(br_word_t out) { memset((void*)out, 0, 64); }
void bls24_509_one(br_word_t out) {
    static const uint64_t R[8] = {
        0xD50A57A3A6E01715ULL, 0x4AB46410CFA0D504ULL,
        0x38E8E4D5D79D6774ULL, 0x36CC2E2E7C7A56DCULL,
        0x6AFE0117020AA12EULL, 0,0,0};
    memcpy((void*)out, R, 64);
}
void bls24_509_select_znz(br_word_t out, br_word_t c, br_word_t x, br_word_t y) {
    uint64_t *o=(uint64_t*)out, *a=(uint64_t*)x, *b=(uint64_t*)y;
    uint64_t mask = -(uint64_t)(c!=0);
    for(int i=0;i<8;i++) o[i]=(a[i]&~mask)|(b[i]&mask);
}
void bls24_509_from_word(br_word_t o, br_word_t w) { memset((void*)o,0,64); }
void bls24_Fp4_inv(br_word_t o, br_word_t x) { memcpy((void*)o,(void*)x,256); }
void bls24_Fp8_inv(br_word_t o, br_word_t x) { memcpy((void*)o,(void*)x,512); }

/* === Typed Fp2 operations === */
typedef struct { uint64_t v[8]; } Fp_t;
typedef struct { Fp_t c0; Fp_t c1; } Fp2_t;

#define FP_ADD(o,a,b) bls24_509_add((br_word_t)(o),(br_word_t)(a),(br_word_t)(b))
#define FP_SUB(o,a,b) bls24_509_sub((br_word_t)(o),(br_word_t)(a),(br_word_t)(b))
#define FP_MUL(o,a,b) bls24_509_mul((br_word_t)(o),(br_word_t)(a),(br_word_t)(b))
#define FP_SQR(o,a)   bls24_509_square((br_word_t)(o),(br_word_t)(a))
#define FP_OPP(o,a)   bls24_509_opp((br_word_t)(o),(br_word_t)(a))

void typed_Fp2_mul(Fp2_t *restrict out, const Fp2_t *restrict x, const Fp2_t *restrict y) {
    Fp_t d0, d1, t;
    FP_MUL(&d0, &x->c0, &y->c0);
    FP_MUL(&d1, &x->c1, &y->c1);
    FP_ADD(&t, &x->c0, &x->c1);
    FP_ADD(&out->c1, &y->c0, &y->c1);
    FP_MUL(&out->c1, &out->c1, &t);
    FP_SUB(&out->c1, &out->c1, &d0);
    FP_SUB(&out->c1, &out->c1, &d1);
    FP_OPP(&t, &d1);
    FP_ADD(&out->c0, &d0, &t);
}

void typed_Fp2_square(Fp2_t *restrict out, const Fp2_t *restrict x) {
    Fp_t d0, d1, cross;
    FP_SQR(&d0, &x->c0);
    FP_SQR(&d1, &x->c1);
    FP_MUL(&cross, &x->c0, &x->c1);
    FP_ADD(&out->c1, &cross, &cross);
    FP_OPP(&cross, &d1);
    FP_ADD(&out->c0, &d0, &cross);
}

void typed_Fp2_add(Fp2_t *restrict out, const Fp2_t *restrict x, const Fp2_t *restrict y) {
    FP_ADD(&out->c0, &x->c0, &y->c0);
    FP_ADD(&out->c1, &x->c1, &y->c1);
}

void typed_Fp2_sub(Fp2_t *restrict out, const Fp2_t *restrict x, const Fp2_t *restrict y) {
    FP_SUB(&out->c0, &x->c0, &y->c0);
    FP_SUB(&out->c1, &x->c1, &y->c1);
}

/* Timing */
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
    Fp2_t *at=(Fp2_t*)a, *bt=(Fp2_t*)b, *ct=(Fp2_t*)c;

    ((uint64_t*)a)[0]=7; ((uint64_t*)a)[8]=3;
    ((uint64_t*)b)[0]=13; ((uint64_t*)b)[8]=5;

    int N = 500000;

    printf("=== Fp2: bedrock2 vs typed-struct ===\n\n");

    printf("Fp2 mul:\n");
    BENCH("bedrock2 (uintptr_t + stackalloc):", bls24_Fp2_mul(cp, ap, bp), N);
    BENCH("typed (restrict struct, no copy):", typed_Fp2_mul(ct, at, bt), N);

    printf("\nFp2 square:\n");
    BENCH("bedrock2 (uintptr_t + stackalloc):", bls24_Fp2_square(cp, ap), N);
    BENCH("typed (restrict struct, no copy):", typed_Fp2_square(ct, at), N);

    printf("\nFp2 add:\n");
    BENCH("bedrock2 (copy-elim'd):", bls24_Fp2_add(cp, ap, bp), N);
    BENCH("typed (restrict struct):", typed_Fp2_add(ct, at, bt), N);

    printf("\nFp2 sub:\n");
    BENCH("bedrock2 (copy-elim'd):", bls24_Fp2_sub(cp, ap, bp), N);
    BENCH("typed (restrict struct):", typed_Fp2_sub(ct, at, bt), N);

    printf("\nFp mul (reference):\n");
    BENCH("bedrock2 Fp mul:", bls24_509_mul(cp, ap, bp), N);

    return 0;
}
