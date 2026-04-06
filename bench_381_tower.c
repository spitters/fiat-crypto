/* Quick tower benchmark for BLS12-381 (fiat-crypto only, no blst needed) */
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

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

#include "/tmp/bls12_opt.c"

/* Fp2 implementations */
static void bls12_Fp2_felem_copy(uintptr_t out, uintptr_t in) { __builtin_memcpy((void*)out, (void*)in, 96); }
static void bls12_Fp2_add(uintptr_t out, uintptr_t a, uintptr_t b) { bls12_add(out, a, b); bls12_add(out+48, a+48, b+48); }
static void bls12_Fp2_sub(uintptr_t out, uintptr_t a, uintptr_t b) { bls12_sub(out, a, b); bls12_sub(out+48, a+48, b+48); }
static void bls12_Fp2_opp(uintptr_t out, uintptr_t a) { bls12_opp(out, a); bls12_opp(out+48, a+48); }
static void bls12_Fp2_mul(uintptr_t out, uintptr_t a, uintptr_t b) {
    uint64_t t0[6], t1[6], t2[6], t3[6];
    bls12_mul((uintptr_t)t0, a, b);
    bls12_mul((uintptr_t)t1, a+48, b+48);
    bls12_sub(out, (uintptr_t)t0, (uintptr_t)t1);
    bls12_add((uintptr_t)t2, a, a+48);
    bls12_add((uintptr_t)t3, b, b+48);
    bls12_mul(out+48, (uintptr_t)t2, (uintptr_t)t3);
    bls12_sub(out+48, out+48, (uintptr_t)t0);
    bls12_sub(out+48, out+48, (uintptr_t)t1);
}
static void bls12_Fp2_square(uintptr_t out, uintptr_t a) { bls12_Fp2_mul(out, a, a); }
static void bls12_Fp2_inv(uintptr_t out, uintptr_t a) {
    uint64_t t0[6], t1[6], t2[6];
    bls12_square((uintptr_t)t0, a);
    bls12_square((uintptr_t)t1, a+48);
    bls12_add((uintptr_t)t0, (uintptr_t)t0, (uintptr_t)t1);
    /* inv via Fermat — placeholder, just for benchmarking throughput */
    bls12_mul(out, a, (uintptr_t)t0);
    bls12_mul(out+48, a+48, (uintptr_t)t0);
}
static void bls12_opp(uintptr_t out, uintptr_t a) { bls12_sub(out, (uintptr_t)(uint64_t[]){0,0,0,0,0,0}, a); }
static void bls12_from_word(uintptr_t out, uintptr_t v) { memset((void*)out, 0, 48); *(uint64_t*)out = (uint64_t)v; }

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
    printf("%-35s %10.0f ns  (%d iters)\n", name, (_end - _start) / (iters), iters); \
} while(0)
#define BENCH_US(name, code, iters) do { \
    for (int _w = 0; _w < 5; _w++) { code; } \
    double _start = now_ns(); \
    for (int _i = 0; _i < (iters); _i++) { code; } \
    double _end = now_ns(); \
    printf("%-35s %10.1f us  (%d iters)\n", name, (_end - _start) / (iters) / 1000.0, iters); \
} while(0)

int main(void) {
    uint8_t a[576], b[576], c[576];
    memset(a, 0x11, 576); memset(b, 0x22, 576);

    printf("=== BLS12-381 tower (fiat-crypto C, no asm) ===\n");
    BENCH("Fp mul",       bls12_mul((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 2000000);
    BENCH("Fp sqr",       bls12_square((uintptr_t)c, (uintptr_t)a), 2000000);
    BENCH("Fp2 mul",      bls12_Fp2_mul((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 1000000);
    BENCH("Fp6 mul",      bls12_Fp6_mul((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 200000);
    BENCH("Fp12 mul",     bls12_Fp12_mul((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 100000);
    BENCH("Fp12 sqr",     bls12_Fp12_square((uintptr_t)c, (uintptr_t)a), 200000);

    /* Miller loop needs real curve points — use dummy data for throughput */
    uint8_t px[48], py[48], qx[96], qy[96], out[576];
    memset(px, 0x33, 48); memset(py, 0x44, 48);
    memset(qx, 0x55, 96); memset(qy, 0x66, 96);
    BENCH_US("Miller loop",  bls12_miller_loop((uintptr_t)out, (uintptr_t)px, (uintptr_t)py, (uintptr_t)qx, (uintptr_t)qy), 500);

    printf("\nNote: Miller loop uses dummy inputs (wrong result, valid timing).\n");
    return 0;
}
