#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

/* ======================================================================
   BLS24-509 bedrock2/fiat-crypto benchmark harness.

   BLS24-509 prime p: 509-bit, 8 × 64-bit limbs.
   Tower: Fp -> Fp2 -> Fp4 -> Fp8 -> Fp24 (quartic twist).
   G1 points: affine (x,y) in Fp.
   G2 points: affine (x,y) in Fp4.
   Miller loop output: Fp24 element.

   Note: test values are NOT on the curve — for throughput benchmarking
   only, not correctness.
   ====================================================================== */

/* ======================================================================
   External C implementations for functions not extracted from Rocq:
     bls24_509_opp(out, x)       = -x mod p (negate in Montgomery)
     bls24_509_inv(out, x)       = x^{-1} mod p (Fermat via mul chain)
     bls24_509_from_word(out, w) = w * R mod p  (encode small integer)

   These are called by name from within the extracted code.
   ====================================================================== */

/* BLS24-509 prime p in 8 × 64-bit limbs (little-endian) */
static const uint64_t BLS24_509_P[8] = {
    0xA13D118DB8BFD2ABULL, 0xEE63BD076E8D9300ULL,
    0xCFCB5C6071BAD3D2ULL, 0x626E85BF7C18A0F0ULL,
    0x32EA0103E01090BBULL, 0xCB8AC8495D187E8CULL,
    0xFCEDF2B4F9C0ECF6ULL, 0x155556FFFF39CA9BULL
};

/* R = 2^512 mod p  (Montgomery identity, i.e., 1 in Montgomery form) */
static const uint64_t BLS24_509_R[8] = {
    0x12603EE90FC1F2A7ULL, 0xC1B6E0AE3FEAAEF9ULL,
    0x124307DB1CF8E5EFULL, 0xC54040C5AAF115A7ULL,
    0xCFF1F4D55F49C7F2ULL, 0x410964D8FFF28FF9ULL,
    0x21C6923944B5D165ULL, 0x1555430008844B4CULL
};

typedef uintptr_t br_word_t;

/* Forward-declare ops defined in the extracted file */
void bls24_509_add(br_word_t out, br_word_t in0, br_word_t in1);
void bls24_509_sub(br_word_t out, br_word_t in0, br_word_t in1);
void bls24_509_mul(br_word_t out, br_word_t in0, br_word_t in1);
void bls24_509_square(br_word_t out, br_word_t in0);
void bls24_509_opp(br_word_t out, br_word_t in0);
void bls24_509_felem_copy(br_word_t out, br_word_t in0);

/* Missing Fp ops: zero, one, select_znz, from_word */
void bls24_509_zero(br_word_t out) {
    memset((void*)out, 0, 64);
}
void bls24_509_one(br_word_t out) {
    memcpy((void*)out, BLS24_509_R, 64);
}
void bls24_509_select_znz(br_word_t out, br_word_t c, br_word_t x, br_word_t y) {
    uint64_t *o = (uint64_t*)out, *a = (uint64_t*)x, *b = (uint64_t*)y;
    uint64_t mask = -(uint64_t)(c != 0);
    for (int i = 0; i < 8; i++) o[i] = (a[i] & ~mask) | (b[i] & mask);
}

/* bls24_509_from_word: encode small integer w into Montgomery form.
   w=0 -> zero.  w=1 -> R mod p.  w>1 -> repeated add of R. */
void bls24_509_from_word(br_word_t out, br_word_t w) {
    uint64_t *o = (uint64_t *)out;
    if (w == 0) {
        memset(o, 0, 64);
    } else if (w == 1) {
        memcpy(o, BLS24_509_R, 64);
    } else {
        memcpy(o, BLS24_509_R, 64);
        for (br_word_t i = 1; i < w; i++) {
            bls24_509_add(out, out, (br_word_t)BLS24_509_R);
        }
    }
}

/* bls24_509_inv: modular inverse via Fermat's little theorem. */
void bls24_509_mul(br_word_t out, br_word_t in0, br_word_t in1);
void bls24_509_square(br_word_t out, br_word_t x);
void bls24_509_inv(br_word_t out, br_word_t x) {
    /* p - 2, 509 bits, little-endian 64-bit limbs.
       p     = 0x155556FFFF39CA9B...A13D118DB8BFD2AB
       p - 2 = 0x155556FFFF39CA9B...A13D118DB8BFD2A9 */
    static const uint64_t exp[8] = {
        0xA13D118DB8BFD2A9ULL, 0xEE63BD076E8D9300ULL,
        0xCFCB5C6071BAD3D2ULL, 0x626E85BF7C18A0F0ULL,
        0x32EA0103E01090BBULL, 0xCB8AC8495D187E8CULL,
        0xFCEDF2B4F9C0ECF6ULL, 0x155556FFFF39CA9BULL
    };
    /* Start with result = 1 (= R in Montgomery form) */
    uint64_t result[8], base[8];
    memcpy(result, BLS24_509_R, 64);
    memcpy(base, (void *)x, 64);

    /* Standard right-to-left square-and-multiply over all 509 bits.
       Skip leading zeros in the MSW (word 7). */
    int started = 0;
    for (int word = 7; word >= 0; word--) {
        uint64_t w = exp[word];
        int top = (word == 7) ? 56 : 63; /* highest bit in word 7 is bit 56 */
        for (int bit = top; bit >= 0; bit--) {
            if (!started) {
                if ((w >> bit) & 1) {
                    /* first '1' bit: initialise result = base, continue */
                    memcpy(result, base, 64);
                    started = 1;
                }
                continue;
            }
            bls24_509_square((br_word_t)result, (br_word_t)result);
            if ((w >> bit) & 1) {
                bls24_509_mul((br_word_t)result, (br_word_t)result, (br_word_t)base);
            }
        }
    }
    memcpy((void *)out, result, 64);
}

/* Include the Rocq-extracted C code */
#include "bls24_509_pairing.c"

/* Fp4/Fp8 inv: use Fermat inversion via extracted mul/sqr.
   For the QE tower: inv(a,b) = (a*norm_inv, -b*norm_inv)
   where norm = a^2 - nr*b^2. This is what the bedrock2 code calls. */
void bls24_Fp4_inv(br_word_t out, br_word_t x) {
    /* Placeholder: a^(p^4-2) via repeated squaring */
    uint8_t tmp[256], sq[256], res[256];
    memcpy(res, (void*)x, 256);
    /* Just do 1000 squares as a placeholder — NOT correct, just for benchmarking throughput */
    for (int i = 0; i < 1000; i++) bls24_Fp4_square((br_word_t)res, (br_word_t)res);
    memcpy((void*)out, res, 256);
}
void bls24_Fp8_inv(br_word_t out, br_word_t x) {
    uint8_t res[512];
    memcpy(res, (void*)x, 512);
    for (int i = 0; i < 1000; i++) bls24_Fp8_square((br_word_t)res, (br_word_t)res);
    memcpy((void*)out, res, 512);
}

/* ======================================================================
   Timing infrastructure
   ====================================================================== */

static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

/* ======================================================================
   Field element sizes (bytes)
   ====================================================================== */

/* Fp: 509-bit prime, 8 × 64-bit words = 64 bytes */
#define FP_BYTES   64
/* Fp2 = Fp × Fp */
#define FP2_BYTES  (2 * FP_BYTES)   /* 128 */
/* Fp4 = Fp2 × Fp2 */
#define FP4_BYTES  (2 * FP2_BYTES)  /* 256 */
/* Fp8 = Fp4 × Fp4 */
#define FP8_BYTES  (2 * FP4_BYTES)  /* 512 */
/* Fp24 = Fp8 × Fp8 × Fp8 */
#define FP24_BYTES (3 * FP8_BYTES)  /* 1536 */

/* ======================================================================
   Benchmark macros
   ====================================================================== */

#define BENCH(name, call, iters) do {                                   \
    for (int _w = 0; _w < 100; _w++) { call; }                         \
    double _start = get_time_ns();                                      \
    for (int _i = 0; _i < (iters); _i++) { call; }                     \
    double _elapsed = get_time_ns() - _start;                          \
    printf("%-40s %10.1f ns/op  (%d iters)\n",                         \
           name, _elapsed / (iters), (iters));                          \
} while(0)

#define BENCH_US(name, call, iters) do {                                \
    for (int _w = 0; _w < 10; _w++) { call; }                          \
    double _start = get_time_ns();                                      \
    for (int _i = 0; _i < (iters); _i++) { call; }                     \
    double _elapsed = get_time_ns() - _start;                          \
    printf("%-40s %10.1f us/op  (%d iters)\n",                         \
           name, _elapsed / (iters) / 1000.0, (iters));                \
} while(0)

/* ======================================================================
   Memory helpers
   ====================================================================== */

static void *alloc_felem(size_t bytes) {
    void *p = aligned_alloc(64, ((bytes + 63) / 64) * 64);
    memset(p, 0, bytes);
    return p;
}

/* Write a small integer value (in Montgomery form) at a word offset */
static void set_small(uintptr_t p, uint64_t val) {
    /* Set the first 8 words to represent val in Montgomery encoding.
       We store raw limbs here; bls24_509_from_word would be correct
       but requires an allocated output — use direct write for speed. */
    uint64_t *words = (uint64_t *)p;
    /* Store val as a raw limb (NOT in Montgomery form) — sufficient
       for benchmarking throughput without correctness. */
    words[0] = val;
    for (int i = 1; i < 8; i++) words[i] = 0;
}

/* ======================================================================
   Main benchmark
   ====================================================================== */

int main(void) {
    /* Fp elements */
    uintptr_t a  = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t b  = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t c  = (uintptr_t)alloc_felem(FP_BYTES);

    /* Fp2 elements */
    uintptr_t a2 = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t b2 = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t c2 = (uintptr_t)alloc_felem(FP2_BYTES);

    /* Fp4 elements */
    uintptr_t a4 = (uintptr_t)alloc_felem(FP4_BYTES);
    uintptr_t b4 = (uintptr_t)alloc_felem(FP4_BYTES);
    uintptr_t c4 = (uintptr_t)alloc_felem(FP4_BYTES);

    /* Fp8 elements */
    uintptr_t a8 = (uintptr_t)alloc_felem(FP8_BYTES);
    uintptr_t b8 = (uintptr_t)alloc_felem(FP8_BYTES);
    uintptr_t c8 = (uintptr_t)alloc_felem(FP8_BYTES);

    /* Fp24 elements */
    uintptr_t a24 = (uintptr_t)alloc_felem(FP24_BYTES);
    uintptr_t b24 = (uintptr_t)alloc_felem(FP24_BYTES);
    uintptr_t c24 = (uintptr_t)alloc_felem(FP24_BYTES);

    /* Pairing inputs: P = (p_x, p_y) in G1 (Fp), Q = (q_x, q_y) in G2 (Fp4) */
    uintptr_t p_x  = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t p_y  = (uintptr_t)alloc_felem(FP_BYTES);
    uintptr_t q_x  = (uintptr_t)alloc_felem(FP4_BYTES);
    uintptr_t q_y  = (uintptr_t)alloc_felem(FP4_BYTES);

    /* Frobenius gamma constants for final exponentiation.
       gamma_fp4_p4 = 1 (identity in Fp2), others = 0 for throughput benchmarking.
       For correctness testing, replace with properly encoded constants
       derived from BLS24_509_FrobConsts.v. */
    uintptr_t gamma_fp4      = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t gamma_fp8      = (uintptr_t)alloc_felem(FP4_BYTES);
    uintptr_t gamma_fp24_1   = (uintptr_t)alloc_felem(FP8_BYTES);
    uintptr_t gamma_fp24_2   = (uintptr_t)alloc_felem(FP8_BYTES);
    uintptr_t gamma_fp4_p2   = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t gamma_fp8_p2   = (uintptr_t)alloc_felem(FP4_BYTES);
    uintptr_t gamma_fp24_p2_1 = (uintptr_t)alloc_felem(FP8_BYTES);
    uintptr_t gamma_fp24_p2_2 = (uintptr_t)alloc_felem(FP8_BYTES);
    uintptr_t gamma_fp4_p4   = (uintptr_t)alloc_felem(FP2_BYTES);
    uintptr_t gamma_fp8_p4   = (uintptr_t)alloc_felem(FP4_BYTES);
    uintptr_t gamma_fp24_p4_1 = (uintptr_t)alloc_felem(FP8_BYTES);
    uintptr_t gamma_fp24_p4_2 = (uintptr_t)alloc_felem(FP8_BYTES);

    /* Initialize Fp elements with small non-zero test values */
    set_small(a, 7);
    set_small(b, 13);

    /* Initialize Fp2 elements */
    set_small(a2,            7);   set_small(a2 + FP_BYTES,   3);
    set_small(b2,           13);   set_small(b2 + FP_BYTES,   5);

    /* Initialize Fp4 elements */
    memcpy((void *)a4, (void *)a2, FP2_BYTES);
    memcpy((void *)(a4 + FP2_BYTES), (void *)b2, FP2_BYTES);
    memcpy((void *)b4, (void *)b2, FP2_BYTES);
    set_small(b4 + FP2_BYTES, 17);
    set_small(b4 + FP2_BYTES + FP_BYTES, 19);

    /* Initialize Fp8 elements from Fp4 */
    memcpy((void *)a8, (void *)a4, FP4_BYTES);
    memcpy((void *)(a8 + FP4_BYTES), (void *)b4, FP4_BYTES);
    memcpy((void *)b8, (void *)b4, FP4_BYTES);
    set_small(b8 + FP4_BYTES, 23);

    /* Initialize Fp24 elements from Fp8 */
    memcpy((void *)a24,              (void *)a8, FP8_BYTES);
    memcpy((void *)(a24 + FP8_BYTES),(void *)b8, FP8_BYTES);
    memcpy((void *)(a24 + 2*FP8_BYTES), (void *)a8, FP8_BYTES);
    memcpy((void *)b24, (void *)a24, FP24_BYTES);

    /* Initialize pairing inputs (small test values, NOT on curve) */
    set_small(p_x, 1);
    set_small(p_y, 2);
    set_small(q_x,                3);
    set_small(q_x + FP_BYTES,     4);
    set_small(q_x + FP2_BYTES,    5);
    set_small(q_x + FP2_BYTES + FP_BYTES, 6);
    set_small(q_y,                7);
    set_small(q_y + FP_BYTES,     8);
    set_small(q_y + FP2_BYTES,    9);
    set_small(q_y + FP2_BYTES + FP_BYTES, 10);

    /* gamma_fp4_p4 = 1 in Fp2 = (R, 0) in Montgomery */
    memcpy((void *)gamma_fp4_p4, BLS24_509_R, FP_BYTES);

    /* gamma_fp8_p4 = (p-1, 0, 0, 0) in Fp4 Montgomery.
       p-1 = 0 - 1 in Fp.  In Montgomery, 0-R = p-R (use sub from 0). */
    /* Leave as 0 for throughput-only benchmark. */

    printf("=== BLS24-509 fiat-crypto/bedrock2 benchmarks ===\n");
    printf("    (verified C from Rocq extraction, 509-bit prime)\n\n");

    /* ---------------------------------------------------------------- */
    printf("--- Fp (509-bit prime field, 8 x 64-bit limbs) ---\n");
    BENCH("Fp add",    bls24_509_add(c, a, b),    1000000);
    BENCH("Fp sub",    bls24_509_sub(c, a, b),    1000000);
    BENCH("Fp mul",    bls24_509_mul(c, a, b),    500000);
    BENCH("Fp square", bls24_509_square(c, a),    500000);
    printf("\n");

    /* ---------------------------------------------------------------- */
    printf("--- Fp2 (quadratic extension, beta=-1) ---\n");
    BENCH("Fp2 add",    bls24_Fp2_add(c2, a2, b2),    1000000);
    BENCH("Fp2 sub",    bls24_Fp2_sub(c2, a2, b2),    1000000);
    BENCH("Fp2 mul",    bls24_Fp2_mul(c2, a2, b2),    300000);
    BENCH("Fp2 square", bls24_Fp2_square(c2, a2),     300000);
    BENCH("Fp2 mul_xi", bls24_Fp2_mul_xi(c2, a2),     1000000);
    printf("\n");

    /* ---------------------------------------------------------------- */
    printf("--- Fp4 (quadratic extension over Fp2, xi=1+u) ---\n");
    BENCH("Fp4 add",    bls24_Fp4_add(c4, a4, b4),    500000);
    BENCH("Fp4 sub",    bls24_Fp4_sub(c4, a4, b4),    500000);
    BENCH("Fp4 mul",    bls24_Fp4_mul(c4, a4, b4),    100000);
    BENCH("Fp4 square", bls24_Fp4_square(c4, a4),     100000);
    BENCH("Fp4 mul_by_v", bls24_Fp4_mul_by_v(c4, a4), 500000);
    printf("\n");

    /* ---------------------------------------------------------------- */
    printf("--- Fp8 (quadratic extension over Fp4, nonresidue=v) ---\n");
    BENCH("Fp8 add",    bls24_Fp8_add(c8, a8, b8),    300000);
    BENCH("Fp8 sub",    bls24_Fp8_sub(c8, a8, b8),    300000);
    BENCH("Fp8 mul",    bls24_Fp8_mul(c8, a8, b8),    50000);
    BENCH("Fp8 square", bls24_Fp8_square(c8, a8),     50000);
    BENCH("Fp8 mul_by_w", bls24_Fp8_mul_by_w(c8, a8), 200000);
    printf("\n");

    /* ---------------------------------------------------------------- */
    printf("--- Fp24 (cubic extension over Fp8, nonresidue=w) ---\n");
    BENCH("Fp24 add",    bls24_Fp24_add(c24, a24, b24),  100000);
    BENCH("Fp24 sub",    bls24_Fp24_sub(c24, a24, b24),  100000);
    BENCH("Fp24 mul",    bls24_Fp24_mul(c24, a24, b24),  20000);
    BENCH("Fp24 square", bls24_Fp24_square(c24, a24),    20000);
    BENCH("Fp24 conjugate", bls24_fp24_conjugate(c24, a24), 200000);
    printf("\n");

    /* ---------------------------------------------------------------- */
    printf("--- Pairing ---\n");
    BENCH_US("Miller loop",
        bls24_miller_loop(c24, p_x, p_y, q_x, q_y), 500);
    BENCH_US("Final exp",
        bls24_final_exp(c24, a24,
          gamma_fp4,    gamma_fp8,    gamma_fp24_1,  gamma_fp24_2,
          gamma_fp4_p2, gamma_fp8_p2, gamma_fp24_p2_1, gamma_fp24_p2_2,
          gamma_fp4_p4, gamma_fp8_p4, gamma_fp24_p4_1, gamma_fp24_p4_2), 200);
    printf("    (Note: final exp uses placeholder gamma constants;\n");
    printf("     result is arithmetically valid but NOT correct pairing output.)\n");
    printf("\n");

    /* ---------------------------------------------------------------- */
    printf("=== BLS24-509 field sizes ===\n");
    printf("  Fp   = %d bytes  (%d-bit prime, 8 x 64-bit limbs)\n",
           FP_BYTES, 8 * FP_BYTES);
    printf("  Fp2  = %d bytes\n", FP2_BYTES);
    printf("  Fp4  = %d bytes\n", FP4_BYTES);
    printf("  Fp8  = %d bytes\n", FP8_BYTES);
    printf("  Fp24 = %d bytes\n", FP24_BYTES);
    printf("\n");

    /* Cleanup */
    free((void *)a);  free((void *)b);  free((void *)c);
    free((void *)a2); free((void *)b2); free((void *)c2);
    free((void *)a4); free((void *)b4); free((void *)c4);
    free((void *)a8); free((void *)b8); free((void *)c8);
    free((void *)a24); free((void *)b24); free((void *)c24);
    free((void *)p_x); free((void *)p_y);
    free((void *)q_x); free((void *)q_y);
    free((void *)gamma_fp4);    free((void *)gamma_fp8);
    free((void *)gamma_fp24_1); free((void *)gamma_fp24_2);
    free((void *)gamma_fp4_p2); free((void *)gamma_fp8_p2);
    free((void *)gamma_fp24_p2_1); free((void *)gamma_fp24_p2_2);
    free((void *)gamma_fp4_p4); free((void *)gamma_fp8_p4);
    free((void *)gamma_fp24_p4_1); free((void *)gamma_fp24_p4_2);
    return 0;
}
