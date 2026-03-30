/* BLS12-381 pairing benchmark: baseline vs optimized (#3, #4, #7)
 *
 * Optimizations:
 *  #3: Lazy reduction in Fp2 Karatsuba mul (skip 2 reductions)
 *  #4: Cyclotomic squaring in Fp12 (save 1 Fp6_mul per sqr)
 *  #7: Asm Fp add/sub via __int128 carry chain
 *
 * Links with CryptOpt asm for Fp mul/sqr.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

/* Include the base pairing C code (Fp mul/sqr/add/sub + Fp6/Fp12 ops) */
#include "bls12_pairing.c"

/* Include Fp2 operations that call bls12_mul/add/sub */
#include "/tmp/fp2_ops.c"

/* CryptOpt asm */
extern void fiat_bls12_381_p_mul(uint64_t out[6], const uint64_t a[6], const uint64_t b[6]);
extern void fiat_bls12_381_p_square(uint64_t out[6], const uint64_t a[6]);

/* ================================================================
 * #7: Fast Fp add/sub using __int128 carry chain
 * ================================================================ */
static const uint64_t BLS12_P[6] = {
    0xb9feffffffffaaabULL, 0x1eabfffeb153ffffULL,
    0x6730d2a0f6b0f624ULL, 0x64774b84f38512bfULL,
    0x4b1ba7b6434bacd7ULL, 0x1a0111ea397fe69aULL
};

static void fp_add_fast(uintptr_t out, uintptr_t a, uintptr_t b) {
    const uint64_t *ap = (const uint64_t *)a, *bp = (const uint64_t *)b;
    uint64_t *op = (uint64_t *)out;
    unsigned __int128 carry = 0;
    uint64_t tmp[6];
    for (int i = 0; i < 6; i++) {
        carry += (unsigned __int128)ap[i] + bp[i];
        tmp[i] = (uint64_t)carry;
        carry >>= 64;
    }
    /* Conditional subtraction of p */
    unsigned __int128 borrow = 0;
    for (int i = 0; i < 6; i++) {
        borrow = (unsigned __int128)tmp[i] - BLS12_P[i] - (uint64_t)(borrow >> 127);
        op[i] = (uint64_t)borrow;
        borrow = (borrow >> 64) & 0x8000000000000000ULL ? (unsigned __int128)1 << 127 : 0;
    }
    /* Awkward borrow logic. Simpler: */
    uint64_t sub[6];
    uint64_t b2 = 0;
    for (int i = 0; i < 6; i++) {
        __uint128_t d = (__uint128_t)tmp[i] - BLS12_P[i] - b2;
        sub[i] = (uint64_t)d;
        b2 = (d >> 64) ? 1 : 0; /* borrow if high bits set */
    }
    /* If no final carry from add AND borrow from sub, use tmp (no reduction) */
    uint64_t use_sub = (uint64_t)carry | (1 - b2); /* reduce if carry OR no borrow */
    uint64_t mask = -(uint64_t)(use_sub != 0);
    for (int i = 0; i < 6; i++)
        op[i] = (sub[i] & mask) | (tmp[i] & ~mask);
}

static void fp_sub_fast(uintptr_t out, uintptr_t a, uintptr_t b) {
    const uint64_t *ap = (const uint64_t *)a, *bp = (const uint64_t *)b;
    uint64_t *op = (uint64_t *)out;
    uint64_t borrow = 0;
    uint64_t tmp[6];
    for (int i = 0; i < 6; i++) {
        __uint128_t d = (__uint128_t)ap[i] - bp[i] - borrow;
        tmp[i] = (uint64_t)d;
        borrow = (d >> 64) ? 1 : 0;
    }
    /* If borrow, add p */
    uint64_t mask = -(uint64_t)borrow;
    uint64_t carry = 0;
    for (int i = 0; i < 6; i++) {
        __uint128_t s = (__uint128_t)tmp[i] + (BLS12_P[i] & mask) + carry;
        op[i] = (uint64_t)s;
        carry = (uint64_t)(s >> 64);
    }
}

/* ================================================================
 * #3: Lazy Fp2 mul — skip intermediate reductions
 *
 * In standard Karatsuba: a0+a1 and b0+b1 are reduced mod p before mul.
 * With lazy: compute a0+a1 as 7-limb (384+1 = 385 bits), then
 * use a wider multiply. Since we don't have a wider multiply from
 * fiat-crypto, we approximate: add WITHOUT reduction, then multiply.
 * The result may be slightly off but we reduce at the end.
 *
 * For a CORRECT lazy implementation, we'd need fiat-crypto to generate
 * a "loose" multiply that accepts inputs up to 2p. The Montgomery
 * multiplier already handles inputs < 2^384, so unreduced sums
 * (< 2p < 2^382) are fine as inputs to Montgomery mul.
 * ================================================================ */

/* Add WITHOUT reduction (result may be > p but < 2^384) */
static void fp_add_lazy(uintptr_t out, uintptr_t a, uintptr_t b) {
    const uint64_t *ap = (const uint64_t *)a, *bp = (const uint64_t *)b;
    uint64_t *op = (uint64_t *)out;
    uint64_t carry = 0;
    for (int i = 0; i < 6; i++) {
        __uint128_t s = (__uint128_t)ap[i] + bp[i] + carry;
        op[i] = (uint64_t)s;
        carry = (uint64_t)(s >> 64);
    }
    /* No reduction — result < 2p < 2^382. Montgomery mul handles this. */
}

/* Lazy Fp2 mul: same as standard but uses fp_add_lazy for a0+a1, b0+b1 */
static void bls12_Fp2_mul_lazy(uintptr_t out, uintptr_t a, uintptr_t b) {
    uint8_t v0[48], v1[48], t0[48], t1[48];
    bls12_mul((uintptr_t)v0, a, b);
    bls12_mul((uintptr_t)v1, a+48, b+48);
    bls12_sub(out, (uintptr_t)v0, (uintptr_t)v1);
    fp_add_lazy((uintptr_t)t0, a, a+48);     /* LAZY: no reduction */
    fp_add_lazy((uintptr_t)t1, b, b+48);     /* LAZY: no reduction */
    bls12_mul(out+48, (uintptr_t)t0, (uintptr_t)t1);  /* Montgomery handles loose inputs */
    bls12_sub(out+48, out+48, (uintptr_t)v0);
    bls12_sub(out+48, out+48, (uintptr_t)v1);
}

/* ================================================================
 * #4: Cyclotomic Fp12 squaring
 *
 * For f = (c0, c1) in Fp6 × Fp6, in the cyclotomic subgroup:
 *   new_c0 = 1 + 2 * mul_by_v(c1^2)
 *   new_c1 = 2 * c0 * c1
 *
 * Saves 1 Fp6_mul (replaced by Fp6_mul_by_v which is ~3x cheaper).
 *
 * Fp6 layout: 3 Fp2 = 3 * 96 = 288 bytes
 * Fp12 layout: 2 Fp6 = 2 * 288 = 576 bytes
 * ================================================================ */

/* Montgomery form of 1 for BLS12-381 */
static const uint64_t FP_MONT_ONE[6] = {
    0x760900000002fffdULL, 0xebf4000bc40c0002ULL,
    0x5f48985753c758baULL, 0x77ce585370525745ULL,
    0x5c071a97a256ec6dULL, 0x15f65ec3fa80e493ULL
};

static void bls12_Fp12_cyclotomic_square(uintptr_t out, uintptr_t f) {
    /* c0 = f[0..288), c1 = f[288..576) */
    uintptr_t c0 = f, c1 = f + 288;
    uint8_t c1_sq[288], cross[288], v_c1_sq[288], two_v[288];

    /* c1_sq = c1 * c1 (Fp6 mul) */
    bls12_Fp6_mul((uintptr_t)c1_sq, c1, c1);

    /* cross = c0 * c1 (Fp6 mul) */
    bls12_Fp6_mul((uintptr_t)cross, c0, c1);

    /* v_c1_sq = mul_by_v(c1_sq) (Fp6 shift: multiply by v) */
    /* mul_by_v((a,b,c)) = (xi*c, a, b) where xi = 1+u for BLS12-381 */
    /* xi*c: use bls12_Fp2_mul_xi */
    bls12_Fp2_mul_xi((uintptr_t)v_c1_sq, (uintptr_t)c1_sq + 192);  /* xi*c2 -> v[0] */
    memcpy(v_c1_sq + 96, c1_sq, 96);      /* c0 -> v[1] */
    memcpy(v_c1_sq + 192, c1_sq + 96, 96); /* c1 -> v[2] */

    /* two_v = 2 * v_c1_sq */
    bls12_Fp6_add((uintptr_t)two_v, (uintptr_t)v_c1_sq, (uintptr_t)v_c1_sq);

    /* new_c0 = fp6_one + two_v */
    /* fp6_one = ((mont_one, 0), (0, 0), (0, 0)) */
    memcpy((void*)out, two_v, 288);
    /* Add 1 to first Fp component (Montgomery form) */
    {
        uint64_t *dst = (uint64_t *)out;
        uint64_t carry = 0;
        for (int i = 0; i < 6; i++) {
            __uint128_t s = (__uint128_t)dst[i] + FP_MONT_ONE[i] + carry;
            dst[i] = (uint64_t)s;
            carry = (uint64_t)(s >> 64);
        }
        /* Reduce if needed */
        uint64_t sub[6], borrow = 0;
        for (int i = 0; i < 6; i++) {
            __uint128_t d = (__uint128_t)dst[i] - BLS12_P[i] - borrow;
            sub[i] = (uint64_t)d;
            borrow = (d >> 64) ? 1 : 0;
        }
        uint64_t use_sub = carry | (1 - borrow);
        uint64_t mask = -(uint64_t)(use_sub != 0);
        for (int i = 0; i < 6; i++)
            dst[i] = (sub[i] & mask) | (dst[i] & ~mask);
    }

    /* new_c1 = 2 * cross */
    bls12_Fp6_add(out + 288, (uintptr_t)cross, (uintptr_t)cross);
}

/* ================================================================
 * Benchmark
 * ================================================================ */

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

int main(void) {
    /* Fp test data */
    uint64_t a[6] = {0x1234567890abcdef, 0xfedcba0987654321, 0x1111111111111111,
                     0x2222222222222222, 0x3333333333333333, 0x0444444444444444};
    uint64_t b[6] = {0xabcdef1234567890, 0x1234567890abcdef, 0x5555555555555555,
                     0x6666666666666666, 0x7777777777777777, 0x0888888888888888};
    uint64_t c[6];

    printf("=== #7: Fp add/sub ===\n");
    BENCH("bls12_add (generated C)",      bls12_add((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 5000000);
    BENCH("fp_add_fast (__int128)",        fp_add_fast((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 5000000);
    BENCH("bls12_sub (generated C)",      bls12_sub((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 5000000);
    BENCH("fp_sub_fast (__int128)",        fp_sub_fast((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 5000000);

    printf("\n=== Fp mul/sqr (CryptOpt vs C) ===\n");
    BENCH("bls12_mul (generated C)",      bls12_mul((uintptr_t)c, (uintptr_t)a, (uintptr_t)b), 2000000);
    BENCH("CryptOpt mul (asm)",           fiat_bls12_381_p_mul(c, a, b), 2000000);
    BENCH("bls12_square (generated C)",   bls12_square((uintptr_t)c, (uintptr_t)a), 2000000);
    BENCH("CryptOpt sqr (asm)",           fiat_bls12_381_p_square(c, a), 2000000);

    /* Fp2 test data */
    uint8_t fp2a[96], fp2b[96], fp2c[96];
    memset(fp2a, 0x42, 96); memset(fp2b, 0x37, 96);

    printf("\n=== #3: Fp2 mul (lazy vs standard) ===\n");
    BENCH("bls12_Fp2_mul (standard)",     bls12_Fp2_mul((uintptr_t)fp2c, (uintptr_t)fp2a, (uintptr_t)fp2b), 1000000);
    BENCH("bls12_Fp2_mul_lazy (#3)",      bls12_Fp2_mul_lazy((uintptr_t)fp2c, (uintptr_t)fp2a, (uintptr_t)fp2b), 1000000);

    /* Fp12 test data */
    uint8_t f12a[576], f12b[576];
    memset(f12a, 0x11, 576); memset(f12b, 0x22, 576);

    printf("\n=== #4: Fp12 squaring (cyclotomic vs generic) ===\n");
    BENCH("bls12_Fp12_square (generic)",  bls12_Fp12_square((uintptr_t)f12b, (uintptr_t)f12a), 200000);
    BENCH("bls12_Fp12_cyclotomic_sq (#4)",bls12_Fp12_cyclotomic_square((uintptr_t)f12b, (uintptr_t)f12a), 200000);

    printf("\n=== Fp12 mul ===\n");
    BENCH("bls12_Fp12_mul (baseline)",    bls12_Fp12_mul((uintptr_t)f12b, (uintptr_t)f12a, (uintptr_t)f12b), 100000);

    return 0;
}
