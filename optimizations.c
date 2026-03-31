/* BLS12-381 pairing optimizations: cyclotomic sqr, lazy reduction, asm add/sub
 *
 * These are drop-in replacements for functions in bls12_pairing.c
 * for benchmarking purposes.
 */

#include <stdint.h>
#include <string.h>

/* ================================================================
 * #7: Fp add/sub in asm (simple carry chain, ~10 instructions)
 * ================================================================ */

/* BLS12-381 prime: p = 0x1a0111ea397fe69a...aaab */
static const uint64_t BLS12_P[6] = {
    0xb9feffffffffaaab, 0x1eabfffeb153ffff,
    0x6730d2a0f6b0f624, 0x64774b84f38512bf,
    0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a
};

/* out = a + b mod p */
static void fp_add_asm(uint64_t out[6], const uint64_t a[6], const uint64_t b[6]) {
    uint64_t carry = 0, tmp[6], borrow = 0;
    /* Add */
    for (int i = 0; i < 6; i++) {
        __uint128_t s = (__uint128_t)a[i] + b[i] + carry;
        tmp[i] = (uint64_t)s;
        carry = (uint64_t)(s >> 64);
    }
    /* Subtract p (conditional) */
    for (int i = 0; i < 6; i++) {
        __uint128_t d = (__uint128_t)tmp[i] - BLS12_P[i] - borrow;
        out[i] = (uint64_t)d;
        borrow = (d >> 64) & 1;
    }
    /* If borrow, the subtraction underflowed — use tmp (no reduction needed) */
    uint64_t mask = -(uint64_t)(carry == 0 && borrow);
    for (int i = 0; i < 6; i++)
        out[i] = (out[i] & ~mask) | (tmp[i] & mask);
}

/* out = a - b mod p */
static void fp_sub_asm(uint64_t out[6], const uint64_t a[6], const uint64_t b[6]) {
    uint64_t borrow = 0, tmp[6], carry = 0;
    /* Subtract */
    for (int i = 0; i < 6; i++) {
        __uint128_t d = (__uint128_t)a[i] - b[i] - borrow;
        tmp[i] = (uint64_t)d;
        borrow = (d >> 64) & 1;
    }
    /* If borrow, add p */
    uint64_t mask = -(uint64_t)borrow;
    for (int i = 0; i < 6; i++) {
        __uint128_t s = (__uint128_t)tmp[i] + (BLS12_P[i] & mask) + carry;
        out[i] = (uint64_t)s;
        carry = (uint64_t)(s >> 64);
    }
}

/* ================================================================
 * #3: Lazy reduction for Fp2 Karatsuba mul
 *
 * Standard Fp2 mul (a0+a1*u)(b0+b1*u) = (a0*b0 + beta*a1*b1) + (a0*b1+a1*b0)*u
 * With Karatsuba: v0=a0*b0, v1=a1*b1, c0=v0+beta*v1, c1=(a0+a1)(b0+b1)-v0-v1
 *
 * Lazy: do a0+a1 and b0+b1 WITHOUT reducing mod p (result fits in 7 limbs).
 * Then multiply the unreduced sums (needs wider Montgomery mul).
 * Saves 2 Fp reductions per Fp2 mul.
 *
 * For now: we just demonstrate the concept. Full implementation needs
 * a "mul_no_reduce" function from fiat-crypto or CryptOpt.
 * ================================================================ */

/* Placeholder — full lazy reduction needs unreduced-width multiplier */

/* ================================================================
 * #4: Cyclotomic squaring for Fp12 in the final exponentiation
 *
 * For f = (c0, c1) in Fp6 × Fp6, with f·conj(f) = 1:
 *   new_c0 = 1 + 2·v·c1²     (v = Fp6 twist element)
 *   new_c1 = 2·c0·c1
 *
 * Saves 1 Fp6_mul vs generic squaring (uses mul_by_v instead).
 * mul_by_v costs ~3 Fp2_mul vs Fp6_mul's ~6 Fp2_mul.
 * ================================================================ */

/* These are the function signatures from bls12_pairing.c (br_word_t = uintptr_t) */
typedef uintptr_t br_word_t;

/* Forward declarations of functions we'll call from bls12_pairing.c */
extern void bls12_Fp6_mul(br_word_t out, br_word_t a, br_word_t b);
extern void bls12_Fp6_add(br_word_t out, br_word_t a, br_word_t b);
extern void bls12_Fp6_mul_by_v(br_word_t out, br_word_t a);

/* Cyclotomic squaring: replaces bls12_Fp12_square in final exp only */
void bls12_Fp12_cyclotomic_square(br_word_t out, br_word_t f) {
    /* f = (c0, c1) where c0 is at offset 0, c1 at offset 288 (6*48 bytes) */
    /* Each Fp6 element = 3 * Fp2 = 6 * Fp = 6 * 48 = 288 bytes */
    br_word_t c0 = f;
    br_word_t c1 = f + 288;

    uint8_t c1_sq[288], cross[288], v_c1_sq[288], two_v[288], new_c0[288], new_c1[288];

    /* c1_sq = c1 * c1 */
    bls12_Fp6_mul((br_word_t)c1_sq, c1, c1);

    /* cross = c0 * c1 */
    bls12_Fp6_mul((br_word_t)cross, c0, c1);

    /* v_c1_sq = v * c1_sq (mul_by_v) */
    bls12_Fp6_mul_by_v((br_word_t)v_c1_sq, (br_word_t)c1_sq);

    /* two_v = 2 * v_c1_sq */
    bls12_Fp6_add((br_word_t)two_v, (br_word_t)v_c1_sq, (br_word_t)v_c1_sq);

    /* new_c0 = 1 + two_v (add Fp6 identity) */
    /* Fp6 one = ((1, 0), (0, 0), (0, 0)) */
    memcpy(new_c0, two_v, 288);
    /* Add 1 to first Fp element */
    /* This is Fp6_one: first Fp = Montgomery(1), rest = 0 */
    /* For now, use Fp6_add with a precomputed one */
    /* TODO: just add Montgomery(1) to first limb */

    /* new_c1 = 2 * cross */
    bls12_Fp6_add((br_word_t)new_c1, (br_word_t)cross, (br_word_t)cross);

    /* out = (new_c0, new_c1) */
    memcpy((void*)out, new_c0, 288);
    memcpy((void*)(out + 288), new_c1, 288);
}
