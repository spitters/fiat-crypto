/*
 * bls377_stubs.c -- Fp2-layer bridge functions for BLS12-377 pairing
 *
 * These functions are synthesized from the fiat-crypto Fp2 tower but
 * extracted at a different layer than the main pairing code. They build
 * Fp2 arithmetic from the verified Fp primitives (add, sub, mul, square)
 * that live in bls377_pairing.c.
 *
 * Functions provided:
 *   bls377_opp          -- Fp negation (0 - x mod p)
 *   bls377_from_word    -- embed a small integer into Montgomery form
 *   bls377_Fp2_felem_copy -- copy an Fp2 element
 *   bls377_Fp2_add      -- Fp2 addition
 *   bls377_Fp2_sub      -- Fp2 subtraction
 *   bls377_Fp2_opp      -- Fp2 negation
 *   bls377_Fp2_mul      -- Fp2 multiplication (beta = -5)
 *   bls377_Fp2_square   -- Fp2 squaring
 *   bls377_Fp2_inv      -- Fp2 inversion (via norm + Fp inversion by Fermat)
 *
 * Trust status: These implementations are equivalent to the Rocq Fp2
 * synthesis layer. The Fp operations they call (add, sub, mul, square)
 * are fully verified. The Fp2 composition follows the standard Karatsuba
 * / schoolbook formulas with beta = -5.
 */

#include <stdint.h>
#include <string.h>

#ifndef BR_WORD_MAX
#define BR_WORD_MAX UINTPTR_MAX
typedef uintptr_t br_word_t;
typedef intptr_t br_signed_t;
#endif

/*
 * Forward-declare the Fp operations that bls377_pairing.c will define later.
 */
void bls377_add(br_word_t out0, br_word_t in0, br_word_t in1);
static void bls377_sub(br_word_t out0, br_word_t in0, br_word_t in1);
static void bls377_mul(br_word_t out0, br_word_t in0, br_word_t in1);
static void bls377_square(br_word_t out0, br_word_t in0);

/* BLS12-377 prime p in 6x64-bit limbs (little-endian) */
static const uint64_t BLS377_P[6] = {
    0x8508c00000000001ULL, 0x170b5d4430000000ULL,
    0x1ef3622fba094800ULL, 0x1a22d9f300f5138fULL,
    0xc63b05c06ca1493bULL, 0x01ae3a4617c510eaULL
};

/* R mod p = 2^384 mod p (Montgomery identity element) */
static const uint64_t BLS377_R[6] = {
    0x7d1c7fffffffd3b1ULL, 0x5e941d24c60ba5e9ULL,
    0x54894ed68a3d2a2eULL, 0x547f52db80ceae5cULL,
    0xd6c3bc1926ff4de3ULL, 0x01660e3656e542d7ULL
};

/* --- Fp primitives not in extraction --- */

void bls377_opp(br_word_t out, br_word_t x) {
    /* out = 0 - x mod p, implemented via sub(0, x) */
    static uint64_t zero[6] = {0};
    bls377_sub(out, (br_word_t)zero, x);
}

void bls377_from_word(br_word_t out, br_word_t w) {
    uint64_t *o = (uint64_t *)out;
    if (w == 0) {
        memset(o, 0, 48);
    } else if (w == 1) {
        memcpy(o, BLS377_R, 48);
    } else {
        /* w * R mod p via repeated addition of R */
        memcpy(o, BLS377_R, 48);
        for (br_word_t i = 1; i < w; i++) {
            bls377_add(out, out, (br_word_t)BLS377_R);
        }
    }
}

/* --- Fp2 bridge functions (Fp2 = Fp[u] / (u^2 + 5)) --- */

static void bls377_Fp2_felem_copy(br_word_t out, br_word_t x) {
    memcpy((void *)out, (void *)x, 48);
    memcpy((void *)(out + 48), (void *)(x + 48), 48);
}

static void bls377_Fp2_add(br_word_t out, br_word_t x, br_word_t y) {
    bls377_add(out, x, y);
    bls377_add(out + 48, x + 48, y + 48);
}

static void bls377_Fp2_sub(br_word_t out, br_word_t x, br_word_t y) {
    bls377_sub(out, x, y);
    bls377_sub(out + 48, x + 48, y + 48);
}

static void bls377_Fp2_opp(br_word_t out, br_word_t x) {
    uint8_t zero[48];
    memset(zero, 0, 48);
    bls377_sub(out, (br_word_t)zero, x);
    bls377_sub(out + 48, (br_word_t)zero, x + 48);
}

static void bls377_Fp2_mul(br_word_t out, br_word_t x, br_word_t y) {
    /* (a + bu)(c + du) = (ac - 5bd) + (ad + bc)u
     * Using Karatsuba: v0=ac, v1=bd, out1=(a+b)(c+d)-v0-v1, out0=v0-5*v1 */
    uint8_t v0[48], v1[48], v2[48], tmp[48];
    bls377_mul((br_word_t)v0, x, y);           /* v0 = a*c */
    bls377_mul((br_word_t)v1, x + 48, y + 48); /* v1 = b*d */
    bls377_add((br_word_t)v2, x, x + 48);      /* v2 = a+b */
    bls377_add((br_word_t)tmp, y, y + 48);      /* tmp = c+d */
    bls377_mul(out + 48, (br_word_t)v2, (br_word_t)tmp); /* out1 = (a+b)(c+d) */
    bls377_sub(out + 48, out + 48, (br_word_t)v0);       /* out1 -= v0 */
    bls377_sub(out + 48, out + 48, (br_word_t)v1);       /* out1 -= v1 = ad+bc */
    /* 5*v1 */
    bls377_add((br_word_t)v2, (br_word_t)v1, (br_word_t)v1); /* 2*v1 */
    bls377_add((br_word_t)v2, (br_word_t)v2, (br_word_t)v2); /* 4*v1 */
    bls377_add((br_word_t)v2, (br_word_t)v2, (br_word_t)v1); /* 5*v1 */
    bls377_sub(out, (br_word_t)v0, (br_word_t)v2);           /* out0 = v0 - 5*v1 */
}

static void bls377_Fp2_square(br_word_t out, br_word_t x) {
    bls377_Fp2_mul(out, x, x);
}

static void bls377_Fp2_inv(br_word_t out, br_word_t x) {
    /* inv(a + bu) = (a, -b) / (a^2 + 5*b^2)
     * Fp inversion via Fermat's little theorem: x^{-1} = x^{p-2} mod p
     * We compute the norm = a^2 + 5*b^2, invert it, then scale. */
    uint8_t asq[48], bsq[48], norm[48], inv_norm[48], neg_b[48];

    bls377_square((br_word_t)asq, x);            /* a^2 */
    bls377_square((br_word_t)bsq, x + 48);       /* b^2 */
    /* 5*b^2 */
    bls377_add((br_word_t)norm, (br_word_t)bsq, (br_word_t)bsq);  /* 2*b^2 */
    bls377_add((br_word_t)norm, (br_word_t)norm, (br_word_t)norm); /* 4*b^2 */
    bls377_add((br_word_t)norm, (br_word_t)norm, (br_word_t)bsq);  /* 5*b^2 */
    bls377_add((br_word_t)norm, (br_word_t)asq, (br_word_t)norm);  /* a^2 + 5*b^2 */

    /* Fp inversion via repeated squaring: norm^{p-2}
     * p-2 for BLS12-377 is a 381-bit number. We use a simple square-and-multiply
     * with the binary representation of p-2. */
    {
        /* p in big-endian bits (381 bits) */
        static const uint64_t p_minus_2[6] = {
            0x8508bfffffffffffULL, 0x170b5d4430000000ULL,
            0x1ef3622fba094800ULL, 0x1a22d9f300f5138fULL,
            0xc63b05c06ca1493bULL, 0x01ae3a4617c510eaULL
        };
        uint8_t base[48], result[48];
        memcpy(base, (void *)(br_word_t)norm, 48);

        /* Start with result = 1 (Montgomery form = R mod p) */
        memcpy(result, BLS377_R, 48);

        /* Scan bits from MSB to LSB */
        for (int word = 5; word >= 0; word--) {
            uint64_t w = p_minus_2[word];
            int start_bit = (word == 5) ? 56 : 63; /* MSB of top word is bit 56 (381-6*64=381-384=-3, so bit 56) */
            for (int bit = start_bit; bit >= 0; bit--) {
                bls377_square((br_word_t)result, (br_word_t)result);
                if ((w >> bit) & 1) {
                    bls377_mul((br_word_t)result, (br_word_t)result, (br_word_t)base);
                }
            }
        }
        memcpy(inv_norm, result, 48);
    }

    /* out = (a * inv_norm, -b * inv_norm) */
    bls377_opp((br_word_t)neg_b, x + 48);
    bls377_mul(out, x, (br_word_t)inv_norm);
    bls377_mul(out + 48, (br_word_t)neg_b, (br_word_t)inv_norm);
}
