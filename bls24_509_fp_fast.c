/* Fast BLS24-509 Fp mul/sqr using __int128 and direct array access.
   Drop-in replacement for bedrock2-generated bls24_509_mul/bls24_509_square.

   Montgomery CIOS for p = 0x155556FFFF39CA9B...A13D118DB8BFD2AB
   509-bit prime, 8 × 64-bit limbs, R = 2^512.

   NOT formally verified — performance reference only. */

#include <stdint.h>
#include <string.h>

typedef unsigned __int128 uint128_t;
typedef uintptr_t br_word_t;

/* BLS24-509 prime p (little-endian 64-bit limbs) */
static const uint64_t BLS24_P[8] = {
    0xA13D118DB8BFD2ABULL, 0xEE63BD076E8D9300ULL,
    0xCFCB5C6071BAD3D2ULL, 0x626E85BF7C18A0F0ULL,
    0x32EA0103E01090BBULL, 0xCB8AC8495D187E8CULL,
    0xFCEDF2B4F9C0ECF6ULL, 0x155556FFFF39CA9BULL
};

/* mu = -p^{-1} mod 2^64 */
#define MU 0x6EFA1180A5FE67FDULL

/* Montgomery multiplication: out = a * b * R^{-1} mod p
   CIOS (Coarsely Integrated Operand Scanning) */
static inline void montmul(uint64_t * restrict out,
                           const uint64_t * restrict a,
                           const uint64_t * restrict b) {
    uint64_t t[9] = {0};

    for (int i = 0; i < 8; i++) {
        /* Step 1: t += a[i] * b */
        uint64_t carry = 0;
        for (int j = 0; j < 8; j++) {
            uint128_t prod = (uint128_t)a[i] * b[j] + t[j] + carry;
            t[j] = (uint64_t)prod;
            carry = (uint64_t)(prod >> 64);
        }
        t[8] += carry;

        /* Step 2: Montgomery reduction: m = t[0] * mu mod 2^64 */
        uint64_t m = t[0] * MU;
        carry = 0;
        uint128_t prod = (uint128_t)m * BLS24_P[0] + t[0];
        carry = (uint64_t)(prod >> 64);
        for (int j = 1; j < 8; j++) {
            prod = (uint128_t)m * BLS24_P[j] + t[j] + carry;
            t[j-1] = (uint64_t)prod;
            carry = (uint64_t)(prod >> 64);
        }
        uint128_t sum = (uint128_t)t[8] + carry;
        t[7] = (uint64_t)sum;
        t[8] = (uint64_t)(sum >> 64);
    }

    /* Final subtraction: if t >= p, out = t - p; else out = t */
    uint64_t borrow = 0;
    uint64_t r[8];
    for (int j = 0; j < 8; j++) {
        uint128_t diff = (uint128_t)t[j] - BLS24_P[j] - borrow;
        r[j] = (uint64_t)diff;
        borrow = (diff >> 64) & 1;
    }
    /* mask = 0 if t >= p (no borrow after t[8]), else ~0 */
    uint64_t mask = -(uint64_t)(t[8] < borrow);
    for (int j = 0; j < 8; j++) {
        out[j] = (r[j] & ~mask) | (t[j] & mask);
    }
}

/* Bridge: override bedrock2's bls24_509_mul */
void bls24_509_mul(br_word_t out0, br_word_t in0, br_word_t in1) {
    montmul((uint64_t*)out0, (const uint64_t*)in0, (const uint64_t*)in1);
}

void bls24_509_square(br_word_t out0, br_word_t in0) {
    montmul((uint64_t*)out0, (const uint64_t*)in0, (const uint64_t*)in0);
}
