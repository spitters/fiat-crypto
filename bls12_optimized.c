/* BLS12-381 optimized final exponentiation
 *
 * Integrates:
 * - DSD (Hayashida-Hayasaka-Teruya) hard part: 5.5 exp-by-x vs 1268-bit naive
 * - Cyclotomic squaring: saves 1 Fp6_mul per squaring in GΦ₁₂
 *
 * Drop-in replacement for bls12_final_exp.
 */

/* No-alias Fp12_mul: skip input copies when caller guarantees out != inx && out != iny */
static void bls12_Fp12_mul_noalias(br_word_t out, br_word_t inx, br_word_t iny) {
    br_word_t v0, v1, t, u;
    uint8_t _v0[0x120], _v1[0x120], _t[0x120], _u[0x120];
    v0 = (br_word_t)&_v0; v1 = (br_word_t)&_v1;
    t = (br_word_t)&_t; u = (br_word_t)&_u;
    bls12_Fp6_mul(v0, inx, iny);
    bls12_Fp6_mul(v1, inx+0x120, iny+0x120);
    bls12_Fp6_add(t, inx, inx+0x120);
    bls12_Fp6_add(u, iny, iny+0x120);
    bls12_Fp6_mul(t, t, u);
    bls12_Fp6_mul_by_v(u, v1);
    bls12_Fp6_add(out, v0, u);
    bls12_Fp6_sub(t, t, v0);
    bls12_Fp6_sub(out+0x120, t, v1);
}

/* No-alias Fp12_square: skip input copy */
static void bls12_Fp12_square_noalias(br_word_t out, br_word_t x) {
    bls12_Fp12_mul_noalias(out, x, x);
}

/* Montgomery form of 1 for BLS12-381 */
static const uint64_t FP_MONT_ONE[6] = {
    0x760900000002fffdULL, 0xebf4000bc40c0002ULL,
    0x5f48985753c758baULL, 0x77ce585370525745ULL,
    0x5c071a97a256ec6dULL, 0x15f65ec3fa80e493ULL
};

/* #4: Cyclotomic Fp12 squaring.
 * For f = (c0, c1) in GΦ₁₂:
 *   new_c0 = 1 + 2·mul_by_v(c1²)
 *   new_c1 = 2·c0·c1
 * Uses 2 Fp6_mul + 1 Fp6_mul_by_v instead of 3 Fp6_mul. */
static void bls12_Fp12_cyc_square(br_word_t out, br_word_t f) {
    br_word_t c0 = f, c1 = f + 288;
    uint8_t c1_sq[288], cross[288], v_c1_sq[288];

    bls12_Fp6_mul((br_word_t)c1_sq, c1, c1);
    bls12_Fp6_mul((br_word_t)cross, c0, c1);

    /* mul_by_v((a,b,c)) = (xi*c, a, b) */
    bls12_Fp2_mul_xi((br_word_t)v_c1_sq, (br_word_t)c1_sq + 192);
    __builtin_memcpy(v_c1_sq + 96, c1_sq, 96);
    __builtin_memcpy(v_c1_sq + 192, c1_sq + 96, 96);

    /* new_c0 = 2*v_c1_sq + 1 */
    bls12_Fp6_add(out, (br_word_t)v_c1_sq, (br_word_t)v_c1_sq);
    /* Add Montgomery(1) to first Fp component */
    uint64_t *dst = (uint64_t *)out;
    uint64_t carry = 0;
    for (int i = 0; i < 6; i++) {
        __uint128_t s = (__uint128_t)dst[i] + FP_MONT_ONE[i] + carry;
        dst[i] = (uint64_t)s;
        carry = (uint64_t)(s >> 64);
    }
    /* Conditional reduction */
    static const uint64_t P[6] = {
        0xb9feffffffffaaabULL, 0x1eabfffeb153ffffULL,
        0x6730d2a0f6b0f624ULL, 0x64774b84f38512bfULL,
        0x4b1ba7b6434bacd7ULL, 0x1a0111ea397fe69aULL
    };
    uint64_t sub[6], borrow = 0;
    for (int i = 0; i < 6; i++) {
        __uint128_t d = (__uint128_t)dst[i] - P[i] - borrow;
        sub[i] = (uint64_t)d;
        borrow = (d >> 64) ? 1 : 0;
    }
    uint64_t mask = -(uint64_t)(carry | (1 - borrow));
    for (int i = 0; i < 6; i++)
        dst[i] = (sub[i] & mask) | (dst[i] & ~mask);

    /* new_c1 = 2*cross */
    bls12_Fp6_add(out + 288, (br_word_t)cross, (br_word_t)cross);
}

/* Exp-by-x: compute f^|x| where |x| = 0xd201000000010000 (64 bits, HW=6).
 * Uses cyclotomic squaring since inputs are in GΦ₁₂. */
static void bls12_exp_by_x(br_word_t out, br_word_t f) {
    /* |x| = 0xd201000000010000
     * Binary: 1101001000000001000000000000000000000000000000010000000000000000
     * Non-zero bits at positions (from MSB): 63,62,60,57,48,16 */
    uint8_t result[576], tmp[576];
    int started = 0;

    bls12_Fp12_felem_copy((br_word_t)result, f);

    /* Scan bits 62 down to 0 (bit 63 is handled by initializing result=f) */
    for (int i = 62; i >= 0; i--) {
        bls12_Fp12_cyc_square((br_word_t)result, (br_word_t)result);
        uint64_t bit = (0xd201000000010000ULL >> i) & 1;
        if (bit) {
            bls12_Fp12_mul((br_word_t)result, (br_word_t)result, f);
        }
    }
    bls12_Fp12_felem_copy(out, (br_word_t)result);
}

/* Exp-by-x signed: compute f^{-|x|} = conjugate(f^|x|) */
static void bls12_exp_by_x_signed(br_word_t out, br_word_t f) {
    bls12_exp_by_x(out, f);
    bls12_Fp12_conjugate(out, out);
}

/* Exp-by-x-half signed: compute f^{-|x|/2}
 * |x|/2 = 0x6900800000008000 */
static void bls12_exp_by_x_half_signed(br_word_t out, br_word_t f) {
    uint8_t result[576];
    bls12_Fp12_felem_copy((br_word_t)result, f);

    for (int i = 62; i >= 0; i--) {
        bls12_Fp12_cyc_square((br_word_t)result, (br_word_t)result);
        uint64_t bit = (0x6900800000008000ULL >> i) & 1;
        if (bit) {
            bls12_Fp12_mul((br_word_t)result, (br_word_t)result, f);
        }
    }
    /* Conjugate for the negative sign */
    bls12_Fp12_conjugate(out, (br_word_t)result);
}

/* DSD hard part: Hayashida-Hayasaka-Teruya algorithm.
 * Computes f^{3*h3} using 5.5 exp-by-x + 2 Frobenius + 9 mul.
 * ~320 cyclotomic squarings vs 1268 for naive. */
static void bls12_final_exp_hard_dsd(br_word_t out, br_word_t f,
    br_word_t gamma1, br_word_t gamma2, br_word_t w_frob_c1,
    br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_p2_c1) {
    uint8_t t0[576], t1[576], t2[576], result[576];

    /* t0 = f^2 */
    bls12_Fp12_cyc_square((br_word_t)t0, f);

    /* t1 = t0^{-|x|/2} = f^{-|x|} */
    bls12_exp_by_x_half_signed((br_word_t)t1, (br_word_t)t0);

    /* t2 = f^{-1} */
    bls12_Fp12_conjugate((br_word_t)t2, f);

    /* t1 = t1 * t2 = f^{-|x|-1} */
    bls12_Fp12_mul((br_word_t)t1, (br_word_t)t1, (br_word_t)t2);

    /* t2 = t1^{-|x|} = f^{|x|^2+|x|} */
    bls12_exp_by_x_signed((br_word_t)t2, (br_word_t)t1);

    /* t1 = t1^{-1} = f^{|x|+1} */
    bls12_Fp12_conjugate((br_word_t)t1, (br_word_t)t1);

    /* t1 = t1 * t2 = f^{(|x|+1)^2} */
    bls12_Fp12_mul((br_word_t)t1, (br_word_t)t1, (br_word_t)t2);

    /* t2 = t1^{-|x|} = f^{-|x|(|x|+1)^2} */
    bls12_exp_by_x_signed((br_word_t)t2, (br_word_t)t1);

    /* t1 = Frob(t1) = f^{p(|x|+1)^2} */
    bls12_Fp12_frobenius((br_word_t)t1, (br_word_t)t1, gamma1, gamma2, w_frob_c1);

    /* t1 = t1 * t2 = f^{(|x|+1)^2 * (p-|x|)} */
    bls12_Fp12_mul((br_word_t)t1, (br_word_t)t1, (br_word_t)t2);

    /* result = f * t0 = f^3 */
    bls12_Fp12_mul_noalias((br_word_t)result, f, (br_word_t)t0);

    /* t0 = t1^{-|x|} */
    bls12_exp_by_x_signed((br_word_t)t0, (br_word_t)t1);

    /* t2 = t0^{-|x|} */
    bls12_exp_by_x_signed((br_word_t)t2, (br_word_t)t0);

    /* t0 = Frob^2(t1) */
    bls12_Fp12_frobenius_p2((br_word_t)t0, (br_word_t)t1, gamma1_p2, gamma2_p2, w_frob_p2_c1);

    /* t1 = t1^{-1} */
    bls12_Fp12_conjugate((br_word_t)t1, (br_word_t)t1);

    /* t1 = t1 * t2 */
    bls12_Fp12_mul((br_word_t)t1, (br_word_t)t1, (br_word_t)t2);

    /* t1 = t1 * t0 */
    bls12_Fp12_mul((br_word_t)t1, (br_word_t)t1, (br_word_t)t0);

    /* result = result * t1 = f^{3*h3} */
    bls12_Fp12_mul_noalias(out, (br_word_t)result, (br_word_t)t1);
}

/* Complete optimized final exponentiation.
 * Easy part: f^{(p^6-1)(p^2+1)}
 * Hard part: DSD for f^{3*h3} */
static void bls12_final_exp_opt(br_word_t out, br_word_t f,
    br_word_t gamma1, br_word_t gamma2, br_word_t w_frob_c1,
    br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_p2_c1) {
    uint8_t result[576], tmp[576];

    /* Easy part 1: f^{p^6-1} = conj(f) * inv(f) */
    bls12_Fp12_conjugate((br_word_t)result, f);
    bls12_Fp12_inv((br_word_t)tmp, f);
    bls12_Fp12_mul((br_word_t)result, (br_word_t)result, (br_word_t)tmp);

    /* Easy part 2: result^{p^2+1} */
    bls12_Fp12_frobenius_p2((br_word_t)tmp, (br_word_t)result, gamma1_p2, gamma2_p2, w_frob_p2_c1);
    bls12_Fp12_mul((br_word_t)result, (br_word_t)tmp, (br_word_t)result);

    /* Hard part: DSD */
    bls12_final_exp_hard_dsd(out, (br_word_t)result,
        gamma1, gamma2, w_frob_c1,
        gamma1_p2, gamma2_p2, w_frob_p2_c1);
}
