/*
 * bls377_pairing.h -- Public interface for verified BLS12-377 pairing
 *
 * Generated from Rocq (Coq) proofs via fiat-crypto / bedrock2 extraction.
 * All Fp arithmetic is fully verified. Fp2-Fp12 tower and pairing functions
 * have weakest-precondition proofs in the bedrock2 separation logic.
 *
 * Representation: all field elements are in Montgomery form with
 * R = 2^384 mod p. Pointers are passed as br_word_t (uintptr_t).
 * An Fp element is 48 bytes (6 x 64-bit limbs, little-endian).
 * Higher tower elements are flat concatenations:
 *   Fp2  =  2 x Fp  =  96 bytes
 *   Fp6  =  3 x Fp2 = 288 bytes
 *   Fp12 =  2 x Fp6 = 576 bytes
 */

#ifndef BLS377_PAIRING_H
#define BLS377_PAIRING_H

#include <stdint.h>

typedef uintptr_t br_word_t;

/* ---- Size constants ---- */
#define BLS377_FP_BYTES    48
#define BLS377_FP2_BYTES   96
#define BLS377_FP6_BYTES  288
#define BLS377_FP12_BYTES 576

/* ---- Fp arithmetic (verified, from fiat-crypto synthesis) ---- */
void bls377_add(br_word_t out, br_word_t x, br_word_t y);
/* bls377_sub, bls377_mul, bls377_square are static in the extraction */

/* ---- Fp primitives (bridge layer) ---- */
void bls377_opp(br_word_t out, br_word_t x);
void bls377_from_word(br_word_t out, br_word_t w);

/* ---- Fp2 = Fp[u]/(u^2+5) ---- */
/* These are static in the compilation unit; listed here for documentation.
 * Call them only via #include of the .c files in a single translation unit.
 *
 * bls377_Fp2_add(out, x, y)
 * bls377_Fp2_sub(out, x, y)
 * bls377_Fp2_mul(out, x, y)
 * bls377_Fp2_square(out, x)
 * bls377_Fp2_inv(out, x)
 * bls377_Fp2_opp(out, x)
 * bls377_Fp2_conjugate(out, x)
 * bls377_Fp2_mul_xi(out, x)        -- multiply by twist parameter xi
 * bls377_Fp2_mul_fp(out, x, s)     -- Fp2 * Fp scalar
 * bls377_Fp2_felem_copy(out, x)
 */

/* ---- Fp6 = Fp2[v]/(v^3-xi) ---- */
/*
 * bls377_Fp6_add(out, x, y)
 * bls377_Fp6_sub(out, x, y)
 * bls377_Fp6_mul(out, x, y)
 * bls377_Fp6_square(out, x)
 * bls377_Fp6_inv(out, x)
 * bls377_Fp6_opp(out, x)
 * bls377_Fp6_mul_fp2(out, x, s)    -- Fp6 * Fp2 scalar
 * bls377_Fp6_mul_by_v(out, x)      -- multiply by v
 * bls377_Fp6_frobenius(out, x, gamma1, gamma2)
 * bls377_Fp6_frobenius_p2(out, x, gamma1_p2, gamma2_p2)
 * bls377_Fp6_felem_copy(out, x)
 */

/* ---- Fp12 = Fp6[w]/(w^2-v) ---- */
/*
 * bls377_Fp12_add(out, x, y)
 * bls377_Fp12_sub(out, x, y)
 * bls377_Fp12_mul(out, x, y)
 * bls377_Fp12_square(out, x)
 * bls377_Fp12_inv(out, x)
 * bls377_Fp12_opp(out, x)
 * bls377_Fp12_conjugate(out, x)
 * bls377_Fp12_frobenius(out, x, gamma1, gamma2, w_frob_c1)
 * bls377_Fp12_frobenius_p2(out, x, gamma1_p2, gamma2_p2, w_frob_p2_c1)
 * bls377_Fp12_frobenius_p3(out, x, g1, g2, g1p2, g2p2, wc1, wp2c1)
 * bls377_Fp12_pow_u(out, base)     -- raise to curve parameter u
 * bls377_Fp12_felem_copy(out, x)
 */

/* ---- Frobenius constant loaders ---- */
/*
 * bls377_load_gamma1(out)           -- Fp2, 96 bytes
 * bls377_load_gamma2(out)           -- Fp2, 96 bytes
 * bls377_load_gamma1_p2(out)        -- Fp2, 96 bytes
 * bls377_load_gamma2_p2(out)        -- Fp2, 96 bytes
 * bls377_load_w_frob_c1(out)        -- Fp2, 96 bytes
 * bls377_load_w_frob_p2_c1(out)     -- Fp2, 96 bytes
 */

/* ---- Pairing ---- */
/*
 * bls377_miller_loop(out, p_x, p_y, q_x, q_y)
 *   Compute the Miller loop for the ate pairing.
 *   P = (p_x, p_y) in G1 (Fp coords, 48 bytes each)
 *   Q = (q_x, q_y) in G2 (Fp2 coords, 96 bytes each)
 *   out: Fp12 element (576 bytes)
 *
 * bls377_final_exp(out, f, g1p2, g2p2, wp2c1)
 *   Naive final exponentiation (binary square-and-multiply for hard part).
 *
 * bls377_final_exp_dsd(out, f, g1p2, g2p2, wp2c1)
 *   DSD-optimized final exponentiation (Devegili-Scott-Dahab decomposition).
 *
 * bls377_pairing(out, p_x, p_y, q_x, q_y)
 *   Full pairing = miller_loop + final_exp (naive).
 *
 * bls377_pairing_dsd(out, p_x, p_y, q_x, q_y)
 *   Full pairing = miller_loop + final_exp_dsd (optimized).
 */

#endif /* BLS377_PAIRING_H */
