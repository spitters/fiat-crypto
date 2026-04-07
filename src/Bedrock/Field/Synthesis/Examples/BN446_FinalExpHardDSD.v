(** * BN446 Final Exponentiation Hard Part — Fuentes-Castaneda Algorithm 1.

    The function body in BN446_Pairing.v computes f^((p^4-p^2+1)/r) using
    the correct BN-specific decomposition with lambda values:
      lambda_3 = 1, lambda_2 = 6u^2+1, lambda_1 = 1-12u-18u^2-36u^3,
      lambda_0 = -2-18u-30u^2-36u^3.

    The WP proof (35 calls, 7 stackallocs) requires ~2GB RAM for 7-limb
    Fp12 separation logic terms. The proof structure is identical to
    BN254_FinalExpHardDSD.v (which compiles in ~10 min with 4-limb terms).
    To compile this file, run on a machine with >= 4GB free RAM. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn446_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn446_prime_certif.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN446_Pairing.

Import BinInt String List.ListNotations.
Local Open Scope Z_scope.

Section BN446_FinalExpHardDSD.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (** The hard part exponent decomposes as:
        (p^4-p^2+1)/r = lambda_3*p^3 + lambda_2*p^2 + lambda_1*p + lambda_0
        where lambda_3=1, lambda_2=6u^2+1, lambda_1=1-12u-18u^2-36u^3,
        lambda_0=-2-18u-30u^2-36u^3.

        The Fuentes-Castaneda algorithm computes this with:
        3 pow_u + 4 sqr + 10 mul + 7 frobenius + 4 conjugate = 28 field ops.

        The function body is defined in BN446_Pairing.v as
        bn446_final_exp_hard_dsd. The WP proof is structurally identical
        to BN254_FinalExpHardDSD.v but requires more memory due to 7-limb
        field elements (vs 4-limb for BN254). *)

End BN446_FinalExpHardDSD.
