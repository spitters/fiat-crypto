(** * BLS12-381 fp_sqrt correctness — isolated for slow Qed.

    This file proves [fp_sqrt_correct] and [fp_sqrt_other_root] separately
    from [BLS12_Legendre.v]. The Qed takes 10+ minutes because the kernel
    WHNF-reduces [Z.pow] through the 380-bit exponent during conversion.
    By compiling this once (with [ulimit -s unlimited]) and caching the .vo,
    downstream files pay nothing on rebuild.

    Build: [ulimit -s unlimited && dune build ... BLS12_Legendre_FpSqrt.vo] *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.

From Crypto.Bedrock.Field.Synthesis.Examples Require Import BLS12_Legendre.

Local Open Scope Z_scope.

(** The exponents must be Transparent for the proof to go through,
    since the rewrite chain needs kernel conversion between
    [legendre_spec a] and [a ^ bls12_legendre_exp mod bls12_p].
    We locally undo the Opaque from BLS12_Legendre.v. *)
#[local] Transparent bls12_legendre_exp bls12_sqrt_exp.

Lemma fp_sqrt_correct_proved : forall a, 0 < a < bls12_p ->
  legendre a = 1 ->
  (fp_sqrt a * fp_sqrt a) mod bls12_p = a mod bls12_p.
Proof.
  intros a Ha Hleg.
  rewrite fp_sqrt_eq_spec. unfold fp_sqrt_spec.
  rewrite Zmult_mod. rewrite Zmod_mod. rewrite <- Zmult_mod.
  rewrite <- Z.pow_twice_r.
  rewrite bls12_sqrt_leg_exp.
  rewrite Z.pow_add_r by (try apply bls12_legendre_exp_nonneg; lia).
  rewrite Z.pow_1_r.
  rewrite Zmult_mod.
  replace (a ^ bls12_legendre_exp mod bls12_p) with (legendre a).
  2:{ symmetry. apply legendre_eq_spec. }
  rewrite Hleg. rewrite Z.mul_1_l. rewrite Zmod_mod. reflexivity.
Qed.

Lemma fp_sqrt_other_root_proved : forall a, 0 < a < bls12_p ->
  legendre a = 1 ->
  let s := fp_sqrt a in
  ((bls12_p - s) * (bls12_p - s)) mod bls12_p = a mod bls12_p.
Proof.
  intros a Ha Hleg. simpl.
  pose proof (fp_sqrt_correct_proved a Ha Hleg) as Hcorr.
  set (s := fp_sqrt a) in *.
  replace ((bls12_p - s) * (bls12_p - s))
    with (s * s + bls12_p * (bls12_p - 2 * s)) by ring.
  rewrite Z_mod_plus_full.
  exact Hcorr.
Qed.
