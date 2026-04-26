(** Precomputed Montgomery constants for P-256.
    Uses native_compute once; downstream files import the .vo. *)

From Crypto.Bedrock.P256 Require Import Specs.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
From Stdlib Require Import ZArith.
Import Specs.NotationsCustomEntry.
Local Existing Instances
  Bitwidth64.BW64 Defaults64.default_parameters Defaults64.default_parameters_ok
  p256_field_parameters p256_field_parameters_ok p256_frep p256_frep_ok.

Local Open Scope Z_scope.

Definition p256_r' : Z := @WordByWordMontgomery.r' 64 p256_field_parameters.
Definition p256_m' : Z := WordByWordMontgomery.m' m 64.

Lemma p256_r'_correct : (2 ^ 64 * p256_r') mod m = 1.
Proof. apply Z.eqb_eq. native_compute. reflexivity. Qed.

Lemma p256_m'_correct : (m * p256_m') mod 2 ^ 64 = (-1) mod 2 ^ 64.
Proof. apply Z.eqb_eq. native_compute. reflexivity. Qed.

Lemma p256_m_big : m < (2 ^ 64) ^ Z.of_nat 4.
Proof. apply Z.ltb_lt. native_compute. reflexivity. Qed.

Lemma p256_m_small : 1 < m.
Proof. apply Z.ltb_lt. native_compute. reflexivity. Qed.

Lemma p256_r'4 : (p256_r' ^ 4 * 2 ^ 256) mod m = 1.
Proof. apply Z.eqb_eq. native_compute. reflexivity. Qed.
