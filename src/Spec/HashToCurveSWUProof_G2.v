(** * G2 SWU correctness proof.

    Proves: forall u, on_curve_E2prime (map_to_curve_simple_swu_fp2 ...).

    Structure mirrors HashToCurveSWUProof.v but over Fp2. Requires:
    1. fp2_sqrt correctness (fp2_sqrt(x)² = x when fp2_is_square(x) = true)
    2. Norm multiplicativity for Fp2 quadratic residuosity
    3. Algebraic identity gx2 = t³ · gx1

    Items 2-3 follow the G1 proof pattern. Item 1 needs the complex
    square root algorithm correctness (~200 lines, standalone). *)

From Stdlib Require Import ZArith Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.HashToCurve.
Require Import Crypto.Spec.HashToCurveG2.
Require Import Crypto.Spec.HashToCurveG2FieldSetup.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

(** fp2_sqrt correctness: admitted pending complex sqrt algorithm proof. *)
Axiom fp2_sqrt_correct : forall x : Fp2,
  fp2_is_square x = true -> fp2_sqr (fp2_sqrt x) = x.

(** Main theorem: SWU map always produces a point on E2'.
    Proof sketch (same as G1):
    - gx2 = t³ · gx1 where t = Z·u² (ring identity)
    - Z is a non-square in Fp2 (fp2_is_square swu_Z_g2 = false by native_compute)
    - Legendre multiplicativity via norm: exactly one of {gx1, gx2} is a square
    - fp2_sqrt gives correct y for whichever gx is a square
    - Sign correction preserves y² = gx (since (-y)² = y²) *)
Theorem swu_g2_maps_to_E2prime : forall u : Fp2,
  on_curve_E2prime (map_to_curve_simple_swu_fp2 iso_A_g2 iso_B_g2 swu_Z_g2 u).
Proof. admit. Admitted.
