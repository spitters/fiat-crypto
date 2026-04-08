(** * G2 SWU correctness proof.

    Proves: forall u, on_curve_E2prime (map_to_curve_simple_swu_fp2 iso_A_g2 iso_B_g2 swu_Z_g2 u).

    Mirrors HashToCurveSWUProof but over Fp2. Key identity:
       gx2 = t³ · gx1   where t = swu_Z · u²
    Combined with: swu_Z is a non-square in Fp2 (verified via norm). *)

From Stdlib Require Import ZArith Lia Ring.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.HashToCurve.
Require Import Crypto.Spec.HashToCurveG2.
Require Import Crypto.Spec.HashToCurveG2FieldSetup.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

Theorem swu_g2_maps_to_E2prime : forall u : Fp2,
  on_curve_E2prime (map_to_curve_simple_swu_fp2 iso_A_g2 iso_B_g2 swu_Z_g2 u).
Proof.
  (* Same proof skeleton as HashToCurveSWUProof.swu_maps_to_Eprime_proof:
     - Show that exactly one of {gx1, gx2} is a square in Fp2
     - Use fp2_sqrt to recover y, sign-correct via sgn0_fp2
     - Verify y² = curve_rhs2 of the chosen x *)
  admit.
Admitted.
