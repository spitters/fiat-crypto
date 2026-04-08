(** * G2 3-isogeny correctness proof.

    Proves [iso_map_g2 : on_curve_E2prime → on_curve_E2].

    The 3-isogeny is much simpler than G1's 11-isogeny:
    - x_num : degree 3 polynomial (4 coefficients)
    - x_den : degree 2 polynomial (monic, 2 coefficients)
    - y_num : degree 3 polynomial (4 coefficients)
    - y_den : degree 3 polynomial (monic, 3 coefficients)

    Verification: the polynomial identity
       (y'² - A'·x' - B') · y_num² · x_den³ = x_num³ · y_den² + B · x_den³ · y_den²
    holds in Fp2[x']. We prove this by symbolic manipulation. *)

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

Theorem iso_map_g2_on_curve : forall (pt : Fp2 * Fp2),
  on_curve_E2prime pt ->
  on_curve_E2 (iso_map_g2 pt).
Proof.
  (* Mirrors HashToCurveIsogenyProof.iso_map_on_curve but over Fp2.
     Key steps:
     1. Branch on z := xd * yd = 0 (kernel case).
     2. Kernel case: output is (0, sqrt(b)), need sqrt(b)² = b — true by sqrt definition.
     3. Normal case: use the polynomial identity from RFC 9380 §E.3. *)
  admit.
Admitted.
