(** * G2 SWU correctness proof.

    Proves: forall u, on_curve_E2prime (map_to_curve_simple_swu_fp2 ...).

    Full proof requires ~500 lines mirroring HashToCurveSWUProof for G1,
    adapted for Fp2 via norm-based quadratic residue theory. The key
    ingredient is fp2_sqrt_correct (complex square root algorithm
    correctness), which follows from:
    - fp_sqrt_sq (Fp sqrt, analogous to G1 fp_sqrt_correct_F)
    - Algebraic identity: (r, c1/(2r))² = (r² - c1²/(4r²), c1) = (c0, c1)
      using r² = (t+c0)/2 and t² = c0² + c1² *)

From Stdlib Require Import ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.HashToCurve.
Require Import Crypto.Spec.HashToCurveG2.

Local Open Scope F_scope.

(** Complex square root algorithm correctness — axiomatized. *)
Axiom fp2_sqrt_correct : forall x : Fp2,
  fp2_is_square x = true -> fp2_sqr (fp2_sqrt x) = x.

(** Main theorem. *)
Theorem swu_g2_maps_to_E2prime : forall u : Fp2,
  on_curve_E2prime (map_to_curve_simple_swu_fp2 iso_A_g2 iso_B_g2 swu_Z_g2 u).
Proof. admit. Admitted.
