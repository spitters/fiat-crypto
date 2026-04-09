(** * G2 SWU correctness proof.

    Proves: forall u, on_curve_E2prime (map_to_curve_simple_swu_fp2 ...).

    Has:
    - Algebraic identity: gx2 = t³ · gx1 (Field.fsatz with abstract constants)
    - Norm multiplicativity (provable by ring)

    Uses (axiomatized):
    - fp2_sqrt_correct: complex sqrt algorithm correctness
    - swu_g2_maps_to_E2prime: main theorem (full proof requires ~500 lines
      mirroring G1's HashToCurveSWUProof, blocked by compile-time issues
      when importing the heavy HashToCurveSWUCompute infrastructure) *)

From Stdlib Require Import ZArith Lia Ring.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.HashToCurve.
Require Import Crypto.Spec.HashToCurveG2.
Require Import Crypto.Spec.HashToCurveFieldSetup.
Require Import Crypto.Spec.HashToCurveG2FieldSetup.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

(** Complex square root algorithm correctness — axiomatized.
    Proof outline (case c1 ≠ 0):
    Let r² = (t+c0)/2 where t² = c0² + c1². Then
      (r, c1/(2r))² = (r² - c1²/(4r²), c1)
                   = ((t+c0)/2 - c1²/(2(t+c0)), c1)
                   = (c0, c1)
    after algebra using t² = c0² + c1². *)
Axiom fp2_sqrt_correct : forall x : Fp2,
  fp2_is_square x = true -> fp2_sqr (fp2_sqrt x) = x.

(* ================================================================== *)
(** * Algebraic identity: gx2 = t³ · gx1                              *)
(* ================================================================== *)

Lemma swu_gx_ratio_abstract :
  forall (A B Z u : Fp2),
  let t := fp2_mul Z (fp2_mul u u) in
  let S := fp2_add (fp2_mul t t) t in
  S <> fp2_zero ->
  A <> fp2_zero ->
  let tv1 := fp2_inv S in
  let x1 := fp2_mul (fp2_mul (fp2_neg B) (fp2_inv A)) (fp2_add fp2_one tv1) in
  let x2 := fp2_mul t x1 in
  fp2_add (fp2_add (fp2_mul (fp2_mul x2 x2) x2) (fp2_mul A x2)) B
  = fp2_mul (fp2_mul (fp2_mul t t) t)
            (fp2_add (fp2_add (fp2_mul (fp2_mul x1 x1) x1) (fp2_mul A x1)) B).
Proof.
  intros A B Z u t S HS HA tv1 x1 x2.
  subst x2 x1 tv1 S t.
  Field.fsatz.
Qed.

(* ================================================================== *)
(** * Norm multiplicativity                                            *)
(* ================================================================== *)

Lemma fp2_norm_mul : forall a b : Fp2,
  fp2_norm (fp2_mul a b) = fp2_norm a *f fp2_norm b.
Proof.
  intros [ar ai] [br bi]. unfold fp2_norm, fp2_mul. simpl. ring.
Qed.

(* ================================================================== *)
(** * Main theorem (assembly admitted)                                 *)
(* ================================================================== *)

Theorem swu_g2_maps_to_E2prime : forall u : Fp2,
  on_curve_E2prime (map_to_curve_simple_swu_fp2 iso_A_g2 iso_B_g2 swu_Z_g2 u).
Proof. admit. Admitted.
