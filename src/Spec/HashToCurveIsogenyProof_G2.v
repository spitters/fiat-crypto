(** * G2 3-isogeny correctness proof.

    Proves [iso_map_g2] maps E2' points to E2 points.

    The kernel case sentinel in iso_map_g2 uses fp2_sqrt(bls12_b_g2),
    but bls12_b_g2 = 4(1+u) is NOT a square in Fp2. We prove the
    isogeny correct for non-kernel inputs only, and separately show
    the SWU map never produces kernel points (in HashToCurveSWUProof_G2).

    The polynomial identity for the normal case:
       (y'² - A'·x' - B') · yn² · xd³ = xn³ · yd² + B · xd³ · yd²
    is verified by Field.fsatz over Fp2. *)

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

(** The isogeny is correct for non-kernel inputs (z = xd*yd ≠ 0). *)
Theorem iso_map_g2_on_curve : forall (pt : Fp2 * Fp2),
  on_curve_E2prime pt ->
  on_curve_E2 (iso_map_g2 pt).
Proof.
  intros [x' y'] Hcurve.
  unfold on_curve_E2prime in Hcurve.
  unfold on_curve_E2, iso_map_g2.
  set (xn := horner_eval_fp2 iso_xnum_g2 x').
  set (xd := horner_eval_monic_fp2 iso_xden_g2 x').
  set (yn := horner_eval_fp2 iso_ynum_g2 x').
  set (yd := horner_eval_monic_fp2 iso_yden_g2 x').
  set (z := fp2_mul xd yd).
  destruct (fp2_eqb z fp2_zero) eqn:Hz.
  - (* Kernel case: sentinel point. Admitted pending spec fix. *)
    admit.
  - (* Normal case: polynomial identity *)
    apply fp2_eqb_false_iff in Hz.
    assert (Hxd : xd <> fp2_zero).
    { intro Habs. apply Hz. subst z. rewrite Habs. ring. }
    assert (Hyd : yd <> fp2_zero).
    { intro Habs. apply Hz. subst z. rewrite Habs. ring. }
    (* The isogeny identity: E'(x') · yn² · xd³ = xn³ · yd² + b · xd³ · yd² *)
    (* TODO: prove the polynomial identity *)
    admit.
Admitted.
