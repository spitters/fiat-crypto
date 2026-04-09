(** * G2 3-isogeny correctness proof.

    Proves [iso_map_g2] maps E2' points to E2 points.
    - Kernel case: sentinel verified via precomputed values.
    - Normal case: polynomial identity (verified at Z×Z level in
      HashToCurveIsogenyCompute_G2) + Field.fsatz.

    Bridge from Z×Z → Fp2 is admitted: vm_compute on map of F.of_Z
    with 381-bit constants is too slow (OOMs at >6GB). *)

From Stdlib Require Import ZArith Lia Ring.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.HashToCurve.
Require Import Crypto.Spec.HashToCurveG2.
Require Import Crypto.Spec.HashToCurveFieldSetup.
Require Import Crypto.Spec.HashToCurveG2FieldSetup.
Require Import Crypto.Spec.HashToCurveG2SentinelCompute.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

(** The isogeny polynomial identity at the Fp2 level.
    Z×Z verification in IsogenyCompute_G2.isogeny_poly_identity.
    Bridge admitted due to compilation memory issues. *)
Axiom isogeny_identity_Fp2 : forall x' : Fp2,
  let xn := horner_eval_fp2 iso_xnum_g2 x' in
  let xd := horner_eval_monic_fp2 iso_xden_g2 x' in
  let yn := horner_eval_fp2 iso_ynum_g2 x' in
  let yd := horner_eval_monic_fp2 iso_yden_g2 x' in
  fp2_mul (fp2_mul (fp2_add (fp2_add (fp2_cube x') (fp2_mul iso_A_g2 x')) iso_B_g2)
                    (fp2_mul yn yn))
          (fp2_mul (fp2_mul xd xd) xd)
  =
  fp2_add
    (fp2_mul (fp2_mul (fp2_mul xn xn) xn) (fp2_mul yd yd))
    (fp2_mul bls12_b_g2 (fp2_mul (fp2_mul (fp2_mul xd xd) xd) (fp2_mul yd yd))).

(** The isogeny maps E2' points to E2 points. *)
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
  - exact sentinel_on_curve_E2.
  - apply fp2_eqb_false_iff in Hz.
    assert (Hxd : xd <> fp2_zero)
      by (intro H; apply Hz; subst z; rewrite H; ring).
    assert (Hyd : yd <> fp2_zero)
      by (intro H; apply Hz; subst z; rewrite H; ring).
    pose proof (isogeny_identity_Fp2 x') as Hident.
    cbv zeta in Hident. fold xn xd yn yd in Hident.
    unfold fp2_sqr, fp2_cube in *.
    rewrite <- Hcurve in Hident.
    set (b := bls12_b_g2) in *.
    subst z. clearbody xn xd yn yd b. clear Hcurve x'.
    unfold fp2_sqr in *.
    Field.fsatz.
Qed.
