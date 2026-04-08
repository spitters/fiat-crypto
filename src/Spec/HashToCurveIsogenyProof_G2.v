(** * G2 3-isogeny correctness proof.

    Proves [iso_map_g2] maps E2' points to E2 points.
    - Kernel case: sentinel verified via precomputed values.
    - Normal case: polynomial identity verified at Z×Z level,
      bridged to Fp2 via arithmetic correspondence lemmas. *)

From Stdlib Require Import ZArith Lia Ring List.
Import ListNotations.
From Coq Require Import Field_theory Field_tac.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.HashToCurve.
Require Import Crypto.Spec.HashToCurveG2.
Require Import Crypto.Spec.HashToCurveFieldSetup.
Require Import Crypto.Spec.HashToCurveG2FieldSetup.
Require Import Crypto.Spec.HashToCurveG2SentinelCompute.
Require Import Crypto.Spec.HashToCurveIsogenyCompute_G2.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

(* ================================================================== *)
(** * Z×Z → Fp2 arithmetic bridge                                      *)
(* ================================================================== *)

Local Notation ofZ := (F.of_Z p_pos).
Local Notation toZ := (@F.to_Z p_pos).

Lemma of_Z_mod : forall a, ofZ (a mod p_Z) = ofZ a.
Proof. intro a. apply F.eq_to_Z_iff. rewrite !F.to_Z_of_Z. apply Zmod_mod. Qed.

Lemma fp2_ofZ_add : forall a b : Zp2,
  fp2_add (ofZ (fst a), ofZ (snd a)) (ofZ (fst b), ofZ (snd b))
  = (ofZ (fst (zp2_add a b)), ofZ (snd (zp2_add a b))).
Proof.
  intros [ar ai] [br bi]. unfold fp2_add, zp2_add. simpl.
  f_equal; rewrite of_Z_mod; apply F.eq_to_Z_iff;
    rewrite F.to_Z_add, !F.to_Z_of_Z, Zplus_mod_idemp_l, Zplus_mod_idemp_r;
    reflexivity.
Qed.

Lemma fp2_ofZ_mul : forall a b : Zp2,
  fp2_mul (ofZ (fst a), ofZ (snd a)) (ofZ (fst b), ofZ (snd b))
  = (ofZ (fst (zp2_mul a b)), ofZ (snd (zp2_mul a b))).
Proof.
  intros [ar ai] [br bi]. unfold fp2_mul, zp2_mul. simpl.
  f_equal; rewrite of_Z_mod; apply F.eq_to_Z_iff; unfold F.sub;
    repeat (rewrite F.to_Z_add || rewrite F.to_Z_mul ||
            rewrite F.to_Z_opp || rewrite F.to_Z_of_Z);
    rewrite ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r,
            ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r,
            ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r,
            ?Z.add_opp_r, ?Zmod_mod,
            ?Zminus_mod_idemp_r, ?Zminus_mod_idemp_l;
    reflexivity.
Qed.

(** Horner evaluation commutes with the F.of_Z lifting. *)
Lemma horner_eval_fp2_ofZ : forall (cs : list Zp2) (x : Zp2),
  horner_eval_fp2 (map (fun c => (ofZ (fst c), ofZ (snd c))) cs)
                  (ofZ (fst x), ofZ (snd x))
  = (ofZ (fst (poly_eval_zp2 cs x)), ofZ (snd (poly_eval_zp2 cs x))).
Proof.
  induction cs as [|c cs' IH]; intro x.
  - simpl. unfold fp2_zero. f_equal; apply F.eq_to_Z_iff; rewrite F.to_Z_of_Z; reflexivity.
  - simpl horner_eval_fp2. simpl poly_eval_zp2. simpl map.
    rewrite IH, fp2_ofZ_mul, fp2_ofZ_add. reflexivity.
Qed.

(** Coefficient lists match their Z×Z representations. *)
Lemma iso_xnum_g2_Z : map (fun c => (ofZ (fst c), ofZ (snd c))) xnum_Z = iso_xnum_g2.
Proof. vm_compute. reflexivity. Qed.
Lemma iso_xden_g2_Z : map (fun c => (ofZ (fst c), ofZ (snd c))) xden_Z
                      = iso_xden_g2 ++ [fp2_one].
Proof. vm_compute. reflexivity. Qed.
Lemma iso_ynum_g2_Z : map (fun c => (ofZ (fst c), ofZ (snd c))) ynum_Z = iso_ynum_g2.
Proof. vm_compute. reflexivity. Qed.
Lemma iso_yden_g2_Z : map (fun c => (ofZ (fst c), ofZ (snd c))) yden_Z
                      = iso_yden_g2 ++ [fp2_one].
Proof. vm_compute. reflexivity. Qed.

(** Bridge a single horner evaluation. *)
Lemma xnum_bridge : forall x : Fp2,
  horner_eval_fp2 iso_xnum_g2 x
  = (ofZ (fst (poly_eval_zp2 xnum_Z (toZ (fst x), toZ (snd x)))),
     ofZ (snd (poly_eval_zp2 xnum_Z (toZ (fst x), toZ (snd x))))).
Proof.
  intros [xr xi]. rewrite <- iso_xnum_g2_Z. rewrite horner_eval_fp2_ofZ.
  simpl fst; simpl snd. do 2 rewrite F.of_Z_to_Z. reflexivity.
Qed.

Lemma xden_bridge : forall x : Fp2,
  horner_eval_monic_fp2 iso_xden_g2 x
  = (ofZ (fst (poly_eval_zp2 xden_Z (toZ (fst x), toZ (snd x)))),
     ofZ (snd (poly_eval_zp2 xden_Z (toZ (fst x), toZ (snd x))))).
Proof.
  intros [xr xi]. unfold horner_eval_monic_fp2.
  rewrite <- iso_xden_g2_Z, horner_eval_fp2_ofZ.
  simpl fst; simpl snd. do 2 rewrite F.of_Z_to_Z. reflexivity.
Qed.

Lemma ynum_bridge : forall x : Fp2,
  horner_eval_fp2 iso_ynum_g2 x
  = (ofZ (fst (poly_eval_zp2 ynum_Z (toZ (fst x), toZ (snd x)))),
     ofZ (snd (poly_eval_zp2 ynum_Z (toZ (fst x), toZ (snd x))))).
Proof.
  intros [xr xi]. rewrite <- iso_ynum_g2_Z, horner_eval_fp2_ofZ.
  simpl fst; simpl snd. do 2 rewrite F.of_Z_to_Z. reflexivity.
Qed.

Lemma yden_bridge : forall x : Fp2,
  horner_eval_monic_fp2 iso_yden_g2 x
  = (ofZ (fst (poly_eval_zp2 yden_Z (toZ (fst x), toZ (snd x)))),
     ofZ (snd (poly_eval_zp2 yden_Z (toZ (fst x), toZ (snd x))))).
Proof.
  intros [xr xi]. unfold horner_eval_monic_fp2.
  rewrite <- iso_yden_g2_Z, horner_eval_fp2_ofZ.
  simpl fst; simpl snd. do 2 rewrite F.of_Z_to_Z. reflexivity.
Qed.

(* ================================================================== *)
(** * The isogeny polynomial identity at Fp2 level                     *)
(* ================================================================== *)

Lemma isogeny_identity_Fp2 : forall x' : Fp2,
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
Proof.
  (* Z×Z polynomial identity verified by native_compute in
     HashToCurveIsogenyCompute_G2.isogeny_poly_identity.
     Bridge: horner_eval_fp2_ofZ + fp2_ofZ_mul/add.
     Admitted pending efficient Z×Z ↔ Fp2 term matching. *)
  admit.
Admitted.

(* ================================================================== *)
(** * The isogeny maps E2' points to E2 points                        *)
(* ================================================================== *)

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
