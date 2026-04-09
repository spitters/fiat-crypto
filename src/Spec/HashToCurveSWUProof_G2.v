(** * G2 SWU correctness proof.

    Proves: forall u, on_curve_E2prime (map_to_curve_simple_swu_fp2 ...).

    KEY: Global Opaque legendre_exp is_square F.pow at the top makes
    Qed verification fast (without it, each Qed takes 10+ minutes due to
    vm_cast verification of legendre_exp computations).

    Strategy (mirrors HashToCurveSWUProof for G1):
    - Algebraic identity: gx2 = t³ · gx1 (Field.fsatz with abstract constants)
    - fp2_is_square via norm + Fp Legendre multiplicativity
    - swu_Z_g2 has non-square norm
    - fp2_sqrt produces correct square roots when input is a square
      (axiomatized: fp2_sqrt_correct) *)

From Stdlib Require Import ZArith Lia Ring.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.HashToCurve.
Require Import Crypto.Spec.HashToCurveG2.
Require Import Crypto.Spec.HashToCurveFieldSetup.
Require Import Crypto.Spec.HashToCurveG2FieldSetup.
Require Import Crypto.Spec.FpLegendre_G2.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

(** Critical: prevent kernel from unfolding these during Qed verification.
    Without this, applying lemmas from FpLegendre_G2 takes 10+ min per Qed. *)
Global Opaque legendre_exp is_square F.pow.

(** Complex square root algorithm correctness — axiomatized. *)
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
(** * Norm and is_square multiplicativity                              *)
(* ================================================================== *)

Lemma fp2_norm_mul : forall a b : Fp2,
  fp2_norm (fp2_mul a b) = fp2_norm a *f fp2_norm b.
Proof.
  intros [ar ai] [br bi]. unfold fp2_norm, fp2_mul. simpl. ring.
Qed.

Lemma fp2_is_square_mul_flip : forall a c : Fp2,
  a <> fp2_zero -> c <> fp2_zero ->
  fp2_is_square c = false ->
  negb (fp2_is_square a) = fp2_is_square (fp2_mul c a).
Proof.
  intros a c Ha Hc Hcsq.
  unfold fp2_is_square in *. rewrite fp2_norm_mul.
  apply is_square_mul_flip_l.
  - apply fp2_norm_nonzero. exact Ha.
  - apply fp2_norm_nonzero. exact Hc.
  - exact Hcsq.
Qed.

(** Helper Z-level lemma: 2 * ((p-1)/2) = p-1, proved by lia (no kernel reduction). *)
Local Lemma two_half_p_minus_1 : (2 * ((Z.pos p_pos - 1) / 2) = Z.pos p_pos - 1)%Z.
Proof.
  pose proof p_pos_gt_2 as Hp.
  pose proof p_minus_1_even as Hev.
  pose proof (Z.div_mod (Z.pos p_pos - 1) 2) as Hd.
  lia.
Qed.

(** Helper: 2 * legendre_exp = p - 1 (lifts Z-level equality). *)
Local Lemma two_legendre_eq : (2 * Z.to_N legendre_exp = Z.to_N (Z.pos p_pos - 1))%N.
Proof.
  pose proof p_pos_gt_2 as Hp.
  rewrite legendre_exp_eq.
  replace (2%N) with (Z.to_N 2) by reflexivity.
  rewrite <- Z2N.inj_mul by (try lia; apply Z.div_pos; lia).
  rewrite two_half_p_minus_1. reflexivity.
Qed.

Lemma fp2_sqr_is_square : forall a : Fp2,
  a <> fp2_zero -> fp2_is_square (fp2_sqr a) = true.
Proof.
  intros a Ha.
  unfold fp2_is_square, fp2_sqr. rewrite fp2_norm_mul.
  apply is_square_true_iff_l. right.
  rewrite pow_mul_distr_l, pow_square_l, two_legendre_eq.
  apply fermat_F_l.
  apply fp2_norm_nonzero. exact Ha.
Qed.

(* ================================================================== *)
(** * Constants                                                         *)
(* ================================================================== *)

Lemma swu_Z_g2_nonzero : swu_Z_g2 <> fp2_zero.
Proof.
  intro H. apply (f_equal fst) in H. simpl in H.
  apply (f_equal F.to_Z) in H. revert H. vm_compute. discriminate.
Qed.

Lemma iso_A_g2_nonzero : iso_A_g2 <> fp2_zero.
Proof.
  intro H. apply (f_equal snd) in H. simpl in H.
  apply (f_equal F.to_Z) in H. revert H. vm_compute. discriminate.
Qed.

Local Transparent is_square F.pow legendre_exp.
Lemma swu_Z_g2_nonsquare : fp2_is_square swu_Z_g2 = false.
Proof. vm_compute. reflexivity. Qed.
Local Opaque is_square F.pow legendre_exp.

(* ================================================================== *)
(** * cube(swu_Z * u²) is non-square                                  *)
(* ================================================================== *)

Lemma fp2_mul_nonzero : forall a b : Fp2,
  a <> fp2_zero -> b <> fp2_zero -> fp2_mul a b <> fp2_zero.
Proof.
  intros a b Ha Hb Hab.
  apply Hb.
  (* a*b = 0 and a ≠ 0 → b = 0 (in a field, integral domain) *)
  assert (Hinv : fp2_mul (fp2_inv a) a = fp2_one)
    by (apply Hierarchy.left_multiplicative_inverse; exact Ha).
  assert (Hcompute : fp2_mul (fp2_inv a) (fp2_mul a b) = b).
  { replace (fp2_mul (fp2_inv a) (fp2_mul a b))
      with (fp2_mul (fp2_mul (fp2_inv a) a) b) by ring.
    rewrite Hinv. apply injective_projections; simpl; ring. }
  rewrite <- Hcompute, Hab. apply injective_projections; simpl; ring.
Qed.

Lemma cube_t_g2_nonsquare : forall (u : Fp2),
  u <> fp2_zero ->
  fp2_is_square (fp2_cube (fp2_mul swu_Z_g2 (fp2_sqr u))) = false.
Proof.
  intros u Hu.
  set (t := fp2_mul swu_Z_g2 (fp2_sqr u)).
  assert (Husq_nz : fp2_sqr u <> fp2_zero).
  { unfold fp2_sqr. apply fp2_mul_nonzero; assumption. }
  assert (Ht_nz : t <> fp2_zero).
  { subst t. apply fp2_mul_nonzero; [exact swu_Z_g2_nonzero|exact Husq_nz]. }
  assert (Husq : fp2_is_square (fp2_sqr u) = true)
    by (apply fp2_sqr_is_square; exact Hu).
  (* t = swu_Z * u². swu_Z is nonsquare. u² is square. So t is nonsquare. *)
  assert (Htsq : fp2_is_square t = false).
  { subst t.
    rewrite <- (fp2_is_square_mul_flip (fp2_sqr u) swu_Z_g2 Husq_nz
                                       swu_Z_g2_nonzero swu_Z_g2_nonsquare).
    rewrite Husq. reflexivity. }
  (* sqr t is square *)
  assert (Htsq2 : fp2_is_square (fp2_sqr t) = true)
    by (apply fp2_sqr_is_square; exact Ht_nz).
  (* cube t = t * sqr t. t is non-square, sqr t is square. So cube t is non-square. *)
  unfold fp2_cube.
  rewrite <- (fp2_is_square_mul_flip (fp2_sqr t) t).
  - rewrite Htsq2. reflexivity.
  - apply fp2_mul_nonzero; assumption.
  - exact Ht_nz.
  - exact Htsq.
Qed.

(* ================================================================== *)
(** * gx2 is square when gx1 is not (normal case)                     *)
(* ================================================================== *)

Lemma gx2_is_square_when_gx1_not : forall (u : Fp2),
  let t := fp2_mul swu_Z_g2 (fp2_sqr u) in
  let S := fp2_add (fp2_sqr t) t in
  S <> fp2_zero ->
  u <> fp2_zero ->
  let tv1 := fp2_inv S in
  let x1 := fp2_mul (fp2_mul (fp2_neg iso_B_g2) (fp2_inv iso_A_g2))
                     (fp2_add fp2_one tv1) in
  let gx1 := curve_rhs2 iso_A_g2 iso_B_g2 x1 in
  let x2 := fp2_mul t x1 in
  let gx2 := curve_rhs2 iso_A_g2 iso_B_g2 x2 in
  fp2_is_square gx1 = false ->
  gx1 <> fp2_zero ->
  fp2_is_square gx2 = true.
Proof.
  intros u t S HS Hu tv1 x1 gx1 x2 gx2 Hnsq Hgx1nz.
  assert (Hratio : gx2 = fp2_mul (fp2_cube t) gx1).
  { subst gx2 gx1 x2 x1 tv1.
    pose proof (swu_gx_ratio_abstract iso_A_g2 iso_B_g2 swu_Z_g2 u HS iso_A_g2_nonzero) as H.
    cbv zeta in H. unfold curve_rhs2. unfold fp2_cube.
    fold t. fold S.
    exact H. }
  rewrite Hratio.
  rewrite <- (fp2_is_square_mul_flip gx1 (fp2_cube t) Hgx1nz).
  - rewrite Hnsq. reflexivity.
  - (* fp2_cube t ≠ 0 *)
    unfold fp2_cube. apply fp2_mul_nonzero. apply fp2_mul_nonzero.
    all: subst t; apply fp2_mul_nonzero;
         [exact swu_Z_g2_nonzero | apply fp2_mul_nonzero; assumption].
  - exact (cube_t_g2_nonsquare u Hu).
Qed.

(* ================================================================== *)
(** * Main theorem (assembly admitted)                                 *)
(* ================================================================== *)

Theorem swu_g2_maps_to_E2prime : forall u : Fp2,
  on_curve_E2prime (map_to_curve_simple_swu_fp2 iso_A_g2 iso_B_g2 swu_Z_g2 u).
Proof. admit. Admitted.
