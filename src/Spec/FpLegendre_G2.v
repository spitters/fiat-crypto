(** * Fp Legendre symbol theory (slim, for G2 hash-to-curve).

    Standalone Fp theory without HashToCurveSWUCompute (which is heavy).
    Provides Fermat's little theorem, Euler criterion, is_square
    characterization, and Legendre multiplicativity. *)

From Stdlib Require Import ZArith Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.HashToCurve.
Require Import Crypto.Spec.HashToCurveFieldSetup.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

(* ================================================================== *)
(** * fp_eqb reflection                                                *)
(* ================================================================== *)

Lemma fp_eqb_true_iff_l : forall (a b : Fp),
  fp_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold fp_eqb. rewrite Z.eqb_eq. split; apply F.eq_to_Z_iff.
Qed.

Lemma fp_eqb_false_iff_l : forall (a b : Fp),
  fp_eqb a b = false <-> a <> b.
Proof.
  intros a b. unfold fp_eqb. rewrite Z.eqb_neq. split.
  - intros H Habs. apply H. apply F.eq_to_Z_iff in Habs. exact Habs.
  - intros H Habs. apply H. apply F.eq_to_Z_iff. exact Habs.
Qed.

(* ================================================================== *)
(** * Nonzero product                                                  *)
(* ================================================================== *)

Lemma mul_nonzero_l : forall (a b : Fp), a <> 0 -> b <> 0 -> a * b <> 0.
Proof.
  intros a b Ha Hb Hab. apply Ha.
  cut (a * (b * F.inv b) = (a * b) * F.inv b). { intro Hassoc.
  cut (b * F.inv b = 1). { intro Hinv.
  cut (a * 1 = a). { intro Hmul1. rewrite <- Hmul1, <- Hinv, Hassoc, Hab. ring. }
  ring. } exact (Fp_mul_inv_r b Hb). } ring.
Qed.

(* ================================================================== *)
(** * Fermat's little theorem                                          *)
(* ================================================================== *)

Lemma fermat_F_l : forall (x : Fp),
  x <> 0 -> F.pow x (Z.to_N (Z.pos p_pos - 1)) = 1.
Proof.
  intros x Hx.
  assert (Hinv : F.inv x * x = 1) by (apply Fp_inv_nonzero; exact Hx).
  assert (Hfermat_inv : F.inv x = F.pow x (Z.to_N (Z.pos p_pos - 2)))
    by (apply (@F.Fq_inv_fermat p_pos p_pos_prime p_pos_gt_2 x)).
  rewrite Hfermat_inv in Hinv.
  replace (F.pow x (Z.to_N (Z.pos p_pos - 2)) * x)
    with (F.pow x (Z.to_N (Z.pos p_pos - 2)) * F.pow x 1) in Hinv
    by (rewrite F.pow_1_r; reflexivity).
  rewrite <- F.pow_add_r in Hinv.
  replace (Z.to_N (Z.pos p_pos - 2) + 1)%N with (Z.to_N (Z.pos p_pos - 1)) in Hinv
    by (vm_compute; reflexivity).
  exact Hinv.
Qed.

(* ================================================================== *)
(** * Power lemmas                                                      *)
(* ================================================================== *)

Lemma pow_square_l : forall (x : Fp) (e : N),
  F.pow x e * F.pow x e = F.pow x (2 * e).
Proof.
  intros. rewrite <- F.pow_add_r. f_equal. lia.
Qed.

Lemma pow_mul_distr_l : forall (a b : Fp) (n : N),
  F.pow (a * b) n = F.pow a n * F.pow b n.
Proof. intros. apply F.pow_mul_l. Qed.

(* ================================================================== *)
(** * Euler test                                                        *)
(* ================================================================== *)

Lemma euler_test_sq_one_l : forall (x : Fp),
  x <> 0 ->
  let v := F.pow x (Z.to_N legendre_exp) in
  v * v = 1.
Proof.
  intros x Hx v. subst v.
  rewrite pow_square_l.
  replace (2 * Z.to_N legendre_exp)%N with (Z.to_N (Z.pos p_pos - 1))
    by (vm_compute; reflexivity).
  exact (fermat_F_l x Hx).
Qed.

Lemma sq_one_cases_l : forall (x : Fp),
  x * x = 1 -> x = 1 \/ x = F.opp 1.
Proof.
  intros x Hsq.
  assert (H : (x - 1) * (x + 1) = 0).
  { replace ((x - 1) * (x + 1)) with (x * x - 1) by ring.
    rewrite Hsq. ring. }
  destruct (F.eq_dec (x - 1) 0) as [Hl|Hl].
  - left. replace x with (x - 1 + 1) by ring. rewrite Hl. ring.
  - right.
    assert (Hx1 : x + 1 = 0).
    { assert (Hstep : F.inv (x - 1) * ((x - 1) * (x + 1)) = 0).
      { rewrite H. ring. }
      replace (F.inv (x - 1) * ((x - 1) * (x + 1)))
        with (F.inv (x - 1) * (x - 1) * (x + 1)) in Hstep by ring.
      rewrite Fp_inv_nonzero in Hstep by exact Hl.
      replace (1 * (x + 1)) with (x + 1) in Hstep by ring.
      exact Hstep. }
    replace x with ((x + 1) - 1) by ring. rewrite Hx1. ring.
Qed.

Lemma euler_test_cases_l : forall (x : Fp),
  x <> 0 ->
  F.pow x (Z.to_N legendre_exp) = 1 \/ F.pow x (Z.to_N legendre_exp) = F.opp 1.
Proof.
  intros x Hx. apply sq_one_cases_l. exact (euler_test_sq_one_l x Hx).
Qed.

(* ================================================================== *)
(** * is_square characterization                                       *)
(* ================================================================== *)

Lemma is_square_true_iff_l : forall (x : Fp),
  is_square x = true <-> (x = 0 \/ F.pow x (Z.to_N legendre_exp) = 1).
Proof.
  intros x. unfold is_square. split.
  - intro H.
    destruct (fp_eqb (F.pow x (Z.to_N legendre_exp)) 1) eqn:He.
    + right. apply fp_eqb_true_iff_l in He. exact He.
    + destruct (fp_eqb x 0) eqn:Hz; [|discriminate].
      left. apply fp_eqb_true_iff_l in Hz. exact Hz.
  - intros [Hz | He].
    + rewrite Hz. unfold is_square.
      destruct (fp_eqb (F.pow 0 (Z.to_N legendre_exp)) 1) eqn:He'.
      * reflexivity.
      * destruct (fp_eqb 0 0) eqn:Hz'.
        -- reflexivity.
        -- apply fp_eqb_false_iff_l in Hz'. exfalso. apply Hz'. reflexivity.
    + rewrite (proj2 (fp_eqb_true_iff_l _ _) He). reflexivity.
Qed.

Lemma is_square_false_iff_l : forall (x : Fp),
  is_square x = false <-> (x <> 0 /\ F.pow x (Z.to_N legendre_exp) <> 1).
Proof.
  intros x.
  rewrite <- Bool.not_true_iff_false, is_square_true_iff_l.
  split.
  - intro H. split.
    + intro Hz. apply H. left. exact Hz.
    + intro He. apply H. right. exact He.
  - intros [Hx He] [Hz | He']; [exact (Hx Hz) | exact (He He')].
Qed.

(* ================================================================== *)
(** * Legendre multiplicativity                                        *)
(* ================================================================== *)

Lemma is_square_mul_flip_l : forall (a c : Fp),
  a <> 0 -> c <> 0 ->
  is_square c = false ->
  negb (is_square a) = is_square (c * a).
Proof.
  intros a c Ha Hc Hcsq.
  apply is_square_false_iff_l in Hcsq. destruct Hcsq as [_ Hce].
  assert (Hcm1 : F.pow c (Z.to_N legendre_exp) = F.opp 1).
  { destruct (euler_test_cases_l c Hc) as [H1|Hm1]; [contradiction | exact Hm1]. }
  assert (Hca : F.pow (c * a) (Z.to_N legendre_exp) =
                F.opp 1 * F.pow a (Z.to_N legendre_exp)).
  { rewrite pow_mul_distr_l. rewrite Hcm1. reflexivity. }
  assert (Hca_nz : c * a <> 0) by (apply mul_nonzero_l; assumption).
  destruct (is_square a) eqn:Hasq; simpl negb.
  - apply is_square_true_iff_l in Hasq. destruct Hasq as [Hz|Hae].
    { exfalso. exact (Ha Hz). }
    symmetry. apply is_square_false_iff_l. split; [exact Hca_nz|].
    rewrite Hca, Hae. replace (F.opp 1 * 1) with (F.opp 1 : Fp) by ring.
    intro Habs.
    assert (Hbad : F.to_Z (F.opp (1 : Fp)) = F.to_Z (1 : Fp)).
    { f_equal. exact Habs. }
    revert Hbad. vm_compute. discriminate.
  - apply is_square_false_iff_l in Hasq. destruct Hasq as [_ Hane].
    assert (Ham1 : F.pow a (Z.to_N legendre_exp) = F.opp 1).
    { destruct (euler_test_cases_l a Ha) as [H1|Hm1]; [contradiction | exact Hm1]. }
    symmetry. apply is_square_true_iff_l. right.
    rewrite Hca, Ham1. ring.
Qed.
