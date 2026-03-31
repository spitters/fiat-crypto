Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.TCSignExtend.
Require Import Crypto.Arithmetic.BYInv.EvalLemmas.
Require Import Crypto.Arithmetic.BYInv.Firstn.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementMul.
Require Import Crypto.Util.ZUtil.SignExtend.
Require Import Crypto.Util.ListUtil.

Require Import Crypto.Util.ZUtil.Tactics.SolveRange.

Import ListNotations.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Lemma sat_mul_bounds machine_wordsize n1 n2 f g
      (mw0 : 0 < machine_wordsize)
      (Hn2 : (0 < n2)%nat)
      (Hf : length f = n1)
      (Hg : length g = n1) :
  in_bounded machine_wordsize (sat_mul machine_wordsize n1 n2 f g).
Proof.
  intros z H; unfold sat_mul in *.
  rewrite Rows.mul_partitions in * by (try apply uwprops; try apply Z.pow_nonzero; lia).
  unfold partition in H. apply ListAux.in_map_inv in H.
  destruct H as [a [H]]. rewrite H0, !uweight_eq_alt; try lia.
  split.
  - apply Z.div_le_lower_bound;
      ring_simplify; try apply Z.mod_pos_bound;
        apply Z.pow_pos_nonneg; try lia; apply Z.pow_pos_nonneg; lia.
  - apply Z.div_lt_upper_bound.
    apply Z.pow_pos_nonneg; try lia; apply Z.pow_pos_nonneg; lia.
    replace ((_ ^ _) ^ _ * _) with ((2 ^ machine_wordsize) ^ Z.of_nat (S a)).
    apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; try lia; apply Z.pow_pos_nonneg; lia.
    rewrite Z.mul_comm, Pow.Z.pow_mul_base;
      try (replace (Z.of_nat (S a)) with ((Z.of_nat a + 1)) by lia; lia). Qed.

Lemma sat_mul_length machine_wordsize n1 n2 f g
      (mw0 : 0 < machine_wordsize)
      (Hn2 : (0 < n2)%nat)
      (Hf : length f = n1)
      (Hg : length g = n1) :
  length (sat_mul machine_wordsize n1 n2 f g) = n2.
Proof.
  unfold sat_mul. rewrite Rows.length_mul by (try apply uwprops; assumption). reflexivity. Qed.

Lemma tc_mul_length machine_wordsize na nb nab f g
      (mw0 : 0 < machine_wordsize)
      (Hna : (0 < na <= nab)%nat)
      (Hnb : (0 < nb <= nab)%nat)
      (Hf : length f = na)
      (Hg : length g = nb) :
  length (tc_mul machine_wordsize na nb nab f g) = nab.
Proof.
  unfold tc_mul. rewrite firstn_length, Rows.length_mul. lia.
  apply uwprops; lia. all: apply sat_sign_extend_length; lia.
Qed.

Theorem tc_mul_correct m na nb nab a b
        (Hm : 0 < m)
        (Hna : (0 < na <= nab)%nat)
        (Hnb : (0 < nb <= nab)%nat)
        (Ha : length a = na)
        (Hb : length b = nb)
        (Ha2 : in_bounded m a)
        (Hb2 : in_bounded m b)
        (Hab_overflow : - 2 ^ (m * Z.of_nat nab - 1) <=
                        tc_eval m na a * tc_eval m nb b <
                        2 ^ (m * Z.of_nat nab - 1)) :
  tc_eval m (nab) (tc_mul m na nb nab a b) =
  (tc_eval m na a) * (tc_eval m nb b).
Proof.
  pose proof (uwprops m Hm).
  pose proof (eval_bound m na a Hm Ha2 Ha).
  pose proof (eval_bound m nb b Hm Hb2 Hb).
  unfold tc_mul, tc_eval in *.
  rewrite (firstn_eval m (2 * nab)), Rows.mul_partitions, !sat_sign_extend_eval, Partition.eval_partition, Z.twos_complement_mod.
  rewrite Z.mod_small.
  fold (Z.twos_complement_mul_aux (m * na) (m * nb) (m * nab) (eval (uweight m) na a) (eval (uweight m) nb b)).
  rewrite Z.twos_complement_mul_aux_spec by nia. reflexivity.
  pose proof (Z.sign_extend_bound (m * na) (m * nab) (eval (uweight m) na a) ltac:(nia) ltac:(nia) ltac:(assumption)).
  pose proof (Z.sign_extend_bound (m * nb) (m * nab) (eval (uweight m) nb b) ltac:(nia) ltac:(nia) ltac:(assumption)).
  rewrite uweight_eq_alt.
  replace ((2 ^ m) ^ Z.of_nat (2 * nab)) with (2 ^ (m * Z.of_nat nab) * 2 ^ (m * Z.of_nat nab)) by
      (rewrite <- Z.pow_mul_r, <- Z.pow_add_r by nia; apply f_equal; nia). all: try nia; try assumption.
  distr_length. distr_length.
  apply Rows.length_mul; try assumption; distr_length.
  apply sat_mul_bounds; distr_length; lia.
Qed.


Lemma tc_mul_full_length machine_wordsize na nb f g
      (mw0 : 0 < machine_wordsize)
      (Hna : (0 < na)%nat)
      (Hnb : (0 < nb)%nat)
      (Hf : length f = na)
      (Hg : length g = nb) :
  length (tc_mul_full machine_wordsize na nb f g) = (na + nb)%nat.
Proof. unfold tc_mul_full. apply tc_mul_length; lia. Qed.

Lemma tc_eval_bounds m n a
        (Hm : 0 < m)
        (Hn : (0 < n)%nat) :
  - 2 ^ (m * Z.of_nat n - 1) <= tc_eval m n a < 2 ^ (m * Z.of_nat n - 1).
Proof. unfold tc_eval; apply Z.twos_complement_bounds; nia. Qed.

Theorem tc_mul_full_correct m na nb a b
        (Hm : 0 < m)
        (Hna : (0 < na)%nat)
        (Hnb : (0 < nb)%nat)
        (Ha : length a = na)
        (Hb : length b = nb)
        (Ha2 : in_bounded m a)
        (Hb2 : in_bounded m b) :
  tc_eval m (na + nb) (tc_mul_full m na nb a b) =
  (tc_eval m na a) * (tc_eval m nb b).
Proof.
  unfold tc_mul_full; apply tc_mul_correct; try assumption; try lia.
  pose proof (tc_eval_bounds m na a).
  pose proof (tc_eval_bounds m nb b).
  assert (2 ^ (m * Z.of_nat na - 1) * 2 ^ (m * Z.of_nat nb - 1) < 2 ^ (m * Z.of_nat (na + nb) - 1)) by
      (rewrite <- Z.pow_add_r by nia; apply Z.pow_lt_mono_r; nia).
  nia.
Qed.

Lemma tc_mul_full_bounds m na nb a b
        (Hm : 0 < m)
        (Hna : (0 < na)%nat)
        (Hnb : (0 < nb)%nat)
        (Ha : length a = na)
        (Hb : length b = nb)
        (Ha2 : in_bounded m a)
        (Hb2 : in_bounded m b) :
 - 2 ^ (m * Z.of_nat (na + nb) - 1) <= tc_eval m (na + nb) (tc_mul_full m na nb a b) < 2 ^ (m * Z.of_nat (na + nb) - 1).
Proof.
  pose proof (tc_eval_bounds m na a).
  pose proof (tc_eval_bounds m nb b).
  assert (2 ^ (m * Z.of_nat na - 1) * 2 ^ (m * Z.of_nat nb - 1) < 2 ^ (m * Z.of_nat (na + nb) - 1)) by
    (rewrite <- Z.pow_add_r by nia; apply Z.pow_lt_mono_r; nia).
  rewrite tc_mul_full_correct by assumption. nia.
Qed.

Lemma word_tc_mul_length m n a b
        (Hm : 0 < m)
        (Hn : (0 < n)%nat)
        (Ha : 0 <= a < 2 ^ m)
        (Hb : length b = n) :
  length (word_tc_mul m n a b) = (1 + n)%nat.
Proof. unfold word_tc_mul; apply tc_mul_full_length; try lia; reflexivity. Qed.

Theorem word_tc_mul_correct m n a b
        (Hm : 0 < m)
        (Hn : (0 < n)%nat)
        (Ha : 0 <= a < 2 ^ m)
        (Hb : length b = n)
        (Hb2 : in_bounded m b) :
  tc_eval m (1 + n) (word_tc_mul m n a b) =
  (Z.twos_complement m a) * tc_eval m n b.
Proof.
  unfold word_tc_mul.
  replace (Z.twos_complement m a) with (tc_eval m 1 [a]).
  apply tc_mul_full_correct; try assumption; try lia; try reflexivity.
  intros z Hin; destruct Hin as [|[]]; subst; assumption.
  unfold tc_eval.
  apply f_equal2; [lia|]; rewrite eval_cons, uweight_0, uweight_eval_shift, eval_nil, uweight_1; try reflexivity; lia.
Qed.

Lemma word_tc_mul_bounds m n a b
        (Hm : 0 < m)
        (Hn : (0 < n)%nat)
        (Ha : 0 <= a < 2 ^ m)
        (Hb : length b = n)
        (Hb2 : in_bounded m b) :
    - 2 ^ (m * Z.of_nat (1 + n) - 1) <= tc_eval m (1 + n) (word_tc_mul m n a b) < 2 ^ (m * Z.of_nat (1 + n) - 1).
Proof.
  unfold word_tc_mul.
  apply tc_mul_full_bounds; try assumption; try lia.
  reflexivity. intros z H. inversion H. subst; assumption. easy.
Qed.
