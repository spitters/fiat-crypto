Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.

Lemma partition_1 machine_wordsize n : (0 < machine_wordsize) -> (0 < n)%nat -> Partition.partition (uweight machine_wordsize) n 1 = one n.
Proof.
  destruct n.
  - lia.
  - induction n.
    + unfold Partition.partition; intros.
      simpl.
      rewrite !uweight_eq_alt', Z.mul_0_r, Z.pow_0_r, Z.div_1_r, Z.mul_1_r, Z.mod_1_l.
      reflexivity.
      apply Z.pow_gt_1. lia. assumption.
    + intros.
      assert (1 < uweight machine_wordsize (S n)).
      { rewrite uweight_eq_alt'. apply Z.pow_gt_1; nia. }
      assert (1 < uweight machine_wordsize (S (S n))).
      { rewrite uweight_eq_alt'. apply Z.pow_gt_1; nia. }
      rewrite partition_step, Z.mod_small, Z.div_1_l.
      rewrite IHn.
      unfold one.
      simpl. rewrite Nat.sub_0_r.
      all: try lia.
      unfold zeros.
      rewrite <- repeat_cons.
      reflexivity.
Qed.

Lemma length_one n (Hn : (0 < n)%nat) :
  length (one n) = n.
Proof. unfold one; simpl; rewrite length_zeros; lia. Qed.

Hint Rewrite length_one : distr_length.

Lemma eval_one n machine_wordsize
      (Hn : (0 < n)%nat)
      (Hmw : 0 <= machine_wordsize) :
  eval (uweight machine_wordsize) n (one n) = 1.
Proof.
  unfold one. destruct n. lia.
  rewrite eval_cons, uweight_eval_shift, uweight_0, uweight_1 by (try rewrite length_zeros; lia).
  replace (S n - 1)%nat with n by lia. rewrite eval_zeros; lia.
Qed.
