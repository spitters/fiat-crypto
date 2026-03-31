Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ListUtil.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

(**************************************************************************************** *)
(** Properties of the twos-complement multi-limb addtion including functional correctness *)
(**************************************************************************************** *)

Lemma eval_tc_add machine_wordsize n f g (mw0 : 0 < machine_wordsize) (Hf : length f = n) (Hg : length g = n) :
  eval (uweight machine_wordsize) n (tc_add machine_wordsize n f g) =
  (eval (uweight machine_wordsize) n f + eval (uweight machine_wordsize) n g) mod (2^(machine_wordsize * n)).
Proof.
  unfold tc_add.
  rewrite Rows.add_partitions;
    rewrite ?Partition.eval_partition; try assumption; try apply (uwprops machine_wordsize mw0).
  rewrite uweight_eq_alt'; reflexivity.
Qed.

Lemma length_tc_add machine_wordsize n f g
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = n)
      (Hg : length g = n) :
  length (tc_add machine_wordsize n f g) = n.
Proof.
  unfold tc_add, Rows.add.
  autorewrite with distr_length. reflexivity.
  apply (uwprops machine_wordsize mw0).
  intros row H; destruct H as [|[H|[]]]; subst; auto.
Qed.

Hint Rewrite length_tc_add : length_distr.

Lemma tc_add_in_bounded machine_wordsize n f g
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = n)
      (Hg : length g = n) :
  in_bounded machine_wordsize (tc_add machine_wordsize n f g).
Proof.
  pose proof uwprops machine_wordsize mw0.
  intros z Hin; unfold tc_add in *; rewrite Rows.add_partitions in *; auto.
  unfold partition in Hin. apply ListAux.in_map_inv in Hin.
  destruct Hin as [a [Hin]].
  rewrite H0, !uweight_eq_alt by lia. split.
  - apply Z.div_le_lower_bound;
      ring_simplify; try apply Z.mod_pos_bound;
        apply Z.pow_pos_nonneg; try apply Z.pow_pos_nonneg; lia.
  - apply Z.div_lt_upper_bound.
    apply Z.pow_pos_nonneg; try apply Z.pow_pos_nonneg; lia.
    replace ((_ ^ _) ^ _ * _) with ((2 ^ machine_wordsize) ^ Z.of_nat (S a)).
    apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; try apply Z.pow_pos_nonneg; lia.
    rewrite Z.mul_comm, Pow.Z.pow_mul_base;
      try (replace (Z.of_nat (S a)) with ((Z.of_nat a + 1)) by lia; lia).
Qed.

Lemma tc_eval_tc_add machine_wordsize n f g
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hf : length f = n)
      (Hg : length g = n)
      (overflow_f : - 2 ^ (machine_wordsize * n - 2) < tc_eval machine_wordsize n f < 2 ^ (machine_wordsize * n - 2))
      (overflow_g : - 2 ^ (machine_wordsize * n - 2) < tc_eval machine_wordsize n g < 2 ^ (machine_wordsize * n - 2)) :
  tc_eval machine_wordsize n (tc_add machine_wordsize n f g) =
  tc_eval machine_wordsize n f + tc_eval machine_wordsize n g.
Proof.
  assert (0 < Z.of_nat n) by lia; unfold tc_eval in *.
  rewrite eval_tc_add, <- Z.twos_complement_add_weak, Z.twos_complement_mod; nia.
Qed.

Lemma tc_eval_tc_add_full machine_wordsize n f g
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hf : length f = n)
      (Hg : length g = n)
      (bounds : - 2 ^ (machine_wordsize * n - 1) < tc_eval machine_wordsize n f + tc_eval machine_wordsize n g <
                    2 ^ (machine_wordsize * n - 1)) :
  tc_eval machine_wordsize n (tc_add machine_wordsize n f g) =
  tc_eval machine_wordsize n f + tc_eval machine_wordsize n g.
Proof.
  assert (0 < Z.of_nat n) by lia; unfold tc_eval in *.
  rewrite eval_tc_add, <- Z.twos_complement_add_full, Z.twos_complement_mod; nia.
Qed.
