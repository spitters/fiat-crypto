Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.TwosComplementNeg.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.
Require Import Crypto.Util.ZUtil.TwosComplement.

Require Import Crypto.Util.LetIn.

Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Import Positional.
Import UnsaturatedSolinas.

Local Open Scope Z_scope.

Module UnsaturatedSolinas.

  Lemma length_addmod limbwidth_num limbwidth_den n :
    forall f, length f = n -> forall g, length g = n -> length (addmod limbwidth_num limbwidth_den n f g) = n.
  Proof. intros; apply length_add; assumption. Qed.

  Lemma length_oppmod limbwidth_num limbwidth_den n balance :
    length balance = n ->
    forall f, length f = n -> length (oppmod limbwidth_num limbwidth_den n balance f) = n.
  Proof. intros; apply length_opp; assumption. Qed.

  Lemma length_carrymod limbwidth_num limbwidth_den s c n idxs :
    forall f, length f = n ->
         length (carrymod limbwidth_num limbwidth_den s c n idxs f) = n.
  Proof. intros; unfold carrymod; apply length_chained_carries; assumption. Qed.

  Lemma length_mulmod weight s c n f g :
    length (mulmod weight s c n f g) = n.
  Proof. intros; unfold mulmod; apply Positional.length_from_associational. Qed.

  Lemma length_carry_mulmod limbwidth_num limbwidth_den s c n idxs :
    forall f, length f = n ->
         forall g, length g = n ->
    length (carry_mulmod limbwidth_num limbwidth_den s c n idxs f g) = n.
  Proof. intros. unfold carry_mulmod. apply Positional.length_chained_carries. apply length_mulmod. Qed.

  Lemma length_encodemod limbwidth_num limbwidth_den s c n a :
    length (encodemod limbwidth_num limbwidth_den s c n a) = n.
  Proof. unfold encodemod. apply Positional.length_encode. Qed.

  Lemma eval_one limbwidth_num limbwidth_den n :
    (0 < limbwidth_den <= limbwidth_num) ->
    (0 < n)%nat ->
    eval (weight limbwidth_num limbwidth_den) n (one n) = 1.
  Proof.
    unfold one.
    destruct n.
    - lia.
    - intros.
      rewrite Positional.eval_cons.
      rewrite weight_0.
      replace (S n - 1)%nat with n by lia.
      rewrite Positional.eval_zeros. lia.
      apply wprops. assumption.
      simpl.
      rewrite Nat.sub_0_r.
      apply length_zeros.
  Qed.

  Lemma word_to_solina_length limbwidth_num limbwidth_den machine_wordsize s c n idxs balance a :
    (length balance = n) ->
    length (word_to_solina limbwidth_num limbwidth_den machine_wordsize s c n idxs balance a) = n.
  Proof.
    intros. unfold word_to_solina.
    rewrite !unfold_Let_In; rewrite Positional.length_select with (n:=n); auto.
    apply length_encodemod. apply length_carrymod.
    apply length_oppmod. assumption. apply length_encodemod.
  Qed.

  Lemma eval_word_to_solina limbwidth_num limbwidth_den machine_wordsize s c n idxs balance a
        (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
        (m_big : 2 ^ machine_wordsize < s - Associational.eval c)
        (m_nz:s - Associational.eval c <> 0)
        (s_nz:s <> 0)
        (Hmw : 0 < machine_wordsize)
        (Hn : (1 < n)%nat)
        (Ha : 0 <= a < 2 ^ machine_wordsize)
        (length_balance : length balance = n)
        (eval_balance : eval (weight limbwidth_num limbwidth_den) n balance mod (s - Associational.eval c) = 0)
    :
    eval (weight limbwidth_num limbwidth_den) n (word_to_solina limbwidth_num limbwidth_den machine_wordsize s c n idxs balance a) mod (s - Associational.eval c) =
      Z.twos_complement machine_wordsize a mod (s - Associational.eval c).
  Proof.
      unfold word_to_solina.
      rewrite Z.twos_complement_neg_spec.
      rewrite !unfold_Let_In.
      rewrite Positional.select_eq with (n:=n).

      unfold Z.twos_complement.
      rewrite Z.twos_complement_cond_equiv.

      destruct (Z.testbit a (machine_wordsize - 1)) eqn:E. cbn -[Partition.partition oppmod].

      rewrite eval_carrymod.
      rewrite eval_oppmod.
      push_Zmod.
      rewrite eval_encodemod.
      pull_Zmod.
      rewrite Z.twos_complement_opp'_opp.
      rewrite Z.twos_complement_opp_correct.

      destruct (Decidable.dec (a = 0)). subst. rewrite Z.bits_0 in E. inversion E.
      pose proof Z.mod_pos_bound a (2 ^ machine_wordsize) ltac:(lia).
      pose proof Z.mod_pos_bound (- a) (2 ^ machine_wordsize) ltac:(lia).

      rewrite Z.mod_opp_small.
      rewrite Z.mod_opp_small.
      replace (a mod 2 ^ machine_wordsize - 2 ^ machine_wordsize) with (- (2 ^ machine_wordsize - (a mod 2 ^ machine_wordsize))) by lia.
      rewrite Z.mod_opp_small.
      rewrite Z.mod_small. lia. lia.
      pose proof Z.mod_pos_bound a (2 ^ machine_wordsize) ltac:(lia).

      lia.  lia.

      rewrite (Z.mod_opp_small a). lia. lia.

      all: try lia; try assumption; unfold encodemod, oppmod; auto with distr_length.

      simpl.
      pose proof wprops limbwidth_num limbwidth_den limbwidth_good. destruct H.
      rewrite Positional.eval_encode. rewrite (Z.mod_small _ (2 ^ _)).

      reflexivity.
      all: auto.

      intros. unfold weight. apply Z.pow_nonzero. lia.
      apply Z.opp_nonneg_nonpos.
      apply Z.div_le_upper_bound. lia. nia. lia. intros. specialize (weight_divides i). lia.

      unfold carrymod; auto with distr_length.
    Qed.
End UnsaturatedSolinas.
