Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.WordByWordMontgomery.

Require Import Crypto.Arithmetic.BYInv.ArithmeticShiftr.
Require Import Crypto.Arithmetic.BYInv.TCAdd.
Require Import Crypto.Arithmetic.BYInv.EvalLemmas.
Require Import Crypto.Arithmetic.BYInv.Divstep.
Require Import Crypto.Arithmetic.BYInv.Ref.
Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.Ones.
Require Import Crypto.Arithmetic.BYInv.TCSignBit.
Require Import Crypto.Arithmetic.BYInv.TCSignExtend.
Require Import Crypto.Arithmetic.BYInv.TCMul.
Require Import Crypto.Arithmetic.BYInv.Firstn.
Require Import Crypto.Arithmetic.BYInv.Divstep.
Require Import Crypto.Arithmetic.BYInv.Zero.
Require Import Crypto.Arithmetic.BYInv.One.
Require Import Crypto.Arithmetic.BYInv.Hints.

Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Odd.
Require Import Crypto.Util.ZUtil.ArithmeticShiftr.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementNeg.
Require Import Crypto.Util.ZUtil.TwosComplementPos.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.
Require Import Crypto.Util.ZUtil.ModExp.
Require Import Crypto.Arithmetic.ModOps.

Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Import ListNotations.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.


(* TODO: Move thise *)
Lemma fold_right_fold_left_lemma {A B : Type} (f : B -> A -> A) (l s : list B) (a : A) :
  (forall x x' y, f x y = f x' y) -> length l = length s -> fold_left (fun i j => f j i) l a = fold_right f a s.
Proof.
  rewrite <- fold_left_rev_right. revert s a.
  induction l; intros; simpl.
  - assert (s = []) by (destruct s; simpl in *; try lia; reflexivity); subst. reflexivity.
  - rewrite fold_right_snoc. replace s with (rev (rev s)) by (apply rev_involutive).
    destruct (rev s) eqn:E.
    apply (f_equal (@rev B)) in E. rewrite rev_involutive in E. subst. simpl in *. lia.
    simpl. rewrite fold_right_snoc.
    replace (f a a0) with (f b a0). apply IHl. assumption.
    apply (f_equal (@length B)) in E. simpl in *.
    rewrite rev_length in *. lia. apply H.
Qed.

Lemma pow_ineq k : (2 <= k)%nat -> k + 2 <= Zpower_nat 2 k.
Proof. induction k as [|[|[|k]]]; [lia|lia|simpl; lia|rewrite Zpower_nat_succ_r; lia]; intros. Qed.

Lemma pow_ineq_Z k : 2 <= k -> k + 2 <= 2 ^ k.
Proof. intros. replace k with (Z.of_nat (Z.to_nat k)) by lia. rewrite <- Zpower_nat_Z. apply pow_ineq; lia. Qed.

Lemma tc_eval_mod2m machine_wordsize tc_limbs f :
  (0 < machine_wordsize) -> (0 < tc_limbs)%nat ->
  tc_eval machine_wordsize tc_limbs f mod 2 ^ machine_wordsize = Positional.eval (uweight machine_wordsize) tc_limbs f mod 2 ^ machine_wordsize.
Proof.
  intros. unfold tc_eval.
  rewrite Z.twos_complement_mod_smaller_pow. reflexivity. nia.
Qed.

Module WordByWordMontgomery.

  Import WordByWordMontgomery.WordByWordMontgomery.
  Import Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
  Import BYInv.WordByWordMontgomery.

  Section __.

    Context
      (machine_wordsize : Z)
      (tc_limbs : nat)
      (mont_limbs : nat)
      (word_tc_mul_limbs : nat)
      (m : Z)
      (m_bounds : 2 ^ machine_wordsize < m < (2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs))
      (r' : Z)
      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m' : Z)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (mw2 : 2 < machine_wordsize)
      (tc_limbs0 : (0 < tc_limbs)%nat)
      (mont_limbs1 : (1 < mont_limbs)%nat)
      (word_tc_mul_limbs_eq : (word_tc_mul_limbs = 1 + tc_limbs)%nat).

    #[local] Notation jump_divstep := (jump_divstep machine_wordsize mont_limbs tc_limbs word_tc_mul_limbs m m').
    #[local] Notation eval := (@WordByWordMontgomery.eval machine_wordsize mont_limbs).
    #[local] Notation tc_eval := (tc_eval machine_wordsize tc_limbs).
    #[local] Notation tc := (Z.twos_complement machine_wordsize).
    #[local] Notation jump_divstep_aux := (jump_divstep_aux machine_wordsize mont_limbs tc_limbs word_tc_mul_limbs m m').
    #[local] Notation valid := (WordByWordMontgomery.valid machine_wordsize mont_limbs m).
    #[local] Notation tc_wtmne := (twosc_word_mod_m machine_wordsize mont_limbs m).
    #[local] Notation mulmod := (mulmod machine_wordsize mont_limbs m m').
    #[local] Notation oppmod := (oppmod machine_wordsize mont_limbs m).
    #[local] Notation from_montgomerymod := (from_montgomerymod machine_wordsize mont_limbs m m').
    #[local] Notation in_bounded := (in_bounded machine_wordsize).

    #[local] Hint Resolve
         (length_addmod machine_wordsize mont_limbs m ltac:(lia))
         (length_oppmod machine_wordsize mont_limbs m ltac:(lia))
         (length_mulmod machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (length_twosc_word_mod_m machine_wordsize mont_limbs m ltac:(lia))
      : len.

    #[local] Hint Resolve
         (zero_valid machine_wordsize mont_limbs m ltac:(lia))
         (addmod_valid machine_wordsize mont_limbs m r' m' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (oppmod_valid machine_wordsize mont_limbs m r' m' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (mulmod_valid machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (twosc_word_mod_m_valid machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia))
      : valid.

    Ltac t := repeat match goal with
                     | |- valid _ => auto with valid
                     | |- length _ = _ => auto with len
                     | |- in_bounded _ => auto with in_bounded
                     | |- _ => assumption
                     | |- _ => lia
                     | |- context[tc] => autorewrite with Ztc
                     | |- context[tc_eval] => autorewrite with tc
                     end.

    (** Correctness of outer loop body  *)
    Theorem jump_divstep_correct d f g v r
            (f_odd : Z.odd (tc_eval f) = true)
            (Hf : length f = tc_limbs)
            (Hg : length g = tc_limbs)
            (d_bounds : - (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2)) < tc d <
                          2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2))
            (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
            (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
            (f_in_bounded : in_bounded f)
            (g_in_bounded : in_bounded g)
            (Hr : valid r)
            (Hv : valid v) :
      let '(d1,f1,g1,v1,r1) := jump_divstep_aux (d, f, g, v, r) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m)
      = jump_divstep_vr (Z.to_nat (machine_wordsize - 2)) machine_wordsize m
                        (tc d, tc_eval f, tc_eval g, (eval v * r' ^ (Z.of_nat mont_limbs)) mod m, (eval r * r' ^ (Z.of_nat mont_limbs)) mod m).
    Proof.
      pose proof (pow_ineq_Z (machine_wordsize - 1) ltac:(lia)).

      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).
      assert (0 < 2 ^ (machine_wordsize - 1))
        by (apply Z.pow_pos_nonneg; lia).
      assert (0 < 2 ^ (machine_wordsize - 2))
        by (apply Z.pow_pos_nonneg; lia).
      assert (2 ^ (machine_wordsize - 2) * 2 = 2 ^ (machine_wordsize - 1))
        by (rewrite Z.mul_comm, Z.pow_mul_base by lia; apply f_equal2; lia).
      assert (2 * (2 * (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) * 2 ^ (machine_wordsize - 1))) = 2 ^ (machine_wordsize * (Z.of_nat (1 + tc_limbs)) - 1))
        by (rewrite <- Zpower_exp, !Z.pow_mul_base by nia; apply f_equal2; nia).

      unfold jump_divstep_aux.
      unshelve epose proof twos_complement_word_full_divstep_iter_correct (machine_wordsize) d (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
      all: t.
      { rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=tc_limbs); t.
        unfold tc_eval in f_odd.
        rewrite Z.twos_complement_odd in f_odd by nia.
        rewrite Z.odd_mod2m by lia. assumption. }
      { replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in *; lia. }
      { apply nth_default_preserves_properties; auto; lia. }
      { apply nth_default_preserves_properties; auto; lia. }

      unshelve epose proof twos_complement_word_full_divsteps_bounds (machine_wordsize) d (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _.
      all: t.
      { replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in *; lia. }
      { rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=tc_limbs); t.
        unfold tc_eval in f_odd.
        rewrite Z.twos_complement_odd in f_odd by nia.
        rewrite Z.odd_mod2m by lia. assumption. }

      unfold jump_divstep_vr.
      replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in * by lia.

      rewrite Z.twos_complement_one, Z.twos_complement_zero in * by lia.

      rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.
      destruct fold_left as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1.

      destruct H6 as [u1_bounds [v1_bounds [q1_bounds [r1_bounds [u1_pos [v1_pos [q1_pos r1_pos]]]]]]].

      rewrite !tc_eval_mod2m by t.
      rewrite <- !eval_nth_default_0 by t.

      set (f0 := nth_default 0 f 0) in *.
      set (g0 := nth_default 0 g 0) in *.

      destruct Nat.iter as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''] eqn:E3.

      assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; nia).

      rewrite !unfold_Let_In by t.
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      + congruence.
      + rewrite word_tc_mul_limbs_eq in *.
        rewrite firstn_tc_eval_small with (n:=(1 + tc_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full, !word_tc_mul_correct; t. inversion H5. reflexivity.
        rewrite !word_tc_mul_correct; t. nia.
        eapply tc_eval_arithmetic_shiftr_bounds; t. nia. nia.
        rewrite tc_eval_tc_add_full, !word_tc_mul_correct, Z.pow_add_r; t. nia. nia.
        rewrite !word_tc_mul_correct; t. nia.
      + rewrite word_tc_mul_limbs_eq in *.
        rewrite firstn_tc_eval_small with (n:=(1 + tc_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full, !word_tc_mul_correct; t. inversion H5. reflexivity.
        rewrite !word_tc_mul_correct; t. nia.
        eapply tc_eval_arithmetic_shiftr_bounds; t. nia. nia.
        rewrite tc_eval_tc_add_full, !word_tc_mul_correct, Z.pow_add_r; t. nia. nia.
        rewrite !word_tc_mul_correct; t. nia.
      + rewrite eval_addmod' by t. push_Zmod.
        rewrite !eval_mulmod' with (r':=r') by t. push_Zmod.
        rewrite !(eval_twosc_word_mod_m _ _ _ r' m') by t.
        inversion H5. push_Zmod; pull_Zmod.
        apply f_equal2; lia.
      + rewrite eval_addmod' by t. push_Zmod.
        rewrite !eval_mulmod' with (r':=r') by t. push_Zmod.
        rewrite !(eval_twosc_word_mod_m _ _ _ r' m') by t. pull_Zmod.
        inversion H5.
        apply f_equal2; lia.
    Qed.

    Lemma jump_divstep_invariants d f g v r
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (f_odd : Z.odd (tc_eval f) = true)
          (d_bounds : - (2 ^ (machine_wordsize - 1) - (machine_wordsize - 2) - 1) < tc d < 2 ^ (machine_wordsize - 1) - (machine_wordsize - 2) - 1)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := jump_divstep_aux (d,f,g,v,r) in
      length f1 = tc_limbs
      /\ length g1 = tc_limbs
      /\ length v1 = mont_limbs
      /\ length r1 = mont_limbs
      /\ valid v1
      /\ valid r1
      /\ in_bounded f1
      /\ in_bounded g1.
    Proof.
      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).

      unfold jump_divstep_aux.

      unshelve epose proof twos_complement_word_full_divsteps_bounds machine_wordsize d (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _.
      all: (t; try nia).
      { replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2); lia. }
      { rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=tc_limbs), Z.odd_mod2m by (assumption || lia).
        rewrite <- Z.twos_complement_odd with (m:=machine_wordsize * tc_limbs); (assumption || nia). }

      rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.
      destruct (fold_left _ (seq 0 (Z.to_nat _))) as [[[[[[dn fn] gn] un] vn] qn] rn].
      rewrite !word_tc_mul_limbs_eq.

      simpl. repeat (split; t).
    Qed.

    Lemma jump_divstep_invariants2 d f g v r Kd
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (f_odd : Z.odd (tc_eval f) = true)
          (Kd_bounds : 0 <= Kd < (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2)))
          (d_bounds : - Kd < tc d < Kd)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := jump_divstep_aux (d,f,g,v,r) in
      Z.odd (tc_eval f1) = true
      /\ - (Kd + (machine_wordsize - 2)) < tc d1 < Kd + (machine_wordsize - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g1 < 2 ^ (machine_wordsize * tc_limbs - 2).
    Proof.
      unshelve epose proof jump_divstep_correct d f g v r _ _ _ _ _ _ _ _ _ _; try assumption; try lia.
      unshelve epose proof jump_divstep_vr_invariants (Z.to_nat (machine_wordsize - 2)) machine_wordsize m (tc d)
               (tc_eval f) (tc_eval g) ((eval v * r' ^ Z.of_nat mont_limbs) mod m) ((eval r * r' ^ Z.of_nat mont_limbs) mod m)
               Kd (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2)) _ _ _ _ _ _ _ _; try assumption; try lia;
        try (apply Z.mod_pos_bound; lia).
      destruct jump_divstep_aux as [[[[d1 f1]g1]v1]r1].
      destruct jump_divstep_vr as [[[[d1' f1']g1']v1']r1'].
      inversion H. subst. repeat (split; easy || lia).
    Qed.

    Lemma jump_divstep_iter_d_bounds d f g v r n K
          (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - (Z.of_nat n) * (machine_wordsize - 2))
          (d_bounds : - K <= tc d <= K) :
      let '(d1,_,_,_,_) := fold_left (fun data i => jump_divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      - K - Z.of_nat n * (machine_wordsize - 2) <= tc d1 <= K + Z.of_nat n * (machine_wordsize - 2).
    Proof.
      induction n; intros.
      - cbn; lia.
      - rewrite seq_snoc, fold_left_app.
        cbn -[Z.of_nat].
        destruct (fold_left _ _ _) as [[[[d1 f1] g1] v1] r1] eqn:E.
        specialize (IHn ltac:(lia)).
        unshelve epose proof twos_complement_word_full_divsteps_d_bound machine_wordsize d1 (nth_default 0 f1 0) (nth_default 0 g1 0) 1 0 0 1
                 (Z.to_nat (machine_wordsize - 2))
                 (K + Z.of_nat n * (machine_wordsize - 2)) ltac:(lia) ltac:(lia) ltac:(lia).
        cbn -[Z.of_nat].
        rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.
        destruct (fold_left _ (seq 0 (Z.to_nat _))) as [[[[[[dn fn] gn] un] vn] qn] rn].
        cbn -[Z.of_nat].
        nia.
    Qed.

    Lemma jump_divstep_iter_invariants d f g v r n Kd
          (* (n_bounds : (0 < n)%nat) *)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (f_odd : Z.odd (tc_eval f) = true)
          (Kd_bounds : 0 <= Kd < (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2) - Z.of_nat n * (machine_wordsize - 2)))
          (d_bounds : - Kd < tc d < Kd)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) :=
        fold_left (fun data i => jump_divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      length f1 = tc_limbs
      /\ length g1 = tc_limbs
      /\ length v1 = mont_limbs
      /\ length r1 = mont_limbs
      /\ Z.odd (tc_eval f1) = true
      /\ - (Kd + Z.of_nat (S n) * (machine_wordsize - 2)) < tc d1 < Kd + Z.of_nat (S n) * (machine_wordsize - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ valid v1
      /\ valid r1
      /\ in_bounded f1
      /\ in_bounded g1.
    Proof.
      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).
      induction n.
      - cbn -[Z.add Z.sub Z.of_nat]. repeat (split; try easy); lia.
      - rewrite seq_snoc, fold_left_app. cbn -[Z.add Z.sub Z.of_nat].
        destruct fold_left as [[[[d1 f1] g1] v1] r1] eqn:E.
        specialize IHn as [f1_length [g1_length [v1_length [r1_length [f1_odd [d1_bounds [f1_bounds [f1_in_bounds [g1_bounds [g1_in_bounds [v1_valid r1_valid]]]]]]]]]]]. lia.
        unshelve epose proof jump_divstep_invariants d1 f1 g1 v1 r1 _ _ _ _ _ _ _ _ _ _ _ _; try assumption. nia.
        unshelve epose proof jump_divstep_invariants2 d1 f1 g1 v1 r1 (Kd + Z.of_nat (S n) * (machine_wordsize - 2)) _ _ _ _ _ _ _ _ _ _ _ _ _; try assumption. nia.
        destruct jump_divstep_aux as [[[[dn fn] gn] vn] rn].
        repeat (split; try easy).  nia. nia.
    Qed.

    Lemma jump_divstep_iter_correct d f g v r n Kd
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (Kd_bounds : 0 <= Kd < (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2) - Z.of_nat n * (machine_wordsize - 2)))
          (d_bounds : - Kd < tc d < Kd)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := fold_left (fun data i => jump_divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m) =
        Nat.iter n (jump_divstep_vr (Z.to_nat (machine_wordsize - 2)) machine_wordsize m) (tc d, tc_eval f, tc_eval g,
                                                                                            (eval v * ((r' ^ Z.of_nat mont_limbs) ^ (Z.of_nat n))) mod m,
                                                                                            (eval r * ((r' ^ Z.of_nat mont_limbs) ^ (Z.of_nat n))) mod m).
    Proof.

      induction n.
      - rewrite !Z.mul_1_r; reflexivity.
      - rewrite Nat_iter_S.
        unshelve epose proof jump_divstep_iter_invariants d f g v r n Kd _ _ _ _ _ _ _ _ _ _ _ _ _; try assumption. lia.
        rewrite seq_snoc, fold_left_app. cbn -[Z.of_nat Z.pow].
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => jump_divstep_aux data) (seq 0 n) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        replace (Z.of_nat (S n)) with (n + 1) by lia.
        rewrite Z.pow_add_r.
        rewrite !Z.mul_assoc.
        rewrite nat_iter_jump_divstep_vr_mul.
        rewrite <- (IHn ltac:(lia)).
        rewrite Z.pow_1_r.
        push_Zmod; pull_Zmod.
        apply jump_divstep_correct.
        specialize (IHn ltac:(lia)).
        inversion IHn.
        all: try easy. lia. lia.
    Qed.

  End __.

End WordByWordMontgomery.

Module UnsaturatedSolinas.

  Import Definitions.UnsaturatedSolinas.
  Import UnsaturatedSolinas.UnsaturatedSolinas.

  Section __.

    Context (limbwidth_num limbwidth_den : Z)
            (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
            (machine_wordsize : Z)
            (s : Z)
            (c : list (Z*Z))
            (n : nat)
            (tc_limbs : nat)
            (word_tc_mul_limbs : nat)
            (idxs : list nat)
            (m_big : 2 ^ machine_wordsize < s - Associational.eval c)
            (len_c : nat)
            (len_idxs : nat)
            (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
            (Hc : length c = len_c)
            (Hidxs : length idxs = len_idxs)
            (n1 : (1 < n)%nat)
            (mw2 : 2 < machine_wordsize)
            (tc_limbs0 : (0 < tc_limbs)%nat)
            (word_tc_mul_limbs_eq : (word_tc_mul_limbs = 1 + tc_limbs)%nat)
    .

    #[local] Notation eval := (Positional.eval (weight limbwidth_num limbwidth_den) n).

    Context (balance : list Z)
            (length_balance : length balance = n)
            (eval_balance : eval balance mod (s - Associational.eval c) = 0).

    #[local] Notation word_to_solina := (word_to_solina limbwidth_num limbwidth_den machine_wordsize s c n idxs balance).
    #[local] Notation jump_divstep := (jump_divstep limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs word_tc_mul_limbs idxs balance).
    #[local] Notation jump_divstep_aux := (jump_divstep_aux limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs word_tc_mul_limbs idxs balance).
    #[local] Notation tc_eval := (tc_eval machine_wordsize tc_limbs).
    #[local] Notation tc := (Z.twos_complement machine_wordsize).
    #[local] Notation m := (s - Associational.eval c).
    #[local] Notation in_bounded := (in_bounded machine_wordsize).

    #[local] Notation addmod := (addmod limbwidth_num limbwidth_den n).
    #[local] Notation oppmod := (oppmod limbwidth_num limbwidth_den n balance).
    #[local] Notation carrymod := (carrymod limbwidth_num limbwidth_den s c n idxs).

    Ltac t := repeat match goal with
                     | |- length _ = _ => auto with len
                     | |- in_bounded _ => auto with in_bounded
                     | |- _ => assumption
                     | |- _ => lia
                     | |- context[tc] => autorewrite with Ztc
                     | |- context[tc_eval] => autorewrite with tc
                     end.

    (** Correctness of jump_divstep  *)
    Theorem jump_divstep_correct d f g v r
            (f_odd : Z.odd (tc_eval f) = true)

            (Hf : length f = tc_limbs)
            (Hg : length g = tc_limbs)
            (Hv : length v = n)
            (Hr : length r = n)

            (d_bounds : - (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2)) < tc d <
                          2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2))
            (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
            (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
            (Hf2 : in_bounded f)
            (Hg2 : in_bounded g) :
      let '(d1, f1,g1,v1,r1) := jump_divstep_aux (d, f, g, v, r) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m)
      = jump_divstep_vr (Z.to_nat (machine_wordsize - 2)) machine_wordsize m (tc d, tc_eval f, tc_eval g, eval v mod m, eval r mod m).
    Proof.
      pose proof (pow_ineq_Z (machine_wordsize - 1) ltac:(lia)).

      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).
      assert (0 < 2 ^ (machine_wordsize - 1))
        by (apply Z.pow_pos_nonneg; lia).
      assert (0 < 2 ^ (machine_wordsize - 2))
        by (apply Z.pow_pos_nonneg; lia).
      assert (2 ^ (machine_wordsize - 2) * 2 = 2 ^ (machine_wordsize - 1))
        by (rewrite Z.mul_comm, Z.pow_mul_base by lia; apply f_equal2; lia).
      assert (2 * (2 * (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) * 2 ^ (machine_wordsize - 1))) = 2 ^ (machine_wordsize * (Z.of_nat (1 + tc_limbs)) - 1))
        by (rewrite <- Zpower_exp, !Z.pow_mul_base by nia; apply f_equal2; nia).

      unfold jump_divstep_aux.
      unshelve epose proof twos_complement_word_full_divstep_iter_correct (machine_wordsize) d (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
      all: (t; try lia).
      { rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=tc_limbs); t.
        unfold tc_eval in f_odd.
        rewrite Z.twos_complement_odd in f_odd by nia.
        rewrite Z.odd_mod2m by lia. assumption. }
      { replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in *; lia. }
      { apply nth_default_preserves_properties; auto; lia. }
      { apply nth_default_preserves_properties; auto; lia. }

      unshelve epose proof twos_complement_word_full_divsteps_bounds (machine_wordsize) d (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _.
      all: t.
      { replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2) in *; lia. }
      { rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=tc_limbs); t.
        unfold tc_eval in f_odd.
        rewrite Z.twos_complement_odd in f_odd by nia.
        rewrite Z.odd_mod2m by lia. assumption. }

      rewrite Z.twos_complement_one, Z.twos_complement_zero in * by lia.

      rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.
      destruct fold_left as [[[[[[d1 f1] g1] u1] v1] q1] r1].

      destruct H6 as [u1_bounds [v1_bounds [q1_bounds [r1_bounds [u1_pos [v1_pos [q1_pos r1_pos]]]]]]].

      simpl.
      rewrite !tc_eval_mod2m by t.
      rewrite <- !eval_nth_default_0 by t.
      rewrite Z2Nat.id in * by t.

      set (f0 := nth_default 0 f 0) in *.
      set (g0 := nth_default 0 g 0) in *.

      destruct Nat.iter as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''].

      assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; nia).

      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end.
      + congruence.
      + rewrite word_tc_mul_limbs_eq in *.
        rewrite firstn_tc_eval_small with (n:=(1 + tc_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full, !word_tc_mul_correct; t. inversion H5. reflexivity.
        rewrite !word_tc_mul_correct; t.
        clear -v1_bounds u1_bounds f_bounds g_bounds H4 H1 H7 H6. nia.
        eapply tc_eval_arithmetic_shiftr_bounds; t.
        clear -mw2 tc_limbs0. nia.
        clear -mw2 tc_limbs0. nia.
        rewrite tc_eval_tc_add_full, !word_tc_mul_correct, Z.pow_add_r; t.
        clear -v1_bounds u1_bounds f_bounds g_bounds H4 H1 H7 H6. nia.
        clear -mw2 tc_limbs0. nia.
        rewrite !word_tc_mul_correct; t.
        clear -v1_bounds u1_bounds f_bounds g_bounds H4 H1 H7 H6. nia.
      + rewrite word_tc_mul_limbs_eq in *.
        rewrite firstn_tc_eval_small with (n:=(1 + tc_limbs)%nat), tc_eval_arithmetic_shiftr, tc_eval_tc_add_full, !word_tc_mul_correct; t. inversion H5. reflexivity.
        rewrite !word_tc_mul_correct; t.
        clear -r1_bounds q1_bounds f_bounds g_bounds H4 H1 H7 H6. nia.
        eapply tc_eval_arithmetic_shiftr_bounds; t.
        clear -mw2 tc_limbs0. nia.
        clear -mw2 tc_limbs0. nia.
        rewrite tc_eval_tc_add_full, !word_tc_mul_correct, Z.pow_add_r; t.
        clear -r1_bounds q1_bounds f_bounds g_bounds H4 H1 H7 H6. nia.
        clear -mw2 tc_limbs0. nia.
        rewrite !word_tc_mul_correct; t.
        clear -r1_bounds q1_bounds f_bounds g_bounds H4 H1 H7 H6. nia.
      + rewrite eval_carrymod, eval_addmod by t.
        push_Zmod.
        rewrite !eval_carry_mulmod by t.
        push_Zmod.
        rewrite !eval_word_to_solina by t.
        inversion H5. push_Zmod; pull_Zmod.
        apply f_equal2; lia.
      + rewrite eval_carrymod, eval_addmod by t.
        push_Zmod.
        rewrite !eval_carry_mulmod by t.
        push_Zmod.
        rewrite !eval_word_to_solina by t.
        inversion H5. push_Zmod; pull_Zmod.
        apply f_equal2; lia.
    Qed.

    Lemma jump_divstep_invariants d f g v r
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = n)
          (r_length : length r = n)
          (f_odd : Z.odd (tc_eval f) = true)
          (d_bounds : - (2 ^ (machine_wordsize - 1) - (machine_wordsize - 2) - 1) < tc d < 2 ^ (machine_wordsize - 1) - (machine_wordsize - 2) - 1)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := jump_divstep_aux (d,f,g,v,r) in
      length f1 = tc_limbs
      /\ length g1 = tc_limbs
      /\ length v1 = n
      /\ length r1 = n
      /\ in_bounded f1
      /\ in_bounded g1.
    Proof.
      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).

      unfold jump_divstep_aux.

      unshelve epose proof twos_complement_word_full_divsteps_bounds machine_wordsize d (nth_default 0 f 0) (nth_default 0 g 0) 1 0 0 1 (Z.to_nat (machine_wordsize - 2)) 1 _ _ _ _ _ _ _ _ _ _ _ _ _.
      all: (t; try nia).
      { replace (Z.of_nat (Z.to_nat (machine_wordsize - 2))) with (machine_wordsize - 2); lia. }
      { rewrite eval_nth_default_0 with (m:=machine_wordsize) (n:=tc_limbs), Z.odd_mod2m by (assumption || lia).
        rewrite <- Z.twos_complement_odd with (m:=machine_wordsize * tc_limbs); (assumption || nia). }

      rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.
      destruct (fold_left _ (seq 0 (Z.to_nat _))) as [[[[[[dn fn] gn] un] vn] qn] rn].
      rewrite !word_tc_mul_limbs_eq.

      simpl. repeat (split; t).
    Qed.

    Lemma jump_divstep_invariants2 d f g v r Kd
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = n)
          (r_length : length r = n)
          (f_odd : Z.odd (tc_eval f) = true)
          (Kd_bounds : 0 <= Kd < (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2)))
          (d_bounds : - Kd < tc d < Kd)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := jump_divstep_aux (d,f,g,v,r) in
      Z.odd (tc_eval f1) = true
      /\ - (Kd + (machine_wordsize - 2)) < tc d1 < Kd + (machine_wordsize - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g1 < 2 ^ (machine_wordsize * tc_limbs - 2).
    Proof.
      unshelve epose proof jump_divstep_correct d f g v r _ _ _ _ _ _ _ _ _ _; try assumption; try lia.
      unshelve epose proof jump_divstep_vr_invariants (Z.to_nat (machine_wordsize - 2)) machine_wordsize m (tc d)
               (tc_eval f) (tc_eval g) (eval v mod m) (eval r mod m)
               Kd (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2)) _ _ _ _ _ _ _ _; try assumption; try lia;
        try (apply Z.mod_pos_bound; lia).
      destruct jump_divstep_aux as [[[[d1 f1]g1]v1]r1].
      destruct jump_divstep_vr as [[[[d1' f1']g1']v1']r1'].
      inversion H. subst. repeat (split; easy || lia).
    Qed.

    Lemma jump_divstep_iter_d_bounds d f g v r k K
          (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - (Z.of_nat k) * (machine_wordsize - 2))
          (d_bounds : - K <= tc d <= K) :
      let '(d1,_,_,_,_) := fold_left (fun data i => jump_divstep_aux data) (seq 0 k) (d,f,g,v,r) in
      - K - Z.of_nat k * (machine_wordsize - 2) <= tc d1 <= K + Z.of_nat k * (machine_wordsize - 2).
    Proof.
      induction k; intros.
      - cbn; lia.
      - rewrite seq_snoc, fold_left_app.
        cbn -[Z.of_nat].
        destruct (fold_left _ _ _) as [[[[d1 f1] g1] v1] r1] eqn:E.
        specialize (IHk ltac:(lia)).
        unshelve epose proof twos_complement_word_full_divsteps_d_bound machine_wordsize d1 (nth_default 0 f1 0) (nth_default 0 g1 0) 1 0 0 1
                 (Z.to_nat (machine_wordsize - 2))
                 (K + Z.of_nat k * (machine_wordsize - 2)) ltac:(lia) ltac:(lia) ltac:(lia).
        unfold jump_divstep_aux.
        rewrite <- fold_right_fold_left_lemma with (l:=(seq 0 (Z.to_nat (machine_wordsize - 2)))) by reflexivity.
        destruct (fold_left _ (seq 0 (Z.to_nat _))) as [[[[[[dn fn] gn] un] vn] qn] rn].
        cbn -[Z.of_nat].
        nia.
    Qed.

    Lemma jump_divstep_iter_invariants d f g v r k Kd
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = n)
          (r_length : length r = n)
          (f_odd : Z.odd (tc_eval f) = true)
          (Kd_bounds : 0 <= Kd < (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2) - Z.of_nat k * (machine_wordsize - 2)))
          (d_bounds : - Kd < tc d < Kd)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) :=
        fold_left (fun data i => jump_divstep_aux data) (seq 0 k) (d,f,g,v,r) in
      length f1 = tc_limbs
      /\ length g1 = tc_limbs
      /\ length v1 = n
      /\ length r1 = n
      /\ Z.odd (tc_eval f1) = true
      /\ - (Kd + Z.of_nat (S k) * (machine_wordsize - 2)) < tc d1 < Kd + Z.of_nat (S k) * (machine_wordsize - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ in_bounded f1
      /\ in_bounded g1.
    Proof.
      assert (1 < 2 ^ machine_wordsize)
        by (apply Zpow_facts.Zpower_gt_1; lia).
      induction k.
      - cbn -[Z.add Z.sub Z.of_nat]. repeat (split; try easy); lia.
      - rewrite seq_snoc, fold_left_app. cbn -[Z.add Z.sub Z.of_nat].
        destruct fold_left as [[[[d1 f1] g1] v1] r1] eqn:E.
        specialize IHk as [f1_length [g1_length [v1_length [r1_length [f1_odd [d1_bounds [f1_bounds [f1_in_bounds [g1_bounds g1_in_bounds]]]]]]]]]. lia.
        unshelve epose proof jump_divstep_invariants d1 f1 g1 v1 r1 _ _ _ _ _ _ _ _ _ _; try assumption. nia.
        unshelve epose proof jump_divstep_invariants2 d1 f1 g1 v1 r1 (Kd + Z.of_nat (S k) * (machine_wordsize - 2)) _ _ _ _ _ _ _ _ _ _ _; try assumption. nia.
        destruct jump_divstep_aux as [[[[dn fn] gn] vn] rn].
        repeat (split; try easy).  nia. nia.
    Qed.

    Lemma jump_divstep_iter_correct d f g v r k Kd
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = n)
          (r_length : length r = n)
          (Kd_bounds : 0 <= Kd < (2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2) - Z.of_nat k * (machine_wordsize - 2)))
          (d_bounds : - Kd < tc d < Kd)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := fold_left (fun data i => jump_divstep_aux data) (seq 0 k) (d,f,g,v,r) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m) =
        Nat.iter k (jump_divstep_vr (Z.to_nat (machine_wordsize - 2)) machine_wordsize m) (tc d, tc_eval f, tc_eval g, eval v mod m, eval r mod m).
    Proof.
      induction k.
      - reflexivity.
      - rewrite Nat_iter_S.
        unshelve epose proof jump_divstep_iter_invariants d f g v r k Kd _ _ _ _ _ _ _ _ _ _ _; try assumption. lia.
        rewrite seq_snoc, fold_left_app. cbn -[Z.of_nat Z.pow].
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => jump_divstep_aux data) (seq 0 k) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        rewrite <- (IHk ltac:(lia)).
        apply jump_divstep_correct.
        specialize (IHk ltac:(lia)).
        inversion IHk.
        all: try easy. lia.
    Qed.
  End __.
End UnsaturatedSolinas.
