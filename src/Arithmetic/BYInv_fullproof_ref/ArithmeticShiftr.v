Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.EvalLemmas.
Require Import Crypto.Arithmetic.BYInv.Mod2.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ListUtil.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.ArithmeticShiftr.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.Tactics.SolveRange.
Require Import Crypto.Util.ZUtil.Tactics.SolveTestbit.

(** Section about arithmetic right shift *)

(*********************************************************************** *)
(**Section for properties of tc_arithmetic_shiftr1 including correctness *)
(*********************************************************************** *)

Lemma eval_arithmetic_shiftr1 machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hz : in_bounded machine_wordsize f)
      (Hf : length f = n) :
  eval (uweight machine_wordsize) n (arithmetic_shiftr1 machine_wordsize n f) =
  Z.arithmetic_shiftr1 (machine_wordsize * n) (eval (uweight machine_wordsize) n f).
Proof.
  generalize dependent n.
  induction f as [|z f IHf]; intros; subst.
  - rewrite !eval0; reflexivity.
  - destruct f.
    + cbn; rewrite uweight_0, !Z.mul_1_r, !Z.mul_1_l, !Z.add_0_r; reflexivity.
    + unfold arithmetic_shiftr1; simpl.
      rewrite eval_cons, !uweight_eval_shift by (autorewrite with distr_length; try reflexivity; lia).
      replace (map _ _ ++ _) with (arithmetic_shiftr1 machine_wordsize (S (length f)) (z0 :: f)).
      rewrite IHf; try reflexivity.

      unfold Z.arithmetic_shiftr1.
      rewrite !Z.land_pow2_testbit, !eval_testbit; try tauto; try nia; simpl.
      replace (Z.abs_nat ((machine_wordsize * Z.pos (Pos.succ (Pos.of_succ_nat (length f))) - 1) / machine_wordsize)) with
          (S (Z.abs_nat ((machine_wordsize * Z.pos (Pos.of_succ_nat (length f)) - 1) / machine_wordsize))).
      rewrite !ListUtil.nth_default_cons_S, !ListUtil.nth_default_cons by lia.

      unfold Z.sub.
      rewrite !Modulo.Z.mod_add_l', uweight_0, uweight_eq_alt', !Z.mul_1_l, Z.mul_1_r, Z.truncating_shiftl_mod by lia.
      destruct (Z.testbit
      (nth_default 0 (z0 :: f)
         (Z.abs_nat
            ((machine_wordsize * Z.pos (Pos.of_succ_nat (length f)) + - (1)) /
             machine_wordsize)))
      ((- (1)) mod machine_wordsize)) eqn:E.
      * rewrite <- !Z.div2_spec, !Z.div2_div, !Z.lor_add; ring_simplify.
        rewrite (eval_cons _ (S _)), uweight_eval_shift by (try reflexivity; lia).
        rewrite uweight_0, uweight_eq_alt', !Z.mul_1_l, Z.mul_1_r, Z.div2_split, <- Z.pow_add_r by nia.
        rewrite eval_mod2 by (try reflexivity; lia). unfold mod2.
        rewrite ListUtil.nth_default_cons.
        replace (machine_wordsize + (_ + _)) with
            (machine_wordsize * Z.pos (Pos.succ (Pos.of_succ_nat (length f))) + - (1)) by lia; ring.

        rewrite Z.land_comm, Z.land_pow2_small; [lia|].
        split.
        apply Div.Z.div_nonneg; try lia.
        assert (0 <= eval (uweight machine_wordsize) (S (S (length f))) (z :: z0 :: f)).
        { apply eval_bound; try lia. intros; apply Hz; simpl; tauto. reflexivity. }
        specialize (Hz z (or_introl eq_refl)); nia.
        apply Div.Z.div_lt_upper_bound'; [lia|].
           rewrite Z.mul_comm, Pow.Z.pow_mul_base by nia.
        simpl; rewrite <- Z.add_assoc, Z.add_0_r.
        apply eval_bound; try lia; tauto.

        rewrite Z.land_comm, Z.land_pow2_small; [lia|].
        split.
        apply Div.Z.div_nonneg; [|lia].
        apply eval_bound; [lia| |]. eapply in_bounded_tail. eassumption. reflexivity.

        apply Div.Z.div_lt_upper_bound'; try lia.
        rewrite Z.mul_comm, Pow.Z.pow_mul_base by nia. rewrite <- Z.add_assoc, Z.add_0_r.
        apply eval_bound; try assumption. eapply in_bounded_tail. eassumption. reflexivity.

        rewrite Zmod_odd.
        specialize (Hz z (or_introl eq_refl)).
        destruct (Z.odd z0).
        ** rewrite Z.mul_1_r, Z.land_pow2_small; [reflexivity|]. split.
           apply Div.Z.div_nonneg; lia.
           apply Div.Z.div_lt_upper_bound'; [lia|].
           rewrite Z.mul_comm, Pow.Z.pow_mul_base, Z.sub_simpl_r; lia.
        ** rewrite Z.mul_0_r, Z.land_0_r; reflexivity.
      * rewrite !Z.lor_0_l, (eval_cons _ (S _)), uweight_eval_shift
          by (try reflexivity; lia).
        rewrite uweight_0, uweight_eq_alt', Z.mul_1_l, Z.mul_1_r.
        rewrite <- !Z.div2_spec, !Z.div2_div, Z.div2_split by lia.
        rewrite eval_mod2, mod2_cons, Z.lor_add;
          [reflexivity| |reflexivity|lia].
        rewrite Zmod_odd. specialize (Hz z (or_introl eq_refl)).
        destruct (Z.odd z0).
        ** rewrite Z.mul_1_r, Z.land_pow2_small; try lia.
           split.
           apply Div.Z.div_nonneg; lia.
           apply Div.Z.div_lt_upper_bound'; [lia|].
           rewrite Z.mul_comm, Pow.Z.pow_mul_base, Z.sub_simpl_r; lia.
        ** rewrite Z.mul_0_r, Z.land_0_r; reflexivity.
      * rewrite <- Zabs2Nat.inj_succ.
        apply f_equal.
        rewrite <- Z.add_1_r.
        unfold Z.sub.
        rewrite !Div.Z.div_add_l'; lia.
        set (x := Pos.of_succ_nat (length f)).
        set (a := machine_wordsize). apply Div.Z.div_nonneg; nia.
      * eapply in_bounded_tail; eassumption.
      * eapply in_bounded_tail; eassumption.
      * unfold arithmetic_shiftr1.
        replace (S (length f) - 1)%nat with (length f) by lia.
        rewrite ListUtil.nth_default_cons_S.
        apply f_equal2; [|reflexivity].
        apply map_seq_ext; [|lia].
        intros; simpl; rewrite !Nat.add_1_r, !(ListUtil.nth_default_cons_S _ z); reflexivity.
Qed.

Lemma tc_eval_arithmetic_shiftr1 machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hz : in_bounded machine_wordsize f)
      (Hf : length f = n) :
  tc_eval machine_wordsize n (arithmetic_shiftr1 machine_wordsize n f) =
  (tc_eval machine_wordsize n f) / 2.
Proof.
  assert (0 < Z.of_nat n) by lia. unfold tc_eval. rewrite eval_arithmetic_shiftr1, Z.arithmetic_shiftr1_spec; auto; [nia|].
  apply eval_bound; auto.
Qed.

Lemma arithmetic_shiftr_0 machine_wordsize n f
      (Hm : 0 < machine_wordsize)
      (Hn : (0 < n)%nat)
      (Hf : length f = n)
      (Hf2 : in_bounded machine_wordsize f) :
  arithmetic_shiftr machine_wordsize n f 0 = f.
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  unfold arithmetic_shiftr.
  rewrite Z.arithmetic_shiftr_0 by
      (try apply nth_default_preserves_properties; try assumption; lia).
  rewrite <- (map_nth_default_seq 0 n f) at 2 by assumption; destruct n; [lia|].
  rewrite seq_snoc, map_app.
  apply f_equal2; replace (S n - 1)%nat with n by lia; try reflexivity.
  apply map_seq_ext; try lia; intros i Hi.
  rewrite Z.shiftr_0_r, Z.truncating_shiftl_large, Z.lor_0_r, Nat.add_0_r by lia.
  reflexivity.
Qed.

Lemma arithmetic_shiftr_1 machine_wordsize n f
      (Hm : 0 < machine_wordsize)
      (Hf2 : in_bounded machine_wordsize f) :
  arithmetic_shiftr machine_wordsize n f 1 =
  arithmetic_shiftr1 machine_wordsize n f.
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  unfold arithmetic_shiftr, arithmetic_shiftr1.
  rewrite Z.arithmetic_shiftr_1 by
      (try apply nth_default_preserves_properties; try assumption; lia).
  reflexivity.
Qed.

Lemma arithmetic_shiftr_arithmetic_shiftr1 machine_wordsize n (f : list Z) k
      (Hn : (0 < n)%nat)
      (Hf : length f = n)
      (Hk : 0 <= k < machine_wordsize)
      (Hf2 : in_bounded machine_wordsize f) :
  arithmetic_shiftr machine_wordsize n
                        (arithmetic_shiftr1 machine_wordsize n f) k =
  arithmetic_shiftr machine_wordsize n f (k + 1).
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  unfold arithmetic_shiftr, arithmetic_shiftr1.
  rewrite nth_default_app, map_length, seq_length.
  destruct (lt_dec (n - 1) (n - 1)); try lia.
  replace (n - 1 - (n - 1))%nat with 0%nat by lia.
  rewrite nth_default_cons, Z.arithmetic_shiftr_arithmetic_shiftr1
    by (try (apply nth_default_preserves_properties; [assumption|Z.solve_range]); lia).
  apply f_equal2; try reflexivity. apply map_seq_ext; try lia; intros i Hi.
  rewrite !nth_default_app, map_length, seq_length.
  destruct (lt_dec i (n - 1));
    destruct (lt_dec (i + 1) (n - 1)); try lia.
  - rewrite !(map_nth_default _ _ _ _ 0%nat 0) by (rewrite seq_length; lia).
    rewrite !nth_default_seq_inbounds by lia.
    rewrite Nat.add_0_r, Z.shiftr_lor, Z.shiftr_shiftr by lia.
    rewrite Z.add_comm, <- Z.lor_assoc. apply f_equal2; try reflexivity.
    rewrite Z.truncating_shiftl_lor by lia.
    rewrite Z.truncating_shiftl_truncating_shiftl by lia.
    Z.solve_using_testbit; rewrite (Z.testbit_neg_r _ (n1 - _)), orb_false_r, ?orb_false_l by lia;
      apply f_equal2; try lia.
    all: apply f_equal2; try reflexivity; lia.
  - assert (E : (i + 1 = n - 1)%nat) by lia.
    rewrite !(map_nth_default _ _ _ _ 0%nat 0) by (rewrite seq_length; lia).
    rewrite !nth_default_seq_inbounds by lia; simpl; rewrite Nat.add_0_r.
    rewrite E. replace (n - 1 - (n - 1))%nat with 0%nat by lia.
    rewrite nth_default_cons, Z.shiftr_lor, Z.shiftr_shiftr, Z.add_comm by lia.
    rewrite <- Z.lor_assoc.
    apply f_equal2; [reflexivity|].
    Z.solve_using_testbit.
    apply nth_default_preserves_properties; [assumption|lia].
Qed.

Local Fixpoint iter_arithmetic_shiftr1 m n f k :=
  match k with
  | 0%nat => f
  | 1%nat => arithmetic_shiftr1 m n f
  | S k => iter_arithmetic_shiftr1 m n (arithmetic_shiftr1 m n f) k
  end.

Lemma iter_arithmetic_shiftr_S m n f k :
  iter_arithmetic_shiftr1 m n f (S k)
  = iter_arithmetic_shiftr1 m n (arithmetic_shiftr1 m n f) k.
Proof. destruct k; reflexivity. Qed.

Lemma arithmetic_shiftr1_in_bounded m n f
      (Hm : 0 <= m)
      (Hf : in_bounded m f) :
  in_bounded m (arithmetic_shiftr1 m n f).
Proof.
  intros y H; unfold arithmetic_shiftr1 in H.
  assert (H1 : 0 <= 0 < 2 ^ m) by Z.solve_range.
  apply in_app_iff in H. destruct H; simpl in H.
  - apply in_map_iff in H; destruct H as [i [H H0] ]; rewrite <- H.
    pose proof nth_default_preserves_properties _ f i 0 Hf H1;
      simpl in H2; Z.solve_range.
  - destruct H as [H|[] ]; rewrite <- H.
    apply Z.arithmetic_shiftr1_bound.
    pose proof nth_default_preserves_properties _ f (n - 1) 0 Hf H1;
      simpl in H0; Z.solve_range.
Qed.

Lemma arithmetic_shiftr1_length m n f
      (Hn : (0 < n)%nat)
      (Hf : length f = n) :
  length (arithmetic_shiftr1 m n f) = n.
Proof. unfold arithmetic_shiftr1; rewrite app_length, map_length, seq_length; simpl; lia. Qed.

Lemma arithmetic_shiftr_iter_arithmetic_shiftr1 machine_wordsize n f k
      (Hn : (0 < n)%nat)
      (Hf : length f = n)
      (Hk : 0 <= k < machine_wordsize)
      (Hf2 : in_bounded machine_wordsize f) :
  arithmetic_shiftr machine_wordsize n f k
  = iter_arithmetic_shiftr1 machine_wordsize n f (Z.abs_nat k).
Proof.
  assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm : 0 <= machine_wordsize) by lia.
  destruct (Z.abs_nat k) as [|m] eqn:E.
  - replace k with 0 by lia; simpl; apply arithmetic_shiftr_0; try assumption; lia.
  - generalize dependent k. generalize dependent f.
    induction m; intros.
    + simpl; replace k with (0 + 1) by lia.
      rewrite arithmetic_shiftr_1 by (try assumption; lia). reflexivity.
    + specialize (IHm (arithmetic_shiftr1 machine_wordsize n f)
                      (arithmetic_shiftr1_length machine_wordsize n f Hn Hf)
                      (arithmetic_shiftr1_in_bounded machine_wordsize n f Hm Hf2)
                      (k - 1) ltac:(lia) ltac:(lia)).
      rewrite iter_arithmetic_shiftr_S, <- IHm.
      rewrite arithmetic_shiftr_arithmetic_shiftr1
        by (try lia; assumption).
      rewrite Z.sub_simpl_r; reflexivity.
Qed.

Lemma arithmetic_shiftr_length machine_wordsize n f k
      (Hn : (0 < n)%nat)
      (Hf : length f = n) :
  length (arithmetic_shiftr machine_wordsize n f k) = n.
Proof. unfold arithmetic_shiftr; autorewrite with distr_length; lia. Qed.

Lemma arithmetic_shiftr_in_bounded machine_wordsize n f k
      (Hn : (0 < n)%nat)
      (Hk : 0 <= k)
      (Hm : 0 < machine_wordsize)
      (Hf : in_bounded machine_wordsize f) :
  in_bounded machine_wordsize (arithmetic_shiftr machine_wordsize n f k).
Proof.
  intros y H. unfold arithmetic_shiftr in H.
  assert (H1 : 0 <= 0 < 2 ^ machine_wordsize) by Z.solve_range.
  apply in_app_iff in H; destruct H; simpl in H.
  - apply in_map_iff in H; destruct H as [i [H H0] ]; rewrite <- H.
    epose proof nth_default_preserves_properties _ f i 0 Hf H1.
      simpl in H2; Z.solve_range.
  - destruct H as [H|[] ]; rewrite <- H.
    apply Z.arithmetic_shiftr_bound; try lia.
    pose proof nth_default_preserves_properties _ f (n - 1) 0 Hf H1; simpl in H0;
      Z.solve_range.
Qed.

Lemma tc_eval_arithmetic_shiftr machine_wordsize n f k
      (Hn : (0 < n)%nat)
      (Hf : length f = n)
      (Hk : 0 <= k < machine_wordsize)
      (Hf2 : in_bounded machine_wordsize f) :
  tc_eval machine_wordsize n
                       (arithmetic_shiftr machine_wordsize n f k) =
  tc_eval machine_wordsize n f / (2 ^ k).
Proof.
  assert (Hm : 0 <= machine_wordsize) by lia.
  rewrite arithmetic_shiftr_iter_arithmetic_shiftr1 by assumption.
  destruct (Z.abs_nat k) as [|m] eqn:E.
  - replace k with 0 by lia; simpl; rewrite Z.div_1_r; reflexivity.
  - generalize dependent k; generalize dependent f; induction m; intros.
    + simpl; replace k with 1 by lia; rewrite Z.pow_1_r.
      apply tc_eval_arithmetic_shiftr1; try assumption; lia.
    + rewrite iter_arithmetic_shiftr_S.
      specialize (IHm (arithmetic_shiftr1 machine_wordsize n f)
                      (arithmetic_shiftr1_length machine_wordsize n f Hn Hf)
                      (arithmetic_shiftr1_in_bounded machine_wordsize n f Hm Hf2)
                      (k - 1) ltac:(lia) ltac:(lia)).
      assert (0 < 2 ^ (k - 1)) by (apply Z.pow_pos_nonneg; lia).
      rewrite IHm, tc_eval_arithmetic_shiftr1 by (try assumption; lia).
      rewrite Z.div_div, Z.pow_mul_base, Z.sub_simpl_r by lia; reflexivity.
Qed.

Lemma div_lt_lower_bound a b c : 0 < b -> b * (a + 1) <= c -> a < c / b.
Proof. intros; enough (a + 1 <= c / b) by lia; apply Z.div_le_lower_bound; assumption. Qed.

Lemma tc_eval_arithmetic_shiftr_bounds machine_wordsize n f k lb ub
      (Hlb : 0 <= lb)
      (Hub : 0 <= ub)
      (Hn : (0 < n)%nat)
      (Hf : length f = n)
      (Hk : 0 <= k < machine_wordsize)
      (Hf2 : in_bounded machine_wordsize f)
      (Hf3 : - 2 ^ (k + lb) <= tc_eval machine_wordsize n f < 2 ^ (k + ub)) :
  - 2 ^ lb <= tc_eval machine_wordsize n (arithmetic_shiftr machine_wordsize n f k) < 2 ^ ub.
Proof.
  rewrite tc_eval_arithmetic_shiftr by assumption.
  Z.solve_range.
  repeat match goal with
  | |- context[(- ?a) * ?b] => replace ((- a) * b) with (- (a * b)) by ring
  | |- context[?a * (- ?b)] => replace (a * (- b)) with (- (a * b)) by ring
         end.
  Z.solve_range.
Qed.

Lemma tc_eval_arithmetic_shiftr_weak_bounds machine_wordsize n f k K
      (Hn : (0 < n)%nat)
      (Hf : length f = n)
      (Hk : 0 <= k < machine_wordsize)
      (Hf2 : in_bounded machine_wordsize f)
      (Hf3 : - K < tc_eval machine_wordsize n f < K) :
  - K < tc_eval machine_wordsize n (arithmetic_shiftr machine_wordsize n f k) < K.
Proof.
  rewrite tc_eval_arithmetic_shiftr by assumption.
  Z.solve_range.
  apply div_lt_lower_bound. lia. nia.
Qed.

Lemma eval_div_pow2 machine_wordsize n f k
  (Hk : 0 <= k <= machine_wordsize)
  (Hf : length f = n)
  (Hf2 : (2 ^ k | nth_default 0 f 0)) :
    (2 ^ k | eval (uweight machine_wordsize) n f).
Proof.
  destruct f.
  - rewrite eval_nil. apply Z.divide_0_r.
  - cbn in Hf2. subst; simpl in *. rewrite eval_cons by reflexivity.
    rewrite uweight_eval_shift by lia.
    rewrite uweight_0.
    rewrite uweight_eq_alt'.
    rewrite Z.mul_1_r.
    rewrite Z.mul_1_l.
    apply Z.divide_add_r. assumption.
    apply Z.divide_mul_l.
    apply Divide.Z.divide_pow_le. assumption.
Qed.

Lemma twos_complement_div_pow2 m a k
  (Hk : 0 <= k <= m) :
  (2 ^ k | a) -> (2 ^ k | Z.twos_complement m a).
Proof.
  intros.
  unfold Z.twos_complement.
  destruct (a mod 2 ^ m <? 2 ^ (m - 1)) eqn:E.
  rewrite Zmod_eq_full.
  apply Z.divide_sub_r. assumption.
  apply Z.divide_mul_r.
  apply Divide.Z.divide_pow_le. assumption.
  apply Z.pow_nonzero. lia. lia.
  apply Z.divide_sub_r.
  rewrite Zmod_eq_full.
  apply Z.divide_sub_r. assumption.
  apply Z.divide_mul_r.
  apply Divide.Z.divide_pow_le. assumption. lia.
  apply Divide.Z.divide_pow_le. assumption.
Qed.

Lemma tc_eval_div_pow2 machine_wordsize n f k
      (Hk : 0 <= k <= machine_wordsize)
      (Hn : (0 < n)%nat)
      (Hf : length f = n)
      (Hf2 : (2 ^ k | nth_default 0 f 0)) :
  (2 ^ k | tc_eval machine_wordsize n f).
Proof.
  unfold tc_eval.
  apply twos_complement_div_pow2. nia.
  apply eval_div_pow2; assumption.
Qed.
