Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Util.ZUtil.Shift.

Import Positional.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Lemma in_bounded_tail machine_wordsize a f : in_bounded machine_wordsize (a :: f) -> in_bounded machine_wordsize f.
Proof.
  intros. unfold in_bounded in *.
  intros. apply H. right. assumption.
Qed.

Lemma in_bounded_head machine_wordsize a f : in_bounded machine_wordsize (a :: f) -> 0 <= a < 2 ^ machine_wordsize.
Proof.
  intros H. apply H. left. reflexivity.
Qed.

Lemma eval_bound machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hz : in_bounded machine_wordsize f)
      (Hf : length f = n) :
  0 <= eval (uweight machine_wordsize) n f < 2 ^ (machine_wordsize * n).
Proof.
  generalize dependent n; induction f; intros; subst; simpl in *.
  - rewrite eval0, Z.mul_0_r, Z.pow_0_r; lia.
  - rewrite eval_cons, uweight_eval_shift, uweight_0, uweight_eq_alt' by lia.
    assert (0 <= 2 ^ machine_wordsize) by (apply Z.pow_nonneg; lia).
    specialize (IHf (fun z H => Hz z (or_intror H)) (length f) eq_refl).
    specialize (Hz a (or_introl eq_refl)).
    split; ring_simplify; rewrite Z.mul_1_r.
    + nia.
    + replace (machine_wordsize * Z.pos (Pos.of_succ_nat (length f))) with
        (machine_wordsize + machine_wordsize * Z.of_nat (length f)) by nia.
      rewrite Z.pow_add_r; nia.
Qed.

Lemma eval_testbit machine_wordsize n f m
      (Hz : in_bounded machine_wordsize f)
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = n)
      (Hm : 0 <= m) :
  Z.testbit (eval (uweight machine_wordsize) n f) m =
  Z.testbit (nth_default 0 f (Z.abs_nat (m / machine_wordsize))) (m mod machine_wordsize).
Proof.
  generalize dependent n. generalize dependent m. induction f; intros; simpl in *; subst.
  - rewrite ListUtil.nth_default_nil, eval0, !Z.testbit_0_l; reflexivity.
  - rewrite eval_cons, uweight_eval_shift
      by (specialize (Hz a (or_introl eq_refl)); lia).
    rewrite uweight_0, uweight_eq_alt', Z.mul_1_l, Z.mul_1_r, Z.mul_comm, <- Z.shiftl_mul_pow2, Shift.Z.testbit_add_shiftl_full
      by (specialize (Hz a (or_introl eq_refl)); lia).
    destruct (m <? machine_wordsize) eqn:E.
    + rewrite Z.ltb_lt in E; rewrite Z.div_small by lia.
      rewrite ListUtil.nth_default_cons, Z.mod_small by lia. reflexivity.
    + rewrite Z.ltb_ge in E; rewrite IHf; try lia.
      replace (Z.abs_nat (m / machine_wordsize)) with
          (S (Z.abs_nat ((m - machine_wordsize) / machine_wordsize))).
      rewrite ListUtil.nth_default_cons_S, PullPush.Z.sub_mod_r, Z_mod_same_full, Z.sub_0_r; reflexivity.
      rewrite <- Zabs2Nat.inj_succ_abs, Z.abs_eq.
      replace machine_wordsize with (1 * machine_wordsize) at 1 by ring.
      rewrite Div.Z.div_sub, Z.sub_1_r, Z.succ_pred; lia.
      apply Div.Z.div_nonneg; lia.
      eapply in_bounded_tail. eassumption.
Qed.

Lemma eval_nth_default_0 m n f
      (Hm : 0 < m)
      (Hf : length f = n)
      (Hf2 : in_bounded m f) :
  nth_default 0 f 0 = eval (uweight m) n f mod 2 ^ m.
Proof.
  induction f.
  - cbn; now rewrite eval_nil, Z.mod_0_l by (apply Z.pow_nonzero; lia).
  - cbn. destruct n; [inversion Hf|].
    rewrite eval_cons, uweight_eval_shift, uweight_0, uweight_1, Z.mul_1_l by (auto with zarith).
    autorewrite with push_Zmod.
    rewrite Z.mod_0_l, Z.add_0_r, Z.mod_mod, Z.mod_small; auto with zarith.
    apply Hf2; left; reflexivity.
Qed.
