Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.TCAdd.
Require Import Crypto.Arithmetic.BYInv.One.
Require Import Crypto.Arithmetic.BYInv.Mod2.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Decidable.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Lemma length_tc_opp machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hn : (0 < n)%nat)
      (Hf : length f = n) :
  length (tc_opp machine_wordsize n f) = n.
Proof. unfold tc_opp; rewrite length_tc_add; auto with distr_length. Qed.

Hint Rewrite length_tc_opp : distr_length.

Lemma eval_tc_opp machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hn : (0 < n)%nat)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hf : length f = n) :
  eval (uweight machine_wordsize) n (tc_opp machine_wordsize n f) =
  (- eval (uweight machine_wordsize) n f) mod (2^(machine_wordsize * n)).
Proof.
  assert (2 ^ machine_wordsize <> 0) by (apply Z.pow_nonzero; lia).
  assert (2 ^ (machine_wordsize * Z.of_nat (length f)) <> 0) by (apply Z.pow_nonzero; nia).

  symmetry. unfold tc_opp.
  rewrite eval_tc_add by distr_length.
  generalize dependent n. induction f; intros.
  - simpl in *; rewrite <- Hf; rewrite eval0; rewrite !Zmod_0_l; reflexivity.
  - simpl in *. subst.
    assert (2 ^ (machine_wordsize * Z.of_nat (length f)) <> 0) by (apply Z.pow_nonzero; nia).

    rewrite !eval_cons, uweight_0, !uweight_eval_shift, uweight_eq_alt' by distr_length.
    rewrite !Z.mul_1_l, !Z.mul_1_r, Z.opp_add_distr, Zopp_mult_distr_r, <- Z.add_mod_idemp_r by distr_length.
    symmetry. rewrite Z.add_assoc, <- Z.add_mod_idemp_r; try (rewrite Zpos_P_of_succ_nat in H0; rewrite Nat2Z.inj_succ; assumption).
    replace (2 ^ (machine_wordsize * Z.of_nat (S (length f)))) with
        ((2 ^ machine_wordsize) * (2 ^ (machine_wordsize * Z.of_nat (length f)))).
    rewrite !Z.mul_mod_distr_l by lia.
    unfold Z.lnot_modulo. rewrite Lnot.Z.lnot_equiv. unfold Z.pred.
    destruct (length f) eqn:E.
    + rewrite !eval0.
      rewrite !Z.mul_0_r, !Z.mul_1_r, !Z.add_0_r.
      replace (-a + -1) with (- (a + 1)) by ring.
      rewrite eval_one.
      rewrite Z.mod_opp_small.
      replace (1 + (2 ^ machine_wordsize - (a + 1))) with
          (-a + 2 ^ machine_wordsize) by ring.
      rewrite <- Z.add_mod_idemp_r.
      rewrite Z_mod_same_full. rewrite Z.add_0_r. reflexivity.
      apply Z.pow_nonzero. lia. lia.
      specialize (Hz a (or_introl eq_refl)). lia. lia. lia.
    + rewrite IHf by (try (intros; apply Hz; right; assumption); lia).
      rewrite !eval_one in * by lia.
      rewrite <- Z.mul_mod_distr_l, Z.add_mod_idemp_r by nia.
      symmetry.
      rewrite <- Z.mul_mod_distr_l, Z.add_mod_idemp_r, Z.mul_add_distr_l, Z.mul_1_r by nia.
      replace (-a + -1) with (- (a + 1)) by ring.
      rewrite Z.mod_opp_small.
      unfold Z.lnot_modulo.
      rewrite Z.add_assoc.
      replace (1 + (2 ^ machine_wordsize - (a + 1))) with
          (- a + 2 ^ machine_wordsize) by ring.
      reflexivity.
      specialize (Hz a (or_introl eq_refl)); lia.
    + rewrite <- Z.pow_add_r; try apply f_equal; nia.
Qed.

Lemma tc_opp_mod2 machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hn : (0 < n)%nat)
      (Hf : length f = n)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
  mod2 (tc_opp machine_wordsize n f) = mod2 f.
Proof.
  rewrite <- !(eval_mod2 machine_wordsize n) by distr_length.
  rewrite eval_tc_opp; auto.
  set (x := eval (uweight machine_wordsize) n f).
  destruct f.
  - subst. reflexivity.
  - rewrite <- (Znumtheory.Zmod_div_mod _ (2 ^ (machine_wordsize * Z.of_nat n))).
    rewrite <- Z.opp_mod2; reflexivity. lia. apply Z.pow_pos_nonneg; nia.
    apply Zpow_facts.Zpower_divide. simpl in *. nia.
Qed.

Lemma tc_eval_tc_opp machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hf : length f = n)
      (f_bounds : tc_eval machine_wordsize n f <> - 2 ^ (machine_wordsize * n - 1)):
  tc_eval machine_wordsize n (tc_opp machine_wordsize n f) =
  - tc_eval machine_wordsize n f.
Proof.
  assert (0 < Z.of_nat n) by lia; unfold tc_eval in *.
  rewrite eval_tc_opp, Z.twos_complement_mod, Z.twos_complement_zopp; try tauto; nia.
Qed.

Lemma tc_eval_tc_opp_alt machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hf : length f = n)
      (f_bounds : tc_eval machine_wordsize n f = - 2 ^ (machine_wordsize * n - 1)):
  tc_eval machine_wordsize n (tc_opp machine_wordsize n f) = tc_eval machine_wordsize n f.
Proof.
  assert (0 < Z.of_nat n) by lia; unfold tc_eval in *.
  rewrite eval_tc_opp, Z.twos_complement_mod, Z.twos_complement_zopp2; try tauto; nia.
Qed.

Lemma tc_eval_tc_opp_bounds machine_wordsize n f K
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hf : length f = n)
      (f_bounds : - K < tc_eval machine_wordsize n f < K) :
  - K < tc_eval machine_wordsize n (tc_opp machine_wordsize n f) < K.
Proof.
  destruct (dec (tc_eval machine_wordsize n f = - 2 ^ (machine_wordsize * n - 1))).
  - rewrite tc_eval_tc_opp_alt; assumption.
  - rewrite tc_eval_tc_opp; try assumption; lia.
Qed.
