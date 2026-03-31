Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.EvalLemmas.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ListUtil.

Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Lemma tc_sign_bit_spec mw n f
      (f_length : length f = n)
      (f_in_bounded : in_bounded mw f)
      (Hmw : 0 < mw)
      (Hn : (0 < n)%nat) :
  tc_sign_bit mw n f = Z.sign_bit (mw * n) (eval (uweight mw) n f).
Proof.
  intros.
  unfold tc_sign_bit.
  fold (Z.sign_bit mw (nth_default 0 f (n - 1))).
  rewrite !Z.sign_bit_testbit, eval_testbit.
  all: try lia; try assumption.
  2: apply eval_bound; try lia; assumption.
  f_equal. f_equal. f_equal.
  - rewrite Z.mul_comm.
    rewrite Z.div_sub_l.
    rewrite Z.div_opp_1_l.
    lia. lia. lia.
  - push_Zmod; pull_Zmod.
    rewrite Z.mul_0_l.
    rewrite Z.sub_0_l.
    rewrite Z.mod_neg_small. lia. lia.
  - apply nth_default_preserves_properties.
    assumption. lia.
Qed.

Lemma tc_sign_bit_neg mw n f
      (f_length : length f = n)
      (f_in_bounded : in_bounded mw f)
      (Hmw : 0 < mw)
      (Hn : (0 < n)%nat) :
  tc_sign_bit mw n f = Z.b2z (tc_eval mw n f <? 0).
Proof.
  rewrite tc_sign_bit_spec by assumption.
  rewrite Z.sign_bit_twos_complement.
  reflexivity. nia. apply eval_bound; assumption .
Qed.
