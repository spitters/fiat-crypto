Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.EvalLemmas.
Require Import Crypto.Arithmetic.BYInv.Ones.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.SignExtend.
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.

Require Import Crypto.Util.ZUtil.Tactics.SolveRange.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Lemma sat_sign_extend_eval m n_old n_new f
      (Hn_old : (0 < n_old)%nat)
      (Hn_new : (n_old <= n_new)%nat)
      (Hf : (length f = n_old))
      (Hm : 0 < m)
      (Hf2 : forall z : Z, In z f -> 0 <= z < 2 ^ m) :
  Positional.eval (uweight m) n_new (tc_sign_extend m n_old n_new f)
  = Z.sign_extend (m * n_old) (m * n_new) (Positional.eval (uweight m) n_old f).
Proof.
  rewrite Z.sign_extend_add by (solve [ nia | apply eval_bound; assumption ]).
  unfold tc_sign_extend; rewrite unfold_Let_In, Zselect.Z.zselect_correct.
  rewrite Z.sign_bit_testbit
    by (solve [ lia | apply nth_default_preserves_properties; try assumption; Z.solve_range]).
  rewrite eval_testbit by (solve [ assumption | nia ]).
  assert (H : (Z.abs_nat ((m * Z.of_nat n_old - 1) / m)) = (n_old - 1)%nat).
  { unfold Z.sub. rewrite Z.div_add_l' by lia.
    assert (H2 : ((- (1)) / m) = - (1)).
    destruct (dec (m = 1)); subst; [reflexivity|].
    rewrite Z_div_nz_opp_full, Z.div_small by (rewrite ?Z.mod_1_l; lia); lia. rewrite H2; lia. }
  assert (H1 : (m * Z.of_nat n_old - 1) mod m = m - 1).
  { destruct (dec (m = 1)); subst; [now rewrite Z.mod_1_r|].
    repeat (pull_Zmod; push_Zmod). rewrite Z.mod_1_l, Z.mod_neg_small; lia. }
  rewrite H, H1.
  destruct (Z.testbit (nth_default 0 f (n_old - 1)) (m - 1)); simpl.
  -  rewrite (uweight_eval_app) with (n := (n_old)%nat) by (rewrite ?repeat_length; lia).
     rewrite repeat_length. fold (ones m (n_new - n_old)).
     rewrite ones_spec,  uweight_eq_alt by lia. unfold Z.ones_at. rewrite Z.shiftl_mul_pow2 by nia.
     rewrite Z.pow_mul_r by lia.
     replace (m * Z.of_nat (n_new - n_old)) with (m * Z.of_nat n_new - m * Z.of_nat n_old) by nia; lia.
  - rewrite (uweight_eval_app) with (n := (n_old)%nat) by (rewrite ?repeat_length; lia).
    rewrite repeat_length; fold (zeros (n_new - n_old)); rewrite eval_zeros; lia.
Qed.

Lemma sat_sign_extend_length m n_old n_new f
      (Hn_old : (0 < n_old)%nat)
      (Hn_new : (n_old <= n_new)%nat)
      (Hf : (length f = n_old)) :
  length (tc_sign_extend m n_old n_new f) = n_new.
Proof. unfold tc_sign_extend; rewrite unfold_Let_In, app_length, repeat_length. lia. Qed.

Hint Rewrite sat_sign_extend_length : distr_length.
