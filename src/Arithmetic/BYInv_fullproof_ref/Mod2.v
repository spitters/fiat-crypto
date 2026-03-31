Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ListUtil.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.

(******************************************* *)
(**Correctness of mod2 including correctness *)
(******************************************* *)

Lemma mod2_cons a f : mod2 (a :: f) = a mod 2.
Proof. unfold mod2. now rewrite ListUtil.nth_default_cons. Qed.

Lemma mod2_odd f :
  mod2 f = Z.b2z (odd f).
Proof. unfold mod2, odd; rewrite Zmod_odd; now destruct (Z.odd (nth_default 0 f 0)). Qed.

Lemma eval_mod2 machine_wordsize n f
      (Hf : length f = n)
      (Hmw : 0 < machine_wordsize) :
  (eval (uweight machine_wordsize) n f) mod 2 = mod2 f.
Proof.
  generalize dependent Hf. generalize dependent n.
  induction f; intros; simpl in *; subst.
  - unfold mod2. rewrite eval0; reflexivity.
  - rewrite eval_cons by trivial. rewrite uweight_eval_shift by lia.
    rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, IHf by reflexivity.
    unfold uweight, ModOps.weight; simpl.
    rewrite Z.mul_0_r, Z.mul_1_r, !Zdiv_1_r, !Z.opp_involutive, !Z.pow_0_r, Z.mul_1_l.
    rewrite <- Zmult_mod_idemp_l, PullPush.Z.mod_pow_full, Z_mod_same_full, Z.pow_0_l by assumption.
    rewrite Zmod_0_l, Z.add_0_r; reflexivity.
Qed.

Lemma tc_eval_mod2 machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hf : length f = n) :
  (tc_eval machine_wordsize n f) mod 2 = mod2 f.
Proof. unfold tc_eval; rewrite Z.twos_complement_mod2, eval_mod2; nia. Qed.

Lemma mod2_dec g : {mod2 g = 0} + {mod2 g = 1}.
Proof. rewrite mod2_odd. destruct (odd g); [right|left]; reflexivity. Qed.
