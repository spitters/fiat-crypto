Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Arithmetic.BYInv.EvalLemmas.
Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TwosComplement.

Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.


Import Positional.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.


Lemma firstn_in_bounded machine_wordsize f k
      (Hf : in_bounded machine_wordsize f) :
  in_bounded machine_wordsize (firstn k f).
Proof. intros y H. apply Hf. eapply In_firstn. eassumption. Qed.

Lemma firstn_eval m n f k
      (Hm : 0 < m)
      (Hf : length f = n)
      (Hf2 : in_bounded m f)
      (Hk : (k <= n)%nat) :
  eval (uweight m) k (firstn k f) = eval (uweight m) n f mod 2 ^ (m * k).
Proof.
  rewrite <- (firstn_skipn k f) at 2.
  replace n with (k + length (skipn k f))%nat by (rewrite skipn_length; lia).
  rewrite (uweight_eval_app' m ltac:(lia) k), uweight_eq_alt, <- Z.pow_mul_r
    by (rewrite ?firstn_length, ?Nat.min_l; lia).
  autorewrite with push_Zmod.
  rewrite Z.mod_0_l, Z.add_0_r,  Z.mod_mod
    by (try apply Z.pow_nonzero; nia).
  rewrite Z.mod_small. reflexivity.
  apply eval_bound. lia. apply firstn_in_bounded. assumption.
  rewrite firstn_length, Nat.min_l. reflexivity. lia.
Qed.

Lemma firstn_tc_eval m n f k
      (Hm : 0 < m)
      (Hf : length f = n)
      (Hf2 : in_bounded m f)
      (Hk : (0 < k <= n)%nat) :
  tc_eval m k (firstn k f) = Z.twos_complement (m * k) (tc_eval m n f).
Proof.
  unfold tc_eval.
  rewrite firstn_eval with (n:=n), Z.twos_complement_mod, Z.twos_complement_twos_complement_smaller_width;
    nia || reflexivity || assumption.
Qed.

Lemma firstn_tc_eval_small m n f k
      (Hm : 0 < m)
      (Hf : length f = n)
      (Hf2 : in_bounded m f)
      (Hf3 : - 2 ^ (m * Z.of_nat k - 1) <= tc_eval m n f < 2 ^ (m * Z.of_nat k - 1))
      (Hk : (0 < k <= n)%nat) :
  tc_eval m k (firstn k f) = tc_eval m n f.
Proof.
  rewrite firstn_tc_eval with (n := n) by assumption. unfold tc_eval.
  erewrite Z.twos_complement_smaller_bitwidth with (m':= m * Z.of_nat n) (m:= m * Z.of_nat k); [|nia|assumption].
  rewrite Z.twos_complement_twos_complement_smaller_width by lia. reflexivity.
Qed.

Lemma firstn_length_le n (f : list Z) :
  (n <= length f)%nat ->
  length (firstn n f) = n.
Proof.
  intros. rewrite firstn_length, Nat.min_l; auto.
Qed.
