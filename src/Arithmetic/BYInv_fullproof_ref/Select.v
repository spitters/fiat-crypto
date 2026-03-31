Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Util.ZUtil.Definitions.

Require Import Crypto.Util.Decidable.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Definition length_select := Positional.length_select.

Lemma tc_eval_select machine_wordsize n cond f g
      (Hf : length f = n)
      (Hg : length g = n) :
  tc_eval machine_wordsize n (select cond f g) = if dec (cond = 0)
                                                    then (tc_eval machine_wordsize n f)
                                                    else (tc_eval machine_wordsize n g).
Proof. unfold tc_eval; rewrite eval_select; auto; destruct (dec (cond = 0)); auto. Qed.

Lemma select_in_bounded machine_wordsize n cond f g
      (f_length : length f = n)
      (g_length : length g = n)
      (f_in_bounded : in_bounded machine_wordsize f)
      (g_in_bounded : in_bounded machine_wordsize g) :
  in_bounded machine_wordsize (Positional.select cond f g).
Proof.
  rewrite (Positional.select_eq Z.to_nat) with (n:=length f) by congruence.
  destruct (dec (cond = 0)); auto.
Qed.

Lemma select_push' n cond a b f : length a = n -> length b = n ->
                                  f (Positional.select cond a b) = Z.zselect cond (f a) (f b).
Proof. intros. apply Positional.select_push; congruence. Qed.

Lemma tc_eval_select_bounds machine_wordsize tc_limbs n cond f g K
      (f_length : length f = n)
      (g_length : length g = n)
      (f_bounds : - K < tc_eval machine_wordsize tc_limbs f < K)
      (g_bounds : - K < tc_eval machine_wordsize tc_limbs g < K) :
  - K < tc_eval machine_wordsize tc_limbs (Positional.select cond f g) < K.
Proof.
  rewrite (Positional.select_eq Z.of_nat) with (n:=n) by assumption. now destruct (dec (cond = 0)).
Qed.
