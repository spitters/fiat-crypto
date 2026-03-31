Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Util.ZUtil.TwosComplement.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.

Lemma length_zero n :
  length (zero n) = n.
Proof. auto with distr_length. Qed.

Lemma eval_zero {weight : Z -> nat -> Z} machine_wordsize n :
  eval (weight machine_wordsize) n (zero n) = 0.
Proof. apply eval_zeros. Qed.

Lemma tc_eval_zero machine_wordsize n
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat) :
  tc_eval machine_wordsize n (zero n) = 0.
Proof. unfold tc_eval; rewrite eval_zero by lia; apply Z.twos_complement_zero; nia. Qed.
