Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Lemma ones_spec m n
      (Hm : 0 <= m) :
  eval (uweight m) n (ones m n) = Z.ones (m * n).
Proof.
  unfold ones; induction n; simpl.
  - rewrite Z.mul_0_r; reflexivity.
  - rewrite eval_cons, uweight_eval_shift by (try apply repeat_length; lia).
    rewrite IHn, uweight_0, uweight_eq_alt, Z.pow_1_r by lia.
    rewrite !Z.ones_equiv, <- !Z.sub_1_r; ring_simplify.
    rewrite <- Z.pow_add_r by lia. repeat apply f_equal2; lia.
Qed.
