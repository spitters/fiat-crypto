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
Require Import Crypto.Util.ListUtil.

Import Positional.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z.

(**************************************************** *)
(**Functional correctness of multi-limb logical shift *)
(**************************************************** *)

Lemma eval_shiftr machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = n)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
  eval (uweight machine_wordsize) n (shiftr machine_wordsize n f) =
  eval (uweight machine_wordsize) n f >> 1.
Proof.
  generalize dependent n. induction f; intros; subst.
  - unfold shiftr; simpl; rewrite eval0; reflexivity.
  - unfold shiftr; simpl.
    rewrite eval_cons, uweight_eval_shift by lia.
    destruct f; simpl in *.
    + rewrite
        eval_cons, uweight_0, eval0, ListUtil.nth_default_cons, uweight_eq_alt',
        Z.mul_0_r, !Z.add_0_r, !Z.mul_1_l; reflexivity.
    + rewrite eval_cons, uweight_eval_shift;
        try (rewrite ?length_snoc, ?map_length, ?seq_length; lia).
      replace ((map _ _) ++ _) with (shiftr machine_wordsize (S (length f)) (z :: f)).
      * rewrite IHf; try (intros; try apply Hz; tauto).
        rewrite uweight_0, ListUtil.nth_default_cons_S, uweight_eq_alt'.
        rewrite !ListUtil.nth_default_cons, !Z.mul_1_l, !Z.mul_1_r.
        rewrite <- !Z.div2_spec, !Z.div2_div, Z.div2_split by lia.
        rewrite eval_cons at 2 by reflexivity.
        rewrite uweight_eval_shift, uweight_0, uweight_eq_alt, Z.pow_1_r by lia.
        rewrite PullPush.Z.add_mod_r, PullPush.Z.mul_mod_l.
        replace 2 with (2 ^ 1) at 7 by trivial.
        rewrite Modulo.Z.mod_same_pow, Z.mul_0_l by lia. ring_simplify.
        rewrite Z.mul_1_l, Z.add_0_r, Z.truncating_shiftl_mod by lia. rewrite Z.lor_add; try ring.
        destruct (Z.odd z) eqn:E; rewrite Zmod_odd, E.
        ** specialize (Hz a (or_introl eq_refl)).
           rewrite Z.mul_1_r, Z.land_div2; rewrite ?Z.sub_simpl_r; lia.
        ** now rewrite Z.mul_0_r, Z.land_0_r.
      * unfold shiftr. replace (S (length f) - 1)%nat with (length f) by lia.
        apply f_equal2.
        ** apply map_seq_ext; intros; [|lia].
           rewrite Nat.sub_0_r, Nat.add_1_r.
           rewrite !(ListUtil.nth_default_cons_S _ a); reflexivity.
        ** now rewrite ListUtil.nth_default_cons_S.
Qed.
