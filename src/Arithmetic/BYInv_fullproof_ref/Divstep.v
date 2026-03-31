Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModOps.

Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.ArithmeticShiftr.
Require Import Crypto.Arithmetic.BYInv.Shiftr.
Require Import Crypto.Arithmetic.BYInv.Select.
Require Import Crypto.Arithmetic.BYInv.TCAdd.
Require Import Crypto.Arithmetic.BYInv.TCOpp.
Require Import Crypto.Arithmetic.BYInv.Mod2.
Require Import Crypto.Arithmetic.BYInv.One.
Require Import Crypto.Arithmetic.BYInv.Zero.
Require Import Crypto.Arithmetic.BYInv.Ref.
Require Import Crypto.Arithmetic.BYInv.WordByWordMontgomery.
Require Import Crypto.Arithmetic.BYInv.Hints.

Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.Odd.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.ArithmeticShiftr.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.
Require Import Crypto.Util.ZUtil.TwosComplementPos.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Import ListNotations.

Local Coercion Z.of_nat : nat >-> Z.
Local Open Scope Z_scope.

(** An implementation of the divsteps2 algorithm from "Fast constant-time gcd computation and modular inversion."
   by D. J. Bernstein et al. See the file inversion-c/readme.txt for generation of C-code.
   For a C-implementation using this generated code to implement modular inversion, see inversion-c/test-inversion.c. **)

Module Export WordDivstep.

  Section __.

    Context
      (machine_wordsize : Z).

    Local Notation tc := (Z.twos_complement machine_wordsize).

    Lemma twos_complement_word_full_divsteps_d_bound d f g u v q r n K
          (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - (Z.of_nat n))
          (mw1 : 1 < machine_wordsize)
          (d_bounds : - K <= tc d <= K) :
      let '(d1,_,_,_,_,_,_) :=
        fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data)
                  (seq 0 n)
                  (d,f,g,u,v,q,r) in
      - K - Z.of_nat n <= tc d1 <= K + Z.of_nat n.
    Proof.
      induction n; intros.
      - rewrite Z.add_0_r, Z.sub_0_r in *; cbn. assumption.
      - rewrite seq_snoc, fold_left_app.
        replace (Z.of_nat (S n)) with (1 + Z.of_nat n) in * by lia.
        cbn -[Z.mul Z.add].
        destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.
        cbn -[Z.mul Z.add].

        rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos_spec, Zmod_odd by lia.
        destruct (0 <? Z.twos_complement machine_wordsize d1);
          destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]; try assumption;
          rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?Z.twos_complement_opp_spec, ?Z.twos_complement_one; try lia;
          rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?Z.twos_complement_opp_spec, ?Z.twos_complement_one; try lia.
    Qed.

    Lemma twos_complement_word_full_divsteps_f_odd d f g u v q r n
          (mw0 : 0 < machine_wordsize)
          (fodd : Z.odd f = true) :
      let '(_,f1,_,_,_,_,_) :=
        fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data)
                  (seq 0 n)
                  (d,f,g,u,v,q,r) in
      Z.odd f1 = true.
    Proof.
      induction n; [assumption|].
      rewrite seq_snoc, fold_left_app.
      destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.
      cbn -[Z.mul Z.add].
      rewrite !Zselect.Z.zselect_correct.
      destruct (dec _); [assumption|].
      rewrite Zmod_odd in *. destruct (Z.odd g1). reflexivity. rewrite Z.land_0_r in n0. contradiction.
    Qed.

    Lemma twos_complement_word_full_divsteps_bounds d f g u v q r n K
          (HK : 0 < K)
          (HK2 : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 2))
          (mw1 : 1 < machine_wordsize)
          (fodd : Z.odd f = true)

          (d_bounds : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) <=
                        tc d <= 2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n)
          (u_bounds : - K <= tc u <= K)
          (v_bounds : - K <= tc v <= K)
          (q_bounds : - K <= tc q <= K)
          (r_bounds : - K <= tc r <= K)
          (u_pos : 0 <= u < 2 ^ machine_wordsize)
          (v_pos : 0 <= v < 2 ^ machine_wordsize)
          (q_pos : 0 <= q < 2 ^ machine_wordsize)
          (r_pos : 0 <= r < 2 ^ machine_wordsize) :
      let '(_,f1,g1,u1,v1,q1,r1) :=
        fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data)
                  (seq 0 n)
                  (d,f,g,u,v,q,r) in
        - 2 ^ n * K <= tc u1 <= 2 ^ n * K /\
        - 2 ^ n * K <= tc v1 <= 2 ^ n * K /\
        - 2 ^ n * K <= tc q1 <= 2 ^ n * K /\
        - 2 ^ n * K <= tc r1 <= 2 ^ n * K /\
        0 <= u1 < 2 ^ machine_wordsize /\
        0 <= v1 < 2 ^ machine_wordsize /\
        0 <= q1 < 2 ^ machine_wordsize /\
        0 <= r1 < 2 ^ machine_wordsize.
    Proof.
      assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).

      induction n; intros.
      - cbn -[Z.mul Z.add]; lia.
      - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
        rewrite <- Z.pow_mul_base in * by lia.

        epose proof twos_complement_word_full_divsteps_d_bound  _ f g u v q r n _ _ _ d_bounds.
        epose proof twos_complement_word_full_divsteps_f_odd d f g u v q r n _ _.

        rewrite seq_snoc, fold_left_app.

        cbn -[Z.mul Z.add].
        destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E.

        specialize (IHn ltac:(lia) ltac:(lia)).
        assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
          (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).

        cbn -[Z.mul Z.add].
        rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos_spec, Zmod_odd by lia.
        destruct (0 <? Z.twos_complement machine_wordsize d1);
          destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add].
        + rewrite Zmod_odd, !Z.twos_complement_opp_odd by (try assumption; lia). cbn -[Z.mul Z.add].
          rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full, !Z.twos_complement_opp_spec by (try rewrite Z.twos_complement_opp_spec; lia).
          assert (forall a b, a <= b -> a / 2 <= b / 2) by (intros; apply Z.div_le_mono; lia).
          repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia.
        + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
          rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
          repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia.
        + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add].
          rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
          repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia.
        + rewrite Zmod_odd, g1odd; cbn -[Z.mul Z.add]; rewrite !Z.add_0_r.
          rewrite !Z.twos_complement_mod, !Z.twos_complement_add_full by lia.
          repeat split; try apply div_lt_lower_bound; try apply Z.div_lt_upper_bound; try apply Z.mod_pos_bound; try lia.

          Unshelve. all: lia || assumption.
    Qed.

    Local Ltac splits :=
      repeat match goal with
             | |- (_, _) = _ => apply f_equal2
             end.

    Theorem twos_complement_word_full_divstep_iter_correct d f g u v q r n K
            (fodd : Z.odd f = true)
            (HK : 2 ^ Z.of_nat n * K <= 2 ^ (machine_wordsize - 2))
            (HK2 : 0 < K)
            (mw1 : 2 < machine_wordsize)
            (nmw : n < machine_wordsize)
            (overflow_d : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) <=
                            tc d <= 2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n)
            (overflow_u : - K <= tc u <= K)
            (overflow_v : - K <= tc v <= K)
            (overflow_q : - K <= tc q <= K)
            (overflow_r : - K <= tc r <= K)
            (u_pos : 0 <= u < 2 ^ machine_wordsize)
            (v_pos : 0 <= v < 2 ^ machine_wordsize)
            (q_pos : 0 <= q < 2 ^ machine_wordsize)
            (r_pos : 0 <= r < 2 ^ machine_wordsize)
            (Hf2 : 0 <= f < 2^machine_wordsize)
            (Hg2 : 0 <= g < 2^machine_wordsize) :
      let '(d1,f1,g1,u1,v1,q1,r1) :=
        fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data)
                  (seq 0 n)
                  (d,f,g,u,v,q,r)  in
      (tc d1, tc f1 mod 2 ^ (machine_wordsize - Z.of_nat n), tc g1 mod 2 ^ (machine_wordsize - Z.of_nat n), tc u1, tc v1, tc q1, tc r1) =
        let '(d1',f1',g1',u1',v1',q1',r1') :=
          Nat.iter n divstep_uvqr (tc d, f, g, tc u, tc v, tc q, tc r) in
        (d1', f1' mod 2 ^ (machine_wordsize - Z.of_nat n), g1' mod 2 ^ (machine_wordsize - Z.of_nat n), u1',v1',q1',r1').
    Proof.
      assert (0 < 2 ^ machine_wordsize) by (apply Z.pow_pos_nonneg; lia).
      assert (2 * 2 ^ (machine_wordsize - 2) = 2 ^ (machine_wordsize - 1)) by
        (rewrite Pow.Z.pow_mul_base; try apply f_equal2; lia).

      induction n.
      - simpl. rewrite Z.sub_0_r; rewrite !Z.twos_complement_mod'; auto.
      - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
        rewrite <- Z.pow_mul_base in * by lia.

        epose proof twos_complement_word_full_divsteps_d_bound _ f g u v q r n _ _ _ overflow_d.
        epose proof twos_complement_word_full_divsteps_f_odd d f g u v q r n _ _.
        epose proof twos_complement_word_full_divsteps_bounds d f g u v q r n K _ _ _ _ _ _ _ _ _ _ _ _ _.
        rewrite Nat_iter_S.

        rewrite seq_snoc, fold_left_app. cbn -[Z.mul Z.add].
        destruct (fold_left (fun (data : Z * Z * Z * Z * Z * Z * Z) (_ : nat)  => twos_complement_word_full_divstep_aux machine_wordsize data) _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1] eqn:E1.
        destruct (Nat.iter _ _ _) as [[[[[[d1' f1'] g1'] u1'] v1'] q1'] r1'] eqn:E2 .

        assert ((Z.twos_complement machine_wordsize d1, Z.twos_complement machine_wordsize f1 mod 2 ^ (machine_wordsize - Z.of_nat n),
                  Z.twos_complement machine_wordsize g1 mod 2 ^ (machine_wordsize - Z.of_nat n), Z.twos_complement machine_wordsize u1,
                  Z.twos_complement machine_wordsize v1, Z.twos_complement machine_wordsize q1, Z.twos_complement machine_wordsize r1) =
                  (d1', f1' mod 2 ^ (machine_wordsize - Z.of_nat n), g1' mod 2 ^ (machine_wordsize - Z.of_nat n), u1', v1', q1', r1')).
        apply IHn; lia.
        inversion H4.

        rewrite Z.twos_complement_mod_smaller_pow in H7 by lia.
        rewrite Z.twos_complement_mod_smaller_pow in H8 by lia.

        cbn -[Z.mul Z.add].
        unfold divstep_uvqr.
        rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos_spec, Zmod_odd by lia.

        assert (Z.odd g1 = Z.odd g1').
        { rewrite <- (Z.odd_mod2m (machine_wordsize - Z.of_nat n) g1'), <- H8, Z.odd_mod2m by lia; reflexivity. }
        rewrite <- H5.
        rewrite Zmod_odd.
        destruct (0 <? Z.twos_complement machine_wordsize d1);
          destruct (Z.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]; rewrite ?Z.twos_complement_opp_odd by (try assumption; lia); cbn -[Z.mul Z.add].
        + splits.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_opp_spec, Z.twos_complement_one by
              (try rewrite Z.twos_complement_opp_spec, Z.twos_complement_one; lia); lia.
          *
            rewrite Z.twos_complement_mod_smaller_pow, <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)) by lia.
            rewrite H8, Z.mod_pow_same_base_smaller; lia.
          * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod by (try apply Z.mod_pos_bound; lia).
            rewrite !Z.mod_pull_div by (apply Z.pow_nonneg; lia).
            apply f_equal2; [|reflexivity].
            replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)) by
              (rewrite Z.mul_comm, Z.pow_mul_base; [apply f_equal2|]; lia).
            rewrite Z.twos_complement_opp_correct, Z.twos_complement_mod_smaller_pow, <- Zplus_mod_idemp_l, Z.mod_pow_same_base_smaller, Zplus_mod_idemp_l by lia.
            push_Zmod. rewrite H7, H8. pull_Zmod.
            apply f_equal2; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full,Z.twos_complement_opp_spec; try rewrite Z.twos_complement_opp_spec; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_opp_spec; try rewrite Z.twos_complement_opp_spec; lia.
        + rewrite g1odd, !Z.add_0_r by lia; cbn -[Z.mul Z.add]. splits.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one;
              try rewrite Z.twos_complement_one; lia.
          * rewrite Z.twos_complement_mod_smaller_pow, <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)), H7, Z.mod_pow_same_base_smaller; lia.
          * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod by (try apply Z.mod_pos_bound; lia).
            rewrite !Z.mod_pull_div by (apply Z.pow_nonneg; lia).
            apply f_equal2; [|reflexivity].
            replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)) by
              (rewrite Z.mul_comm, Z.pow_mul_base; [apply f_equal2|]; lia).
            rewrite Z.twos_complement_mod_smaller_pow; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
          * rewrite Z.twos_complement_mod; lia.
          * rewrite Z.twos_complement_mod; lia.
        + rewrite g1odd by lia; cbn -[Z.mul Z.add]. splits.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one;
              try rewrite Z.twos_complement_one; lia.
          * rewrite Z.twos_complement_mod_smaller_pow, <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)), H7, Z.mod_pow_same_base_smaller; lia.
          * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod by (try apply Z.mod_pos_bound; lia).
            rewrite !Z.mod_pull_div by (apply Z.pow_nonneg; lia).
            apply f_equal2; [|reflexivity].
            replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)) by
              (rewrite Z.mul_comm, Z.pow_mul_base; [apply f_equal2|]; lia).
            rewrite Z.twos_complement_mod_smaller_pow by lia.
            push_Zmod. rewrite H7, H8. pull_Zmod.
            apply f_equal2; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
        + rewrite  g1odd, !Z.add_0_r by lia; cbn -[Z.mul Z.add]. splits.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one;
              try rewrite Z.twos_complement_one; lia.
          * rewrite Z.twos_complement_mod_smaller_pow, <- Z.mod_pow_same_base_smaller with (n:=(machine_wordsize - Z.of_nat n)), H7, Z.mod_pow_same_base_smaller; lia.
          * rewrite Z.arithmetic_shiftr1_spec, Z.twos_complement_mod by (try apply Z.mod_pos_bound; lia).
            rewrite !Z.mod_pull_div by (apply Z.pow_nonneg; lia).
            apply f_equal2; [|reflexivity].
            replace (2 ^ (machine_wordsize - (Z.of_nat n + 1)) * 2) with (2 ^ (machine_wordsize - Z.of_nat n)) by
              (rewrite Z.mul_comm, Z.pow_mul_base; [apply f_equal2|]; lia).
            rewrite Z.twos_complement_mod_smaller_pow; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
          * rewrite Z.twos_complement_mod, Z.twos_complement_add_full; lia.
          * rewrite Z.twos_complement_mod; lia.
          * rewrite Z.twos_complement_mod; lia.

            Unshelve.
            all: try lia; try assumption.
    Qed.

  End __.

End WordDivstep.

Module Export WordByWordMontgomery.

  Import BYInv.WordByWordMontgomery.WordByWordMontgomery.
  Import Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
  Import Definitions.WordByWordMontgomery.

  Section __.

    Context
      (machine_wordsize : Z)
      (tc_limbs : nat)
      (mont_limbs : nat)
      (m : Z)
      (m_bounds : 1 < m < (2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs))
      (r' : Z)
      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m' : Z)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (mw1 : 1 < machine_wordsize)
      (tc_limbs0 : (0 < tc_limbs)%nat)
      (mont_limbs0 : (0 < mont_limbs)%nat).

    Notation eval := (@WordByWordMontgomery.eval machine_wordsize mont_limbs).
    Notation tc_eval := (tc_eval machine_wordsize tc_limbs).
    Notation tc := (Z.twos_complement machine_wordsize).
    Notation divstep_aux := (divstep_aux machine_wordsize mont_limbs tc_limbs m).
    Notation divstep := (divstep machine_wordsize mont_limbs tc_limbs m).
    Notation valid := (valid machine_wordsize mont_limbs m).
    Notation addmod := (addmod machine_wordsize mont_limbs m).
    Notation oppmod := (oppmod machine_wordsize mont_limbs m).
    Notation from_montgomerymod := (from_montgomerymod machine_wordsize mont_limbs m m').
    Notation in_bounded := (in_bounded machine_wordsize).

    #[local]
    Hint Resolve
         (length_addmod machine_wordsize mont_limbs m ltac:(lia))
         (length_oppmod machine_wordsize mont_limbs m ltac:(lia))
      : len.

    #[local]
    Hint Resolve
         (zero_valid machine_wordsize mont_limbs m ltac:(lia))
         (addmod_valid machine_wordsize mont_limbs m r' m' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (oppmod_valid machine_wordsize mont_limbs m r' m' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      : valid.
    #[local] Hint Resolve (select_in_bounded machine_wordsize tc_limbs) : in_bounded.

    Lemma divstep_iter_d_bounds d f g v r n K
          (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - (Z.of_nat n))
          (d_bounds : - K < tc d < K) :
      let '(d1,_,_,_,_) := fold_left (fun data i => divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      - K - Z.of_nat n < tc d1 < K + Z.of_nat n.
    Proof.
      induction n; intros.
      - cbn; lia.

      - rewrite seq_snoc, fold_left_app.
        destruct (fold_left _ _ _) as [[[[d1 f1] g1] v1] r1] eqn:E.
        cbn -[Z.mul Z.add].
        rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos'_spec, mod2_odd by lia.
        destruct (0 <? tc d1);
          destruct (Definitions.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]; try assumption;
          repeat (rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?Z.twos_complement_opp'_spec, ?Z.twos_complement_one; try lia).
    Qed.

    Ltac t := repeat match goal with
                     | |- _ => assumption
                     | |- _ < tc_eval (tc_opp _ _ _) < _ => apply tc_eval_tc_opp_bounds
                     | |- _ < tc_eval (Positional.select _ _ _) < _ => simple apply tc_eval_select_bounds with (n:=tc_limbs)
                     | |- _ < tc_eval (zero _) < _ => rewrite tc_eval_zero; lia
                     | |- _ /\ _ => split
                     | |- in_bounded _ => auto with in_bounded
                     | |- length _ = _ =>  auto with len
                     | |- valid _ => auto with valid
                     | |- _ < _ / _ => apply div_lt_lower_bound; lia
                     | |- _ / _ < _ => apply Z.div_lt_upper_bound; lia
                     end.

    Lemma divstep_iter_bounds d f g v r n
          (fodd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (d_bounds : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n) < tc d < 2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(_,f1,g1,v1,r1) :=
        fold_left (fun data i => divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      length f1 = tc_limbs
      /\ length g1 = tc_limbs
      /\ length v1 = mont_limbs
      /\ length r1 = mont_limbs
      /\ Z.odd (tc_eval f1) = true
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ valid v1
      /\ valid r1
      /\ in_bounded f1
      /\ in_bounded g1.
    Proof.
      assert (mw0 : 0 < machine_wordsize) by lia.
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1))
        by (rewrite Pow.Z.pow_mul_base by lia; f_equal; lia).
      induction n.
      - easy.
      - rewrite seq_snoc, fold_left_app. simpl.
        pose proof divstep_iter_d_bounds d f g v r n ((2 ^ (machine_wordsize - 1) - 1 - Z.of_nat n)) ltac:(lia) ltac:(lia).
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => divstep_aux data) (seq 0 n) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        specialize (IHn ltac:(lia)) as [f1_length [g1_length [v1_length [r1_length [f1_odd [f1_bounds [f1_in_bounds [g1_bounds [g1_in_bounds [v1_valid r1_valid]]]]]]]]]].
        unfold divstep_aux. simpl.
        do 4 (split; auto with len).
        rewrite tc_eval_arithmetic_shiftr1, tc_eval_tc_add, !tc_eval_select, tc_eval_tc_opp, select_push' with (n:=tc_limbs), tc_opp_mod2, Z.twos_complement_pos'_spec, <- !(tc_eval_mod2 machine_wordsize tc_limbs), !Zmod_odd; auto with len; try lia.
        destruct (0 <? tc d1);
          destruct (Z.odd (tc_eval g1)) eqn:g'_odd; rewrite ?f1_odd, ?tc_eval_zero; auto; simpl; t.
        all: t.
    Qed.

    Lemma divstep_full d f g v r
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (d_bounds : - 2 ^ (machine_wordsize - 1) + 1 < tc d < 2 ^ (machine_wordsize - 1) - 1)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := (divstep_aux (d, f, g, v, r)) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m) =
        divstep_vr_mod m (tc d, tc_eval f, tc_eval g, eval v mod m, eval r mod m).
    Proof.
      assert (mw0 : 0 < machine_wordsize) by lia.
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1))
        by (rewrite Pow.Z.pow_mul_base by lia; f_equal; lia).
      destruct m_bounds.
      cbn -[tc_add tc_opp Z.mul Z.sub Z.add oppmod].

      rewrite tc_eval_arithmetic_shiftr1, tc_eval_tc_add, !tc_eval_select, tc_eval_tc_opp, select_push' with (n:=tc_limbs), tc_opp_mod2, Z.twos_complement_pos'_spec, <- !(tc_eval_mod2 machine_wordsize tc_limbs), !Zmod_odd, !Zselect.Z.zselect_correct, !eval_addmod', f_odd; t; try lia.
      destruct (0 <? tc d); destruct (Z.odd (tc_eval g)) eqn:g'_odd;
        cbn -[Z.add Z.mul oppmod]; rewrite !(Positional.select_eq Z.to_nat) with (n:=mont_limbs) by t;
        repeat match goal with
               | |- (_, _) = (_, _) => apply f_equal2; cbn -[Z.add Z.mul oppmod]
               | |- context[tc] => autorewrite with Ztc; try lia
               | |- context[tc_eval (zero _)] => rewrite tc_eval_zero by lia
               | |- _ => pull_Zmod; f_equal; lia
               end; try reflexivity.
      - push_Zmod. rewrite eval_oppmod' by (t; lia). pull_Zmod.
        f_equal; lia.
      - push_Zmod. change eval with (Positional.eval (uweight machine_wordsize) mont_limbs).
        rewrite eval_zero. pull_Zmod. f_equal; lia.
      - push_Zmod. change eval with (Positional.eval (uweight machine_wordsize) mont_limbs).
        rewrite eval_zero. pull_Zmod. f_equal; lia.
    Qed.

    Lemma divstep_iter_correct d f g v r n
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = mont_limbs)
          (r_length : length r = mont_limbs)
          (d_bounds : - 2 ^ (machine_wordsize - 1) + Z.of_nat n < tc d < 2 ^ (machine_wordsize - 1) - Z.of_nat n)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (v_valid : valid v)
          (r_valid : valid r)
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := fold_left (fun data i => divstep_aux data) (seq 0 n) (d,f,g,v,r) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m) =
        Nat.iter n (divstep_vr_mod m) (tc d, tc_eval f, tc_eval g, eval v mod m, eval r mod m).
    Proof.
      induction n.
      - reflexivity.
      - rewrite seq_snoc, fold_left_app. simpl.
        pose proof divstep_iter_d_bounds d f g v r n (2 ^ (machine_wordsize - 1) - Z.of_nat (S n)) ltac:(lia) ltac:(lia).
        pose proof divstep_iter_bounds d f g v r n f_odd f_length g_length v_length r_length ltac:(lia) f_bounds g_bounds v_valid r_valid f_in_bounded g_in_bounded.
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => divstep_aux data) (seq 0 n) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        destruct H0 as [? [? [? [? [? [? [? [? [? [?]]]]]]]]]].
        rewrite <- IHn by lia.
        apply divstep_full; try assumption; lia.
    Qed.
  End __.
End WordByWordMontgomery.

Module Export UnsaturatedSolinas.

  Import Definitions.UnsaturatedSolinas.
  Import BYInv.UnsaturatedSolinas.UnsaturatedSolinas.

  Section __.

    Context (limbwidth_num limbwidth_den : Z)
            (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
            (machine_wordsize : Z)
            (s nn: Z)
            (c : list (Z*Z))
            (n : nat)
            (tc_limbs : nat)
            (len_c : nat)
            (idxs : list nat)
            (len_idxs : nat)
            (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
            (Hn_nz : n <> 0%nat)
            (Hc : length c = len_c)
            (Hidxs : length idxs = len_idxs)
            (mw1 : 1 < machine_wordsize)
            (tc_limbs0 : (0 < tc_limbs)%nat)
            (n0 : (0 < n)%nat).

    #[local] Notation eval := (Positional.eval (weight limbwidth_num limbwidth_den) n).

    Context (balance : list Z)
            (length_balance : length balance = n)
            (eval_balance : eval balance mod (s - Associational.eval c) = 0).

    #[local] Notation divstep_aux := (divstep_aux limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs idxs balance).
    #[local] Notation divstep := (divstep limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs idxs balance).
    #[local] Notation tc_eval := (tc_eval machine_wordsize tc_limbs).
    #[local] Notation tc := (Z.twos_complement machine_wordsize).
    #[local] Notation m := (s - Associational.eval c).
    #[local] Notation in_bounded := (in_bounded machine_wordsize).

    #[local] Notation addmod := (addmod limbwidth_num limbwidth_den n).
    #[local] Notation oppmod := (oppmod limbwidth_num limbwidth_den n balance).
    #[local] Notation carrymod := (carrymod limbwidth_num limbwidth_den s c n idxs).

    #[local] Hint Resolve (select_in_bounded machine_wordsize tc_limbs) : in_bounded.

    Ltac t := repeat match goal with
                     | |- _ => assumption
                     | |- _ < tc_eval (tc_opp _ _ _) < _ => apply tc_eval_tc_opp_bounds
                     | |- _ < tc_eval (Positional.select _ _ _) < _ => simple apply tc_eval_select_bounds with (n:=tc_limbs)
                     | |- _ < tc_eval (zero _) < _ => rewrite tc_eval_zero; lia
                     | |- _ /\ _ => split
                     | |- in_bounded _ => auto with in_bounded
                     | |- length _ = _ =>  auto with len
                     | |- _ < _ / _ => apply div_lt_lower_bound; lia
                     | |- _ / _ < _ => apply Z.div_lt_upper_bound; lia
                     end.

    Lemma divstep_iter_d_bounds d f g v r k K
          (Kpos : 0 <= K < 2 ^ (machine_wordsize - 1) - (Z.of_nat k))
          (d_bounds : - K < tc d < K) :
      let '(d1,_,_,_,_) := fold_left (fun data i => divstep_aux data) (seq 0 k) (d,f,g,v,r) in
      - K - Z.of_nat k < tc d1 < K + Z.of_nat k.
    Proof.
      induction k; intros.
      - cbn; lia.
      - rewrite seq_snoc, fold_left_app.
        destruct (fold_left _ _ _) as [[[[d1 f1] g1] v1] r1] eqn:E.
        cbn -[Z.mul Z.add].
        rewrite !Zselect.Z.zselect_correct, Z.twos_complement_pos'_spec, mod2_odd by lia.
        destruct (0 <? tc d1);
          destruct (Definitions.odd g1) eqn:g1odd; cbn -[Z.mul Z.add]; try assumption;
          repeat (rewrite ?Z.twos_complement_mod, ?Z.twos_complement_add_full, ?Z.twos_complement_opp'_spec, ?Z.twos_complement_one; try lia).
    Qed.

    Lemma divstep_iter_bounds d f g v r k
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = n)
          (r_length : length r = n)
          (d_bounds : - (2 ^ (machine_wordsize - 1) - 1 - Z.of_nat k) < tc d < 2 ^ (machine_wordsize - 1) - 1 - Z.of_nat k)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(_,f1,g1,v1,r1) :=
        fold_left (fun data i => divstep_aux data) (seq 0 k) (d,f,g,v,r) in
      length f1 = tc_limbs
      /\ length g1 = tc_limbs
      /\ length v1 = n
      /\ length r1 = n
      /\ Z.odd (tc_eval f1) = true
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g1 < 2 ^ (machine_wordsize * tc_limbs - 2)
      /\ in_bounded f1
      /\ in_bounded g1.
    Proof.
      assert (mw0 : 0 < machine_wordsize) by lia.
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1))
        by (rewrite Pow.Z.pow_mul_base by lia; f_equal; lia).
      induction k.
      - easy.
      - rewrite seq_snoc, fold_left_app. simpl.
        pose proof divstep_iter_d_bounds d f g v r k ((2 ^ (machine_wordsize - 1) - 1 - Z.of_nat k)) ltac:(lia) ltac:(lia).
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => divstep_aux data) (seq 0 k) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        specialize (IHk ltac:(lia)) as [f1_length [g1_length [v1_length [r1_length [f1_odd [f1_bounds [g1_bounds [f1_in_bounds g1_in_bounds]]]]]]]].
        unfold divstep_aux. simpl.
        do 4 (split; auto 6 with len).
        rewrite tc_eval_arithmetic_shiftr1, tc_eval_tc_add, !tc_eval_select, tc_eval_tc_opp, select_push' with (n:=tc_limbs), tc_opp_mod2, Z.twos_complement_pos'_spec, <- !(tc_eval_mod2 machine_wordsize tc_limbs), !Zmod_odd; auto with len; try lia.
        destruct (0 <? tc d1);
          destruct (Z.odd (tc_eval g1)) eqn:g'_odd; rewrite ?f1_odd, ?tc_eval_zero; auto; simpl; t.
        all: t.
    Qed.

    Lemma divstep_full d f g v r
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = n)
          (r_length : length r = n)
          (d_bounds : - 2 ^ (machine_wordsize - 1) + 1 < tc d < 2 ^ (machine_wordsize - 1) - 1)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := (divstep_aux (d, f, g, v, r)) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m) =
        divstep_vr_mod m (tc d, tc_eval f, tc_eval g, eval v mod m, eval r mod m).
    Proof.
      assert (mw0 : 0 < machine_wordsize) by lia.
      assert (2 * 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) = 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1))
        by (rewrite Pow.Z.pow_mul_base by lia; f_equal; lia).
      unfold divstep_aux.
      cbn -[tc_add tc_opp Z.opp Z.mul Z.sub Z.add oppmod addmod Positional.select].
      rewrite tc_eval_arithmetic_shiftr1, tc_eval_tc_add, !tc_eval_select, tc_eval_tc_opp, select_push' with (n:=tc_limbs), tc_opp_mod2, Z.twos_complement_pos'_spec, <- !(tc_eval_mod2 machine_wordsize tc_limbs), !Zmod_odd, !Zselect.Z.zselect_correct, !eval_carrymod, !eval_addmod, !Positional.eval_select, f_odd, !eval_zero; t; try lia.
      destruct (0 <? tc d); destruct (Z.odd (tc_eval g)) eqn:g'_odd;
        cbn -[Z.add Z.mul oppmod];
        repeat match goal with
               | |- (_, _) = (_, _) => apply f_equal2; cbn -[Z.add Z.mul oppmod]
               | |- context[tc] => autorewrite with Ztc; try lia
               | |- context[tc_eval (zero _)] => rewrite tc_eval_zero by lia
               | |- _ => pull_Zmod; f_equal; lia
               end; try reflexivity.
      - push_Zmod. rewrite eval_carrymod, eval_oppmod by (t; lia).
        pull_Zmod. f_equal. lia.
    Qed.

    Lemma divstep_iter_correct d f g v r k
          (f_odd : Z.odd (tc_eval f) = true)
          (f_length : length f = tc_limbs)
          (g_length : length g = tc_limbs)
          (v_length : length v = n)
          (r_length : length r = n)
          (d_bounds : - 2 ^ (machine_wordsize - 1) + Z.of_nat k < tc d < 2 ^ (machine_wordsize - 1) - Z.of_nat k)
          (f_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval f < 2 ^ (machine_wordsize * tc_limbs - 2))
          (g_bounds : - 2 ^ (machine_wordsize * tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * tc_limbs - 2))
          (f_in_bounded : in_bounded f)
          (g_in_bounded : in_bounded g) :
      let '(d1,f1,g1,v1,r1) := fold_left (fun data i => divstep_aux data) (seq 0 k) (d,f,g,v,r) in
      (tc d1, tc_eval f1, tc_eval g1, eval v1 mod m, eval r1 mod m) =
        Nat.iter k (divstep_vr_mod m) (tc d, tc_eval f, tc_eval g, eval v mod m, eval r mod m).
    Proof.
      induction k.
      - reflexivity.
      - rewrite seq_snoc, fold_left_app. simpl.
        pose proof divstep_iter_d_bounds d f g v r k (2 ^ (machine_wordsize - 1) - Z.of_nat (S k)) ltac:(lia) ltac:(lia).
        pose proof divstep_iter_bounds d f g v r k f_odd f_length g_length v_length r_length ltac:(lia) f_bounds g_bounds f_in_bounded g_in_bounded.
        destruct (fold_left (fun (data : Z * list Z * list Z * list Z * list Z) (_ : nat) => divstep_aux data) (seq 0 k) (d, f, g, v, r)) as [[[[d1 f1] g1] v1] r1] eqn:E.
        destruct H0 as [? [? [? [? [? [? [? [?]]]]]]]].
        rewrite <- IHk by lia.
        apply divstep_full; try assumption; lia.
    Qed.
  End __.
End UnsaturatedSolinas.
