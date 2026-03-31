Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.WordByWordMontgomery.

Require Import Crypto.Arithmetic.BYInv.ArithmeticShiftr.
Require Import Crypto.Arithmetic.BYInv.TCAdd.
Require Import Crypto.Arithmetic.BYInv.EvalLemmas.
Require Import Crypto.Arithmetic.BYInv.Divstep.
Require Import Crypto.Arithmetic.BYInv.Ref.
Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.Ones.
Require Import Crypto.Arithmetic.BYInv.TCSignBit.
Require Import Crypto.Arithmetic.BYInv.TCSignExtend.
Require Import Crypto.Arithmetic.BYInv.TCMul.
Require Import Crypto.Arithmetic.BYInv.Firstn.
Require Import Crypto.Arithmetic.BYInv.Divstep.
Require Import Crypto.Arithmetic.BYInv.Zero.
Require Import Crypto.Arithmetic.BYInv.One.
Require Import Crypto.Arithmetic.BYInv.Hints.
Require Import Crypto.Arithmetic.BYInv.WordByWordMontgomery.
Require Import Crypto.Arithmetic.BYInv.UnsaturatedSolinas.

Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Odd.
Require Import Crypto.Util.ZUtil.ArithmeticShiftr.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.SignBit.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementNeg.
Require Import Crypto.Util.ZUtil.TwosComplementPos.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.
Require Import Crypto.Util.ZUtil.ModExp.
Require Import Crypto.Arithmetic.ModOps.

Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Module WordByWordMontgomery.

  Section __.

    Import WordByWordMontgomery.WordByWordMontgomery.
    Import Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
    Import Divstep.WordByWordMontgomery.
    Import Definitions.WordByWordMontgomery.

    Context
      (machine_wordsize : Z)
      (tc_limbs : nat)
      (mont_limbs : nat)
      (word_tc_mul_limbs : nat)
      (m : Z)
      (m_bounds : 2 ^ machine_wordsize < m < (2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs))
      (r' : Z)
      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m' : Z)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (mw2 : 2 < machine_wordsize)
      (tc_limbs0 : (0 < tc_limbs)%nat)
      (mont_limbs1 : (1 < mont_limbs)%nat)
      (word_tc_mul_limbs_eq : (word_tc_mul_limbs = 1 + tc_limbs)%nat).

    Notation jump_divstep := (jump_divstep machine_wordsize mont_limbs tc_limbs word_tc_mul_limbs m m').
    Notation eval := (@WordByWordMontgomery.eval machine_wordsize mont_limbs).
    Notation tc_eval := (tc_eval machine_wordsize tc_limbs).
    Notation tc := (Z.twos_complement machine_wordsize).
    Notation divstep_aux := (divstep_aux machine_wordsize tc_limbs mont_limbs m).
    Notation divstep := (divstep machine_wordsize tc_limbs mont_limbs m).
    Notation jump_divstep_aux := (jump_divstep_aux machine_wordsize mont_limbs tc_limbs word_tc_mul_limbs m m').
    Notation valid := (WordByWordMontgomery.valid machine_wordsize mont_limbs m).
    Notation tc_wtmne := (twosc_word_mod_m machine_wordsize mont_limbs m).
    Notation mulmod := (mulmod machine_wordsize mont_limbs m m').
    Notation oppmod := (oppmod machine_wordsize mont_limbs m).
    Notation from_montgomerymod := (from_montgomerymod machine_wordsize mont_limbs m m').
    Notation in_bounded := (in_bounded machine_wordsize).
    Notation divstep_precompmod := (divstep_precompmod machine_wordsize mont_limbs m).
    Notation partition_divstep_precomp := (partition_divstep_precomp machine_wordsize mont_limbs m).
    Notation by_inv := (by_inv machine_wordsize mont_limbs tc_limbs m m').

    Lemma precomp_bound : 0 <= divstep_precompmod < m.
    Proof.
      unfold divstep_precompmod.
      rewrite Z.modexp_correct.
      apply Z.mod_pos_bound. lia.
    Qed.

    Lemma eval_precomp :
      eval partition_divstep_precomp = divstep_precompmod.
    Proof.
      unfold partition_divstep_precomp.
      replace eval with (Positional.eval (uweight machine_wordsize) mont_limbs) by reflexivity.
      rewrite eval_partition.
      rewrite Z.mod_small. reflexivity.
      rewrite uweight_eq_alt'.
      rewrite Z.pow_mul_r by lia.
      pose proof precomp_bound.
      lia. apply uwprops. lia.
    Qed.

    Lemma precomp_valid : valid partition_divstep_precomp.
    Proof.
      unfold partition_divstep_precomp.
      apply partition_valid. lia. lia.
      apply precomp_bound.
    Qed.

    Theorem by_inv_jump_spec g
            (g_length : length g = tc_limbs)
            (g_bounds : - 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2))
            (g_in_bounded : in_bounded g)
            (iterations_bounds : 0 <= 2 ^ (machine_wordsize - 1) - iterations (Z.log2 m + 1) - 3)
            (m_odd : Z.odd m = true)
            (m_bounds2 : m < 2 ^ (machine_wordsize * tc_limbs - 2)) :
      eval (by_inv g) mod m = by_inv_ref m (tc_eval g) * 2 ^ (2 * machine_wordsize * mont_limbs) mod m.
    Proof.
      assert (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) < 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1)).
      { apply Z.pow_lt_mono_r. lia. nia. lia. }

      set (msat := Partition.partition (uweight machine_wordsize) tc_limbs m).
      assert (eval_msat : tc_eval msat = m).
      { unfold msat. unfold tc_eval. rewrite eval_partition. 2: apply uwprops; lia.
        rewrite uweight_eq_alt', Z.twos_complement_mod, Z.twos_complement_small; nia. }
      pose proof Z.log2_pos m ltac:(lia).
      pose proof iterations_pos ((Z.log2 m) + 1) ltac:(lia).
      unshelve epose proof divstep_iter_correct machine_wordsize tc_limbs mont_limbs m _ r' _ m' _ _ _ _ 1 msat g (zero mont_limbs) (one mont_limbs) (Z.to_nat (iterations (Z.log2 m + 1))) _ _ _ _ _ _ _ _ _ _ _ _.
      all: try assumption; try lia.
      rewrite eval_msat. assumption.
      all: auto with len.
      unfold msat; auto with len.
      rewrite Z.twos_complement_one.
      rewrite !Z2Nat.id. lia. lia. lia.
      unfold msat; auto with in_bounded.


      unshelve epose proof divstep_iter_bounds machine_wordsize tc_limbs mont_limbs m _ r' _ m' _ _ _ _ 1 msat g (zero mont_limbs) (one mont_limbs) (Z.to_nat (iterations (Z.log2 m + 1))) _ _ _ _ _ _ _ _ _ _ _ _.
      all: try assumption; try lia.
      rewrite eval_msat. assumption.
      all: auto with len.
      unfold msat; auto with len.
      rewrite Z.twos_complement_one.
      rewrite !Z2Nat.id. lia. lia. lia.
      unfold msat; auto with in_bounded.

      unfold by_inv.
      unfold by_inv_ref.
      unfold by_inv_full.

      destruct fold_left as [[[[dn fn]gn]vn]rn].
      destruct H3 as [fn_length [gn_length [vn_length [rn_length [fn_odd [fn_bounds [gn_bounds [vn_valid [rn_valid [fn_in_bounded gn_in_bounded]]]]]]]]]].

      rewrite eval_msat in H2.
      rewrite Z.twos_complement_one in H2 by lia.
      replace (eval (zero mont_limbs)) with 0 in H2 by (symmetry; apply eval_zero).
      replace (eval (one mont_limbs)) with 1 in H2 by (symmetry; apply eval_one; lia).
      rewrite Z.mod_0_l, Z.mod_1_l in H2 by lia.
      destruct Nat.iter as [[[[dk fk]gk]vk]rk].
      inversion H2.
      rewrite tc_sign_bit_neg; try assumption; try lia.

      replace eval with (Positional.eval (uweight machine_wordsize) mont_limbs) by reflexivity.
      rewrite Positional.eval_select; auto with len.
      2: { unfold partition_divstep_precomp.
           apply length_mulmod with (r':=r').
           assumption.
           assumption. lia. lia. lia. lia.
           apply partition_valid. lia. lia.
           apply precomp_bound.
           assumption. }
      2: { apply length_oppmod. lia.
           apply length_mulmod with (r':=r').
           assumption.
           assumption. lia. lia. lia. lia.
           apply partition_valid. lia. lia.
           apply precomp_bound.
           assumption. }

      destruct (tc_eval fn <? 0).
      - cbn -[Z.mul Z.add mulmod oppmod].
        replace (Positional.eval (uweight machine_wordsize) mont_limbs) with eval by reflexivity.
        rewrite eval_oppmod'.
        pull_Zmod; push_Zmod.
        rewrite eval_mulmod' with (r':=r').
        rewrite eval_precomp.
        unfold divstep_precompmod.
        push_Zmod.
        rewrite !Z.modexp_correct.
        rewrite H7.
        pull_Zmod.

        set (bits := (Z.log2 m) + 1) in *.
        rewrite Zpower_nat_Z. rewrite !Z2Nat.id.
        set (pc := (((m + 1) / 2) ^ iterations bits)).

        replace (2 ^ (3 * machine_wordsize * Z.of_nat mont_limbs)) with
          (2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * 2 ^ (machine_wordsize * Z.of_nat mont_limbs)).
        replace (- (2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * 2 ^ (machine_wordsize * Z.of_nat mont_limbs) * pc * vk * r' ^ Z.of_nat mont_limbs) mod m) with
          ((- 2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * pc * vk * (((2 ^ machine_wordsize) * r' mod m) ^ Z.of_nat mont_limbs)) mod m).
        rewrite r'_correct.
        f_equal. rewrite Z.pow_1_l. lia. lia.
        push_Zmod; pull_Zmod.
        f_equal.
        rewrite Z.pow_mul_l.
        rewrite <- Z.pow_mul_r.  lia.
        lia. lia.
        rewrite <- Z.pow_add_r.
        f_equal. all: try lia.
        apply precomp_valid. assumption.
        apply mulmod_valid with (r':=r'). all: try lia.
        apply precomp_valid. assumption.
      - cbn -[Z.mul Z.add mulmod oppmod].
        replace (Positional.eval (uweight machine_wordsize) mont_limbs) with eval by reflexivity.
        pull_Zmod; push_Zmod.
        rewrite eval_mulmod' with (r':=r').
        rewrite eval_precomp.
        unfold divstep_precompmod.
        push_Zmod.
        rewrite !Z.modexp_correct.
        rewrite H7.
        pull_Zmod.

        set (bits := (Z.log2 m) + 1) in *.
        rewrite Zpower_nat_Z. rewrite !Z2Nat.id.
        set (pc := (((m + 1) / 2) ^ iterations bits)).

        replace (2 ^ (3 * machine_wordsize * Z.of_nat mont_limbs)) with
          (2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * 2 ^ (machine_wordsize * Z.of_nat mont_limbs)).
        replace ((2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * 2 ^ (machine_wordsize * Z.of_nat mont_limbs) * pc * vk * r' ^ Z.of_nat mont_limbs) mod m) with
          ((2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * pc * vk * (((2 ^ machine_wordsize) * r' mod m) ^ Z.of_nat mont_limbs)) mod m).
        rewrite r'_correct.
        f_equal. rewrite Z.pow_1_l. lia. lia.
        push_Zmod; pull_Zmod.
        f_equal.
        rewrite Z.pow_mul_l.
        rewrite <- Z.pow_mul_r.  lia.
        lia. lia.
        rewrite <- Z.pow_add_r.
        f_equal. all: try lia.
        apply precomp_valid. assumption.
    Qed.

  End __.

End WordByWordMontgomery.

Module UnsaturatedSolinas.

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

    Local Notation eval := (Positional.eval (weight limbwidth_num limbwidth_den) n).

    Context (balance : list Z)
            (length_balance : length balance = n)
            (eval_balance : eval balance mod (s - Associational.eval c) = 0).

    Local Notation divstep_aux := (divstep_aux limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs idxs balance).
    Local Notation divstep := (divstep limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs idxs balance).
    Local Notation tc_eval := (tc_eval machine_wordsize tc_limbs).
    Local Notation tc := (Z.twos_complement machine_wordsize).
    Local Notation in_bounded := (in_bounded machine_wordsize).
    Local Notation m := (s - Associational.eval c).

    Context (m_bounds : 1 < m).

    Local Notation addmod := (addmod limbwidth_num limbwidth_den n).
    Local Notation oppmod := (oppmod limbwidth_num limbwidth_den n balance).
    Local Notation carrymod := (carrymod limbwidth_num limbwidth_den s c n idxs).
    Local Notation carry_mulmod := (carry_mulmod limbwidth_num limbwidth_den s c n idxs).
    Local Notation encodemod := (encodemod limbwidth_num limbwidth_den s c n).


    Local Notation divstep_precompmod := (divstep_precompmod s c).
    Local Notation encodemod_divstep_precomp := (encodemod_divstep_precomp limbwidth_num limbwidth_den s c n).
    Local Notation partition_divstep_precomp := (partition_divstep_precomp machine_wordsize n m).
    Local Notation by_inv := (by_inv limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs idxs balance).

    Lemma precomp_bound : 0 <= divstep_precompmod < m.
    Proof.
      unfold divstep_precompmod.
      rewrite Z.modexp_correct.
      apply Z.mod_pos_bound. lia.
    Qed.

    Lemma eval_precomp :
      eval encodemod_divstep_precomp mod m = divstep_precompmod.
    Proof.
      unfold encodemod_divstep_precomp.
      rewrite eval_encodemod, Z.mod_small.
      all: auto.  apply precomp_bound.
    Qed.

    Lemma length_precomp :
      length encodemod_divstep_precomp = n.
    Proof. unfold encodemod_divstep_precomp. auto with len. Qed.

    #[local] Hint Resolve length_precomp : len.

    Theorem by_inv_jump_spec g
            (g_length : length g = tc_limbs)
            (g_bounds : - 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2))
            (g_in_bounded : in_bounded g)
            (iterations_bounds : 0 <= 2 ^ (machine_wordsize - 1) - iterations (Z.log2 m + 1) - 3)
            (m_odd : Z.odd m = true)
            (m_bounds2 : m < 2 ^ (machine_wordsize * tc_limbs - 2)) :
      eval (by_inv g) mod m = by_inv_ref m (tc_eval g).
    Proof.
      assert (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) < 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1)).
      { apply Z.pow_lt_mono_r. lia. nia. lia. }

      set (msat := Partition.partition (uweight machine_wordsize) tc_limbs m).
      assert (eval_msat : tc_eval msat = m).
      { unfold msat. unfold tc_eval. rewrite eval_partition. 2: apply uwprops; lia.
        rewrite uweight_eq_alt', Z.twos_complement_mod, Z.twos_complement_small; nia. }
      pose proof Z.log2_pos m ltac:(lia).
      pose proof iterations_pos ((Z.log2 m) + 1) ltac:(lia).
      unshelve epose proof divstep_iter_correct limbwidth_num limbwidth_den limbwidth_good machine_wordsize s c n tc_limbs len_c idxs len_idxs m_nz s_nz Hn_nz Hc Hidxs mw1 tc_limbs0 n0 balance length_balance eval_balance 1 msat g (zero n) (one n) (Z.to_nat (iterations (Z.log2 m + 1))) _ _ _ _ _ _ _ _ _ _.
      all: try assumption; try lia; auto with len.
      rewrite eval_msat. assumption.
      unfold msat. auto with len.
      rewrite Z.twos_complement_one.
      rewrite !Z2Nat.id. lia. lia. lia.
      unfold msat. auto with in_bounded.

      unshelve epose proof divstep_iter_bounds limbwidth_num limbwidth_den limbwidth_good machine_wordsize s c n tc_limbs len_c idxs len_idxs Hn_nz Hc Hidxs mw1 tc_limbs0 n0 balance length_balance 1 msat g (zero n) (one n) (Z.to_nat (iterations (Z.log2 m + 1))) _ _ _ _ _ _ _ _ _ _.
      all: try assumption; try lia; auto with len.
      rewrite eval_msat. assumption.
      unfold msat. auto with len.
      rewrite Z.twos_complement_one.
      rewrite !Z2Nat.id. lia. lia. lia.
      unfold msat. auto with in_bounded.

      unfold by_inv.
      unfold by_inv_ref.
      unfold by_inv_full.

      destruct fold_left as [[[[dn fn]gn]vn]rn].
      destruct H3 as [fn_length [gn_length [vn_length [rn_length [fn_odd [fn_bounds [gn_bounds [fn_in_bounded gn_in_bounded]]]]]]]].

      rewrite eval_msat in H2.
      rewrite Z.twos_complement_one in H2 by lia.
      replace (eval (zero n)) with 0 in H2 by (symmetry; apply eval_zero).
      replace (eval (one n)) with 1 in H2.
      2: { unfold one.
           destruct n. lia.
           rewrite Positional.eval_cons.
           rewrite weight_0.
           replace (S n1 - 1)%nat with n1 by lia.
           rewrite Positional.eval_zeros. lia.
           apply wprops. assumption. simpl.
           rewrite Nat.sub_0_r.
           auto with len. }

      rewrite Z.mod_0_l, Z.mod_1_l in H2 by lia.
      destruct Nat.iter as [[[[dk fk]gk]vk]rk].
      inversion H2.
      rewrite tc_sign_bit_neg; try assumption; try lia.

      rewrite eval_carrymod.
      rewrite Positional.eval_select.
      all: auto with len.
      destruct (tc_eval fn <? 0).
      - cbn -[Z.mul Z.add oppmod].
        rewrite eval_oppmod.
        push_Zmod.
        rewrite eval_carry_mulmod.
        push_Zmod.
        rewrite eval_precomp.
        unfold divstep_precompmod.
        push_Zmod.
        rewrite !Z.modexp_correct.
        rewrite H7.
        pull_Zmod.

        set (bits := (Z.log2 m) + 1) in *.
        rewrite Zpower_nat_Z. rewrite !Z2Nat.id.
        set (pc := (((m + 1) / 2) ^ iterations bits)).
        f_equal. lia.
        all: auto with len.
      - cbn -[Z.mul Z.add oppmod].
        rewrite eval_carry_mulmod.
        push_Zmod.
        rewrite eval_precomp.
        unfold divstep_precompmod.
        push_Zmod.
        rewrite !Z.modexp_correct.
        rewrite H7.
        pull_Zmod.

        set (bits := (Z.log2 m) + 1) in *.
        rewrite Zpower_nat_Z. rewrite !Z2Nat.id.
        set (pc := (((m + 1) / 2) ^ iterations bits)).
        f_equal. lia.
        all: auto with len.
    Qed.

  End __.

End UnsaturatedSolinas.
