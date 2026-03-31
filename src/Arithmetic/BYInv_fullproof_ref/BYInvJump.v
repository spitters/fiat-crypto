Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.ModOps.

Require Import Crypto.Arithmetic.BYInv.UnsaturatedSolinas.
Require Import Crypto.Arithmetic.BYInv.Ref.
Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.TCSignBit.
Require Import Crypto.Arithmetic.BYInv.JumpDivstep.
Require Import Crypto.Arithmetic.BYInv.Zero.
Require Import Crypto.Arithmetic.BYInv.One.
Require Import Crypto.Arithmetic.BYInv.Hints.

Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.ModExp.

Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Import ListNotations.

Local Open Scope Z.
Local Coercion Z.of_nat : nat >-> Z.

Module WordByWordMontgomery.

  Import WordByWordMontgomery.WordByWordMontgomery.
  Import Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
  Import BYInv.WordByWordMontgomery.
  Import JumpDivstep.WordByWordMontgomery.

  Section __.

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
    Notation jump_divstep_aux := (jump_divstep_aux machine_wordsize mont_limbs tc_limbs word_tc_mul_limbs m m').
    Notation valid := (WordByWordMontgomery.valid machine_wordsize mont_limbs m).
    Notation tc_wtmne := (twosc_word_mod_m machine_wordsize mont_limbs m).
    Notation mulmod := (mulmod machine_wordsize mont_limbs m m').
    Notation oppmod := (oppmod machine_wordsize mont_limbs m).
    Notation from_montgomerymod := (from_montgomerymod machine_wordsize mont_limbs m m').
    Notation in_bounded := (in_bounded machine_wordsize).
    Notation jumpdivstep_precompmod := (jumpdivstep_precompmod machine_wordsize mont_limbs m).
    Notation partition_jumpdivstep_precomp := (partition_jumpdivstep_precomp machine_wordsize mont_limbs m).
    Notation by_inv_jump := (by_inv_jump machine_wordsize mont_limbs tc_limbs word_tc_mul_limbs m m').

    #[local] Hint Resolve
         (length_addmod machine_wordsize mont_limbs m ltac:(lia))
         (length_oppmod machine_wordsize mont_limbs m ltac:(lia))
         (length_mulmod machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (length_twosc_word_mod_m machine_wordsize mont_limbs m ltac:(lia))
      : len.

    #[local] Hint Resolve
         (zero_valid machine_wordsize mont_limbs m ltac:(lia))
         (addmod_valid machine_wordsize mont_limbs m r' m' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (oppmod_valid machine_wordsize mont_limbs m r' m' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (mulmod_valid machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
         (twosc_word_mod_m_valid machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia))
      : valid.

    Ltac t := repeat match goal with
                     | |- valid _ => auto with valid
                     | |- length _ = _ => auto with len
                     | |- in_bounded _ => auto with in_bounded
                     | |- _ => assumption
                     | |- _ => lia
                     end.

    Lemma precomp_bound : 0 <= jumpdivstep_precompmod < m.
    Proof.
      unfold jumpdivstep_precompmod.
      apply Z.mod_pos_bound. lia.
    Qed.

    Lemma eval_precomp :
      eval partition_jumpdivstep_precomp = jumpdivstep_precompmod.
    Proof.
      unfold partition_jumpdivstep_precomp.
      replace eval with (Positional.eval (uweight machine_wordsize) mont_limbs) by reflexivity.
      rewrite eval_partition.
      rewrite Z.mod_small. reflexivity.
      rewrite uweight_eq_alt'.
      rewrite Z.pow_mul_r by lia.
      pose proof precomp_bound.
      lia. apply uwprops. lia.
    Qed.

    Lemma precomp_valid : valid partition_jumpdivstep_precomp.
    Proof.
      unfold partition_jumpdivstep_precomp.
      apply partition_valid. lia. lia.
      apply precomp_bound.
    Qed.

    Lemma length_precomp : length partition_jumpdivstep_precomp = mont_limbs.
    Proof. unfold partition_jumpdivstep_precomp. auto with len. Qed.

    #[local] Hint Resolve length_precomp : len.
    #[local] Hint Resolve precomp_valid : valid.

    Theorem by_inv_jump_spec g
            (g_length : length g = tc_limbs)
            (g_bounds : - 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2))
            (g_in_bounded : in_bounded g)
            (iterations_bouns : 0 <=
  2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2) - (jump_iterations (Z.log2 m + 1) machine_wordsize + 1) * (machine_wordsize - 2) - 3)
            (m_odd : Z.odd m = true)
            (m_bounds2 : m < 2 ^ (machine_wordsize * tc_limbs - 2)) :
      eval (by_inv_jump g) mod m =
        by_inv_jump_ref m (tc_eval g) machine_wordsize * 2 ^ (2 * machine_wordsize * mont_limbs) mod m.
    Proof.
      assert (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) < 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1)).
      { apply Z.pow_lt_mono_r. lia. nia. lia. }
      unfold by_inv_jump.
      unfold by_inv_jump_ref.
      unfold by_inv_jump_full.
      unfold jumpdivstep_precompmod.
      set (msat := Partition.partition (uweight machine_wordsize) tc_limbs m).
      assert (eval_msat : tc_eval msat = m).
      { unfold msat. unfold tc_eval. rewrite eval_partition. 2: apply uwprops; lia.
        rewrite uweight_eq_alt'.
        rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_small. reflexivity. nia.
        lia. nia. }
      pose proof Z.log2_pos m ltac:(lia).
      pose proof iterations_pos ((Z.log2 m) + 1) ltac:(lia).
      pose proof jump_iterations_pos (Z.log2 m + 1) machine_wordsize ltac:(lia) ltac:(lia).

      unshelve epose proof jump_divstep_iter_correct machine_wordsize tc_limbs mont_limbs word_tc_mul_limbs m _ r' _ m' _ _ _ _ _ 1 msat g (zero mont_limbs) (one mont_limbs) (Z.to_nat (jump_iterations (Z.log2 m + 1) machine_wordsize)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _.
      all: auto with len.
      rewrite eval_msat. assumption.
      unfold msat; auto with len.
      rewrite Z.twos_complement_one. lia. lia.
      unfold msat.
      auto with in_bounded.

      unshelve epose proof jump_divstep_iter_invariants machine_wordsize tc_limbs mont_limbs word_tc_mul_limbs m _ r' _ m' _ _ _ _ _ 1 msat g (zero mont_limbs) (one mont_limbs) (Z.to_nat (jump_iterations (Z.log2 m + 1) machine_wordsize)) 2 _ _ _ _ _ _ _ _ _ _ _ _ _.
      all: auto with len.
      unfold msat; auto with len.
      rewrite eval_msat. assumption.
      rewrite Z.twos_complement_one. lia. lia.
      unfold msat.
      auto with in_bounded.

      destruct fold_left as [[[[dn fn]gn]vn]rn].
      destruct H4 as [fn_length [gn_length [vn_length [rn_length [fn_odd [dn_bounds [fn_bounds [fn_in_bounds [gn_bounds [gn_in_bounds [vn_valid rn_valid]]]]]]]]]]].

      rewrite nat_iter_jump_divstep_vr_mul in H3.
      rewrite eval_msat in H3.
      rewrite Z.twos_complement_one in H3 by lia.
      replace (eval (zero mont_limbs)) with 0 in H3 by (symmetry; apply eval_zero).
      replace (eval (one mont_limbs)) with 1 in H3 by (symmetry; apply eval_one; lia).
      rewrite Z.mod_0_l, Z.mod_1_l in H3 by lia.
      destruct Nat.iter as [[[[dk fk]gk]vk]rk].
      inversion H3.
      rewrite tc_sign_bit_neg; try assumption; try lia.

      replace eval with (Positional.eval (uweight machine_wordsize) mont_limbs) by reflexivity.
      rewrite Positional.eval_select; auto with len.
      destruct (tc_eval fn <? 0).
      - cbn -[Z.mul Z.add mulmod oppmod].
        change (Positional.eval (uweight machine_wordsize) mont_limbs ) with eval.
        push_Zmod.
        rewrite eval_oppmod' by t.
        pull_Zmod; push_Zmod.
        rewrite eval_mulmod' with (r':=r'), eval_precomp by t.
        unfold jumpdivstep_precompmod.
        push_Zmod.
        rewrite !Z.modexp_correct.
        rewrite H8.
        pull_Zmod.

        set (bits := (Z.log2 m) + 1) in *.
        set (jump_iterations := jump_iterations bits machine_wordsize).
        set (total_iterations := jump_iterations * (machine_wordsize - 2)) in *.
        rewrite Zpower_nat_Z. rewrite !Z2Nat.id.
        set (pc := (((m + 1) / 2) ^ total_iterations)).

        rewrite !Z.mul_assoc.
        rewrite <- Z.pow_mul_r.
        rewrite <- (Z.mul_assoc _ (r' ^ _)).
        rewrite <- Z.pow_add_r.
        replace (Z.of_nat mont_limbs) with ((Z.of_nat mont_limbs) * 1) at 3 by lia.
        rewrite <- Z.mul_add_distr_l.

        replace (2 ^ (machine_wordsize * Z.of_nat mont_limbs * (jump_iterations + 3))) with
          (2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * (2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs * (jump_iterations + 1))).
        replace
          ((-
  (2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * (2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs * (jump_iterations + 1)) * pc * vk *
                              r' ^ (Z.of_nat mont_limbs * (jump_iterations + 1)))) mod m) with
          ((- 2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * pc * vk * (((2 ^ machine_wordsize) * r' mod m) ^ (Z.of_nat mont_limbs * (jump_iterations + 1)))) mod m).
        rewrite r'_correct.
        rewrite Z.pow_1_l.
        f_equal. lia. clear -H2 mont_limbs1. lia.
        rewrite <- Zmult_mod_idemp_r.
        rewrite <- PullPush.Z.mod_pow_full.
        rewrite Zmult_mod_idemp_r.
        rewrite Z.pow_mul_l.
        f_equal. lia.
        rewrite <- !Z.pow_mul_r.
        rewrite <- Z.pow_add_r.
        f_equal. lia. clear -mw2.
        lia. clear -H2 mont_limbs1 mw2. nia.
        clear -H2 mont_limbs1 mw2. lia.
        clear -H2. lia. clear -H2. lia. lia. lia. assumption. unfold total_iterations.
        clear -H2 mw2. nia. assumption.
      - cbn -[Z.mul Z.add mulmod oppmod].
        replace (Positional.eval (uweight machine_wordsize) mont_limbs ) with eval by reflexivity.
        rewrite eval_mulmod' with (r':=r'), eval_precomp by t.
        unfold jumpdivstep_precompmod.

        push_Zmod.
        rewrite !Z.modexp_correct.
        rewrite H8.
        pull_Zmod.

        set (bits := (Z.log2 m) + 1) in *.
        set (jump_iterations := jump_iterations bits machine_wordsize) in *.
        set (total_iterations := jump_iterations * (machine_wordsize - 2)) in *.
        rewrite Zpower_nat_Z. rewrite !Z2Nat.id.
        set (pc := (((m + 1) / 2) ^ total_iterations)).

        rewrite !Z.mul_assoc.
        rewrite <- Z.pow_mul_r.
        rewrite <- (Z.mul_assoc _ (r' ^ _)).
        rewrite <- Z.pow_add_r.
        replace (Z.of_nat mont_limbs) with ((Z.of_nat mont_limbs) * 1) at 3 by lia.
        rewrite <- Z.mul_add_distr_l.
        replace (2 ^ (machine_wordsize * Z.of_nat mont_limbs * (jump_iterations + 3))) with
          (2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * (2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs * (jump_iterations + 1))).
        replace (((2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * (2 ^ machine_wordsize) ^ (Z.of_nat mont_limbs * (jump_iterations + 1)) * pc * vk *
                              r' ^ (Z.of_nat mont_limbs * (jump_iterations + 1)))) mod m) with
          ((2 ^ (2 * machine_wordsize * Z.of_nat mont_limbs) * pc * vk * (((2 ^ machine_wordsize) * r' mod m) ^ (Z.of_nat mont_limbs * (jump_iterations + 1)))) mod m).
        rewrite r'_correct.
        rewrite Z.pow_1_l.
        f_equal. lia. clear -H2 mont_limbs1. lia.
        push_Zmod. pull_Zmod.
        rewrite Z.pow_mul_l.
        f_equal. lia.
        rewrite <- !Z.pow_mul_r.
        rewrite <- Z.pow_add_r.
        f_equal. lia.
        all: try (clear -H2 mont_limbs1 mw2; nia).
    Qed.
  End __.
End WordByWordMontgomery.

Module UnsaturatedSolinas.

  Import Definitions.UnsaturatedSolinas.
  Import JumpDivstep.UnsaturatedSolinas.

  Section __.

    Context (limbwidth_num limbwidth_den : Z)
            (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
            (machine_wordsize : Z)
            (s : Z)
            (c : list (Z*Z))
            (n : nat)
            (tc_limbs : nat)
            (word_tc_mul_limbs : nat)
            (idxs : list nat)
            (m_big : 2 ^ machine_wordsize < s - Associational.eval c)
            (len_c : nat)
            (len_idxs : nat)
            (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
            (Hc : length c = len_c)
            (Hidxs : length idxs = len_idxs)
            (n1 : (1 < n)%nat)
            (mw2 : 2 < machine_wordsize)
            (tc_limbs0 : (0 < tc_limbs)%nat)
            (word_tc_mul_limbs_eq : (word_tc_mul_limbs = 1 + tc_limbs)%nat)
    .

    #[local] Notation eval := (Positional.eval (weight (limbwidth_num) (limbwidth_den)) n).

    Context (balance : list Z)
            (length_balance : length balance = n)
            (eval_balance : eval balance mod (s - Associational.eval c) = 0).

    #[local] Notation word_to_solina := (word_to_solina limbwidth_num limbwidth_den machine_wordsize s c n idxs balance).
    #[local] Notation by_inv_jump := (by_inv_jump limbwidth_num limbwidth_den machine_wordsize s c n tc_limbs word_tc_mul_limbs idxs balance).
    #[local] Notation tc_eval := (tc_eval machine_wordsize tc_limbs).
    #[local] Notation tc := (Z.twos_complement machine_wordsize).
    #[local] Notation m := (s - Associational.eval c).
    #[local] Notation in_bounded := (in_bounded machine_wordsize).
    #[local] Notation jumpdivstep_precompmod := (jumpdivstep_precompmod machine_wordsize s c).
    #[local] Notation encodemod_jumpdivstep_precomp := (encodemod_jumpdivstep_precomp limbwidth_num limbwidth_den machine_wordsize s c n).

    #[local] Notation addmod := (addmod limbwidth_num limbwidth_den n).
    #[local] Notation oppmod := (oppmod limbwidth_num limbwidth_den n balance).
    #[local] Notation carrymod := (carrymod limbwidth_num limbwidth_den s c n idxs).

    Ltac t := repeat match goal with
                     | |- length _ = _ => auto with len
                     | |- in_bounded _ => auto with in_bounded
                     | |- _ => assumption
                     | |- _ => lia
                     | |- context[tc] => autorewrite with Ztc
                     | |- context[tc_eval] => autorewrite with tc
                     end.

    Lemma precomp_bound : 0 <= jumpdivstep_precompmod < m.
    Proof.
      unfold jumpdivstep_precompmod.
      apply Z.mod_pos_bound. lia.
    Qed.

    Lemma eval_precomp :
      eval encodemod_jumpdivstep_precomp mod m = jumpdivstep_precompmod.
    Proof.
      unfold encodemod_jumpdivstep_precomp.
      rewrite eval_encodemod.
      rewrite Z.mod_small. reflexivity.
      apply precomp_bound.
      all: t.
    Qed.

    Lemma length_precomp : length encodemod_jumpdivstep_precomp = n.
    Proof. unfold encodemod_jumpdivstep_precomp. auto with len. Qed.

    #[local] Hint Resolve length_precomp : len.

    Theorem by_inv_jump_spec g
            (g_length : length g = tc_limbs)
            (g_bounds : - 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) < tc_eval g < 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2))
            (g_in_bounded : in_bounded g)
            (iterations_bouns : 0 <= 2 ^ (machine_wordsize - 1) - 1 - (machine_wordsize - 2) - (jump_iterations (Z.log2 m + 1) machine_wordsize + 1) * (machine_wordsize - 2) - 3)
            (m_odd : Z.odd m = true)
            (m_bounds2 : m < 2 ^ (machine_wordsize * tc_limbs - 2)) :
      eval (by_inv_jump g) mod m = by_inv_jump_ref m (tc_eval g) machine_wordsize.
    Proof.
      assert (2 ^ (machine_wordsize * Z.of_nat tc_limbs - 2) < 2 ^ (machine_wordsize * Z.of_nat tc_limbs - 1)).
      { apply Z.pow_lt_mono_r. lia. nia. lia. }
      unfold by_inv_jump.
      unfold by_inv_jump_ref.
      unfold by_inv_jump_full.
      set (msat := Partition.partition (uweight machine_wordsize) tc_limbs m).
      assert (eval_msat : tc_eval msat = m).
      { unfold msat. unfold tc_eval. rewrite eval_partition. 2: apply uwprops; lia.
        rewrite uweight_eq_alt'.
        rewrite Z.twos_complement_mod.
        rewrite Z.twos_complement_small. reflexivity. nia.
        lia. nia. }
      pose proof Z.log2_pos m ltac:(lia).
      pose proof iterations_pos ((Z.log2 m) + 1) ltac:(lia).
      pose proof jump_iterations_pos (Z.log2 m + 1) machine_wordsize ltac:(lia) ltac:(lia).

      unshelve epose proof jump_divstep_iter_correct limbwidth_num limbwidth_den _ machine_wordsize s c n tc_limbs word_tc_mul_limbs idxs _ len_c len_idxs _ _ _ _ _ _ _ _ balance _ _ 1 msat g (zero n) (one n) (Z.to_nat (jump_iterations (Z.log2 m + 1) machine_wordsize)) 2 _ _ _ _ _ _ _ _ _ _ _.
      all: rewrite ?eval_msat; unfold msat; t.

      unshelve epose proof jump_divstep_iter_invariants limbwidth_num limbwidth_den _ machine_wordsize s c n tc_limbs word_tc_mul_limbs idxs _ len_c len_idxs _ _ _ _ _ _ _ _ balance _ _ 1 msat g (zero n) (one n) (Z.to_nat (jump_iterations (Z.log2 m + 1) machine_wordsize)) 2 _ _ _ _ _ _ _ _ _ _ _.
      all: rewrite ?eval_msat; unfold msat; t.

      destruct fold_left as [[[[dn fn]gn]vn]rn].
      destruct H4 as [fn_length [gn_length [vn_length [rn_length [fn_odd [dn_bounds [fn_bounds [fn_in_bounds [gn_bounds gn_in_bounds]]]]]]]]].

      rewrite eval_msat in H3.
      rewrite Z.twos_complement_one in H3 by lia.
      replace (eval (zero n)) with 0 in H3 by (symmetry; apply eval_zero).
      replace (eval (one n)) with 1 in H3 by (symmetry; apply UnsaturatedSolinas.eval_one; t).
      rewrite Z.mod_0_l, Z.mod_1_l in H3 by lia.
      destruct Nat.iter as [[[[dk fk]gk]vk]rk].
      inversion H3.
      rewrite tc_sign_bit_neg; try assumption; try lia.
      rewrite eval_carrymod, Positional.eval_select; t.
      destruct (tc_eval fn <? 0).
      - cbn -[Z.mul Z.add].
        rewrite eval_oppmod by t.
        push_Zmod.
        rewrite eval_carry_mulmod by t.
        push_Zmod.
        rewrite eval_precomp.
        unfold jumpdivstep_precompmod.
        rewrite !Z.modexp_correct.
        rewrite H8.
        pull_Zmod.

        set (bits := (Z.log2 m) + 1) in *.
        set (jump_iterations := jump_iterations bits machine_wordsize).
        set (total_iterations := jump_iterations * (machine_wordsize - 2)) in *.
        rewrite Zpower_nat_Z. rewrite !Z2Nat.id.
        set (pc := (((m + 1) / 2) ^ total_iterations)).
        f_equal. lia.
        unfold total_iterations. clear -H2 mw2. nia.
      - cbn -[Z.mul Z.add].
        rewrite eval_carry_mulmod by t.
        push_Zmod.
        rewrite eval_precomp.
        unfold jumpdivstep_precompmod.
        rewrite !Z.modexp_correct.
        rewrite H8.
        pull_Zmod.

        set (bits := (Z.log2 m) + 1) in *.
        set (jump_iterations := jump_iterations bits machine_wordsize).
        set (total_iterations := jump_iterations * (machine_wordsize - 2)) in *.
        rewrite Zpower_nat_Z. rewrite !Z2Nat.id.
        set (pc := (((m + 1) / 2) ^ total_iterations)).
        f_equal. lia.
        unfold total_iterations. clear -H2 mw2. nia.
    Qed.
  End __.
End UnsaturatedSolinas.
