Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Core.

Require Import Crypto.Arithmetic.BYInv.Definitions.
Require Import Crypto.Arithmetic.BYInv.Zero.
Require Import Crypto.Arithmetic.BYInv.One.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.
Require Import Crypto.Util.ZUtil.TwosComplementNeg.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.LetIn.

Import ListNotations.

Local Open Scope Z_scope.

Module WordByWordMontgomery.
  Import Arithmetic.WordByWordMontgomery.WordByWordMontgomery.

  Lemma length_addmod machine_wordsize mont_limbs m :
    0 < machine_wordsize ->
    forall f, length f = mont_limbs -> forall g, length g = mont_limbs -> length (addmod machine_wordsize mont_limbs m f g) = mont_limbs.
  Proof.
    intros.
    unfold addmod, add, Rows.conditional_sub.
    rewrite Positional.length_drop_high_to_length.
    rewrite (surjective_pairing (Rows.sub (uweight machine_wordsize) (S mont_limbs) (let '(v, c) := Rows.add (uweight machine_wordsize) mont_limbs f g in v ++ [c])
                                          (Positional.extend_to_length mont_limbs (S mont_limbs) (Partition.partition (uweight machine_wordsize) mont_limbs m)))).
    rewrite Positional.length_select with (n:=S mont_limbs). lia.
    unfold Rows.sub.
    apply Rows.length_flatten; [apply uwprops; assumption|].
    intros.
    inversion H2. subst.
    simpl.
    rewrite app_length, Rows.length_sum_rows with (n:=length f); auto.
    simpl; lia.
    apply uwprops; assumption.
    inversion H3. subst.
    rewrite map_length, Positional.length_extend_to_length; auto.
    apply length_partition. inversion H4.
    simpl.
    rewrite app_length, Rows.length_sum_rows with (n:=mont_limbs); try assumption.
    simpl; lia.
    apply uwprops; assumption.
  Qed.

  Lemma length_oppmod machine_wordsize mont_limbs m :
    0 < machine_wordsize ->
    forall f, length f = mont_limbs -> length (oppmod machine_wordsize mont_limbs m f) = mont_limbs.
  Proof.
    intros. unfold oppmod, opp, sub. simpl.
    rewrite Rows.length_sum_rows with (n:=mont_limbs). reflexivity. apply uwprops. lia.
    rewrite Rows.length_sum_rows with (n:=mont_limbs). reflexivity. apply uwprops. lia.
    apply Positional.length_zeros. rewrite map_length. assumption.
    rewrite Positional.length_zselect. apply length_partition.
  Qed.

  Lemma partition_valid machine_wordsize mont_limbs m a
    (m_bounds : 0 < m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
    (mw0 : 0 < machine_wordsize)
    (a_bounds : 0 <= a < m) :
    valid machine_wordsize mont_limbs m (Partition.partition (uweight machine_wordsize) mont_limbs a).
  Proof.
    unfold valid; split.
    - unfold small.
      replace (eval machine_wordsize) with (Positional.eval (uweight machine_wordsize) mont_limbs) by reflexivity.
      rewrite eval_partition by (apply uwprops; lia).
      rewrite uweight_eq_alt' by assumption.
      rewrite Z.mod_small.
      reflexivity. rewrite Z.pow_mul_r; lia.
    - replace (eval machine_wordsize) with (Positional.eval (uweight machine_wordsize) mont_limbs) by reflexivity.
      rewrite eval_partition by (apply uwprops; lia).
      rewrite Z.mod_small. lia.
      rewrite uweight_eq_alt'.
      rewrite Z.pow_mul_r; lia.
  Qed.

  Lemma addmod_valid machine_wordsize mont_limbs m (r' m' : Z) :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    1 < m ->
    mont_limbs <> 0%nat ->
    m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    forall f, valid machine_wordsize mont_limbs m f -> forall g, valid machine_wordsize mont_limbs m g -> valid machine_wordsize mont_limbs m (addmod machine_wordsize mont_limbs m f g).
  Proof.
    intros.
    epose proof (addmod_correct machine_wordsize mont_limbs m r' m' _ _ _ _ _ _) as [_ h]. apply h; assumption.
    Unshelve. all: try assumption; lia.
  Qed.

  Lemma oppmod_valid machine_wordsize mont_limbs m (r' m' : Z) :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    1 < m ->
    mont_limbs <> 0%nat ->
    m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    forall f, valid machine_wordsize mont_limbs m f -> valid machine_wordsize mont_limbs m (oppmod machine_wordsize mont_limbs m f).
  Proof.
    intros.
    epose proof (oppmod_correct machine_wordsize mont_limbs m r' m' _ _ _ _ _ _) as [_ h]. apply h; assumption.
    Unshelve. all: try assumption; lia.
  Qed.

  Lemma select_valid machine_wordsize mont_limbs m cond f g
        (f_length : length f = mont_limbs)
        (g_length : length g = mont_limbs) :
    valid machine_wordsize mont_limbs m f -> valid machine_wordsize mont_limbs m g -> valid machine_wordsize mont_limbs m (Positional.select cond f g).
  Proof.
    intros. rewrite Positional.select_eq with (n:=mont_limbs) by auto.
    destruct (Decidable.dec _); auto.
  Qed.

  Lemma zero_valid machine_wordsize mont_limbs m :
    0 < m ->
    valid machine_wordsize mont_limbs m (zero mont_limbs).
  Proof.
    unfold valid, small, WordByWordMontgomery.eval.
    rewrite eval_zero, partition_0; try split; auto; lia.
  Qed.

  Lemma nonzero_zero n :
    nonzeromod (zero n) = 0.
  Proof. unfold nonzero, zero; induction n; auto. Qed.

  Lemma eval_oppmod' machine_wordsize mont_limbs m a
        (mw0 : 0 < machine_wordsize)
        (mont_limbs0 : (mont_limbs <> 0)%nat)
        (m_bounds : 0 < m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
        (Ha : valid machine_wordsize mont_limbs m a) :
    @eval machine_wordsize mont_limbs (oppmod machine_wordsize mont_limbs m a) mod m
    = (- @eval machine_wordsize mont_limbs a) mod m.
  Proof.
    unfold oppmod, valid, small in *.
    pose proof @eval_partition (uweight machine_wordsize) (uwprops machine_wordsize ltac:(lia)) mont_limbs m.
    rewrite uweight_eq_alt', Z.pow_mul_r, (Z.mod_small m) in H by lia.
    replace (Positional.eval (uweight machine_wordsize)) with (@eval machine_wordsize) in H by reflexivity.
    rewrite eval_opp; try lia; unfold small; rewrite ?H; try easy.
    destruct (eval machine_wordsize a =? 0).
    - rewrite Z.sub_0_l. reflexivity.
    - push_Zmod; pull_Zmod. f_equal.
  Qed.

  Lemma eval_mulmod' machine_wordsize mont_limbs m m' r' a b
        (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
        (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
        (mw0 : 0 < machine_wordsize)
        (mont_limbs0 : (mont_limbs <> 0)%nat)
        (m_bounds : 1 < m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
        (Ha : valid machine_wordsize mont_limbs m a)
        (Hb : valid machine_wordsize mont_limbs m b) :
    @eval machine_wordsize mont_limbs (mulmod machine_wordsize mont_limbs m m' a b) mod m
    = (@eval machine_wordsize mont_limbs a * @eval machine_wordsize mont_limbs b * r' ^ (Z.of_nat mont_limbs)) mod m.
  Proof.
    unfold mulmod, valid, small in *.
    pose proof @eval_partition (uweight machine_wordsize) (uwprops machine_wordsize ltac:(lia)) mont_limbs m.
    rewrite uweight_eq_alt', Z.pow_mul_r, (Z.mod_small m) in H by lia.
    replace (Positional.eval (uweight machine_wordsize)) with (@eval machine_wordsize) in H by reflexivity.
    rewrite <- H at 2.
    rewrite redc_mod_N with (ri:=r').
    all: unfold small; rewrite ?H; try lia; try easy.
    rewrite Z.mod_1_l by lia. assumption.
    rewrite Z.mul_comm. assumption.
  Qed.

  Lemma eval_addmod' machine_wordsize mont_limbs m a b
        (mw0 : 0 < machine_wordsize)
        (mont_limbs0 : (mont_limbs <> 0)%nat)
        (m_bounds : 0 < m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
        (Ha : valid machine_wordsize mont_limbs m a)
        (Hb : valid machine_wordsize mont_limbs m b) :
    @eval machine_wordsize mont_limbs (addmod machine_wordsize mont_limbs m a b) mod m
    = (@eval machine_wordsize mont_limbs a + @eval machine_wordsize mont_limbs b) mod m.
  Proof.
    unfold addmod, valid, small in *.
    pose proof @eval_partition (uweight machine_wordsize) (uwprops machine_wordsize ltac:(lia)) mont_limbs m.
    rewrite uweight_eq_alt', Z.pow_mul_r, (Z.mod_small m) in H by lia.
    replace (Positional.eval (uweight machine_wordsize)) with (@eval machine_wordsize) in H by reflexivity.
    rewrite eval_add with (B:=[]); try lia; unfold small; rewrite ?H; try easy.
    destruct (m <=? _).
    - push_Zmod; pull_Zmod. rewrite Z.add_0_r. reflexivity.
    - rewrite Z.add_0_r. f_equal.
    - unfold eval. rewrite Positional.eval_nil. lia.
  Qed.

  Lemma mulmod_valid machine_wordsize mont_limbs m r' m' :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    1 < m ->
    mont_limbs <> 0%nat ->
    m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    forall f, valid machine_wordsize mont_limbs m f -> forall g, valid machine_wordsize mont_limbs m g -> valid machine_wordsize mont_limbs m (mulmod machine_wordsize mont_limbs m m' f g).
  Proof.
    intros.
    epose proof (mulmod_correct machine_wordsize mont_limbs m r' m' _ _ _ _ _ _) as [_ h]. apply h; assumption.
    Unshelve. all: assumption.
  Qed.

  Lemma length_mulmod machine_wordsize mont_limbs m r' m' :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    1 < m ->
    mont_limbs <> 0%nat ->
    m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    forall f, valid machine_wordsize mont_limbs m f -> forall g, valid machine_wordsize mont_limbs m g -> length (mulmod machine_wordsize mont_limbs m m' f g) = mont_limbs.
  Proof.
    intros.
    unshelve epose proof mulmod_valid machine_wordsize mont_limbs m r' m' _ _ _ _ _ _ f _ g _; try assumption.
    eapply length_small.
    apply H7.
  Qed.

  Lemma twosc_word_mod_m_correct machine_wordsize mont_limbs m r' m' :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    2 ^ machine_wordsize < m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    (1 < mont_limbs)%nat ->
    forall a, 0 <= a < 2 ^ machine_wordsize ->
    @WordByWordMontgomery.eval machine_wordsize mont_limbs (twosc_word_mod_m machine_wordsize mont_limbs m a) mod m = Z.twos_complement machine_wordsize a mod m
    /\ valid machine_wordsize mont_limbs m (twosc_word_mod_m machine_wordsize mont_limbs m a).
  Proof.
    intros.
    (* assert (2 < 2 ^ machine_wordsize) by (eapply Z.pow_pos_lt; lia). *)
    assert (2 ^ (machine_wordsize) <= 2 ^ (machine_wordsize * Z.of_nat mont_limbs)) by
      (apply Z.pow_le_mono_r; nia).
    unfold twosc_word_mod_m.
    assert (valid machine_wordsize mont_limbs m (Partition.partition (uweight machine_wordsize) mont_limbs (Z.twos_complement_opp machine_wordsize a))).
    { unfold valid, small.
      pose proof Z.mod_pos_bound (-a) (2^machine_wordsize) ltac:(apply Z.pow_pos_nonneg; lia).
      split; unfold eval.
      rewrite eval_partition, uweight_eq_alt', Z.mod_small by
        (try rewrite Z.twos_complement_opp_correct; try apply uwprops; nia); reflexivity.
      rewrite eval_partition, uweight_eq_alt', Z.twos_complement_opp_correct, Z.mod_pow_same_base_larger;
        try apply uwprops; nia. }
    pose proof (Hvalid := oppmod_correct machine_wordsize mont_limbs m r' m' ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite Z.twos_complement_neg_spec, !unfold_Let_In, Positional.select_eq with (n:=mont_limbs); try (try rewrite length_partition; lia);
      try (apply length_small with (lgr:=machine_wordsize); apply Hvalid; assumption); try apply (uweight machine_wordsize).

    unfold Z.twos_complement.
    rewrite Z.twos_complement_cond_equiv by lia.

    destruct (Z.testbit a (machine_wordsize - 1)) eqn:E; cbn -[Partition.partition oppmod]; split.
    - replace (@WordByWordMontgomery.eval machine_wordsize mont_limbs (oppmod machine_wordsize mont_limbs m (Partition.partition (uweight machine_wordsize) mont_limbs (Z.twos_complement_opp machine_wordsize a)))) with
        (@WordByWordMontgomery.eval machine_wordsize mont_limbs (oppmod machine_wordsize mont_limbs m (Partition.partition (uweight machine_wordsize) mont_limbs (Z.twos_complement_opp machine_wordsize a))) * (1 ^ Z.of_nat mont_limbs)) by (rewrite Z.pow_1_l; lia).

      rewrite <- H. push_Zmod; pull_Zmod.
      rewrite Z.pow_mul_l, Z.mul_comm, <- Z.mul_assoc, Z.mul_comm, (Z.mul_comm (r' ^ _)),  <- Zmult_mod_idemp_l,  <- eval_from_montgomerymod with (m':=m'), eval_oppmod with (r':=r'); try lia; try (try apply Hvalid; assumption).
      push_Zmod. rewrite eval_from_montgomerymod with (r':=r'); try lia; try (try apply Hvalid; assumption).
      push_Zmod. unfold eval; rewrite eval_partition by (apply uwprops; lia).
      rewrite Z.twos_complement_opp_correct. pull_Zmod.
      rewrite uweight_eq_alt', Z.mod_pow_same_base_larger, Z.mul_opp_l, <- Z.mul_assoc, <- Z.pow_mul_l, (Z.mul_comm r'), PullPush.Z.opp_mod_mod, <- Zmult_mod_idemp_r, PullPush.Z.mod_pow_full, H, Z.pow_1_l by nia. pull_Zmod. rewrite Z.mul_1_r.
      destruct (Decidable.dec (a = 0)).
      + subst. rewrite Z.bits_0 in *. inversion E.
      + rewrite (Z.mod_opp_small a) by nia; apply f_equal2; [|reflexivity]; rewrite Z.mod_small; lia.
    - apply Hvalid. assumption.
    - unfold eval. rewrite eval_partition, uweight_eq_alt, (Z.mod_small a), (Z.mod_small a (2 ^ _)); try apply uwprops; lia.
    - unfold valid; split.
      + unfold small.
        unfold eval. rewrite eval_partition, uweight_eq_alt', Z.mod_small; try (apply uwprops; lia); try nia; reflexivity.
      + unfold eval. rewrite eval_partition, uweight_eq_alt', Z.mod_small; try (apply uwprops; lia); try nia; reflexivity.
  Qed.

  Lemma eval_twosc_word_mod_m machine_wordsize mont_limbs m r' m' :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    2 ^ machine_wordsize < m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    (1 < mont_limbs)%nat ->
    forall a, 0 <= a < 2 ^ machine_wordsize ->
    @eval machine_wordsize mont_limbs (twosc_word_mod_m machine_wordsize mont_limbs m a) mod m = Z.twos_complement machine_wordsize a mod m.
  Proof. apply twosc_word_mod_m_correct; assumption. Qed.

  Lemma twosc_word_mod_m_valid machine_wordsize mont_limbs m r' m' :
    (2 ^ machine_wordsize * r') mod m = 1 ->
    (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize ->
    0 < machine_wordsize ->
    2 ^ machine_wordsize < m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs ->
    (1 < mont_limbs)%nat ->
    forall a, 0 <= a < 2 ^ machine_wordsize ->
    valid machine_wordsize mont_limbs m (twosc_word_mod_m machine_wordsize mont_limbs m a).
  Proof. apply twosc_word_mod_m_correct; assumption. Qed.

  Lemma length_twosc_word_mod_m machine_wordsize mont_limbs m :
    0 < machine_wordsize ->
    forall a, length (twosc_word_mod_m machine_wordsize mont_limbs m a) = mont_limbs.
  Proof.
    intros. unfold twosc_word_mod_m. rewrite !unfold_Let_In.
    apply Positional.length_select. apply length_partition. apply length_oppmod. assumption. apply length_partition.
  Qed.

  Lemma one_valid machine_wordsize mont_limbs m :
    0 < machine_wordsize ->
    (0 < mont_limbs)%nat ->
    1 < m ->
    valid machine_wordsize mont_limbs m (one mont_limbs).
  Proof.
    intros. unfold valid, small, eval.
    rewrite eval_one, partition_1; try split; auto; lia.
  Qed.

End WordByWordMontgomery.
