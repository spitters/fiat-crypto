(** * Generic FElem split/join for quadratic and cubic extensions.

    Provides parameterized split/join lemmas and Ltac tactics for any
    GenericQuadraticSpecs or GenericCubicSpecs instantiation.

    These replace the per-layer Fp2_raw_FElem_split/join,
    Fp6_raw_FElem_split/join, Fp12_raw_FElem_split/join with
    reusable generic versions.

    Key lemmas:
      - [qe_raw_FElem_split] / [qe_raw_FElem_join] — 2-way
      - [ce_raw_FElem_split] / [ce_raw_FElem_join] — 3-way
      - [qe_list_decomp] / [ce_list_decomp]
      - [generic_FElem_length]

    Key tactics:
      - [wp_qe_split] / [wp_qe_join]
      - [wp_ce_split] / [wp_ce_join] *)

Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.FieldExtensions.SepFromPutmany.

Import Separation SeparationLogic.

(* ================================================================ *)
(* Reusable list lemmas (same as in QuadraticFieldExtensions.v)      *)
(* ================================================================ *)

Section ListLemmas.
  Context {A : Type}.

  Lemma firstn_skipn_app : forall (l : list A) n, firstn n l ++ skipn n l = l.
  Proof.
    intros. generalize dependent n. induction l.
    - destruct n; auto.
    - intros. destruct n; simpl; auto. rewrite IHl; auto.
  Qed.

  Lemma length_firstn_ge : forall (l : list A) n,
    (length l >= n)%nat -> length (firstn n l) = n.
  Proof.
    intros. generalize dependent n. induction l.
    - intros. simpl in H. destruct n; try lia. simpl. auto.
    - intros. destruct n; simpl; auto. apply f_equal. apply IHl. simpl in H. lia.
  Qed.

  Lemma length_skipn_double : forall (l : list A) n,
    (length l = n + n)%nat -> length (skipn n l) = n.
  Proof.
    intros. pose proof (firstn_skipn_app l n).
    rewrite <- H0 in H. rewrite app_length in H.
    rewrite length_firstn_ge in H; lia.
  Qed.

  Lemma firstn_app_exact : forall (a b : list A),
    firstn (length a) (a ++ b) = a.
  Proof.
    intros. induction a; simpl; auto. rewrite IHa. auto.
  Qed.

  Lemma skipn_app_exact : forall (a b : list A),
    skipn (length a) (a ++ b) = b.
  Proof.
    intros. induction a; simpl; auto.
  Qed.

  Lemma firstn_app_le : forall (a b : list A) n,
    (length a = n)%nat -> firstn n (a ++ b) = a.
  Proof.
    intros. subst. apply firstn_app_exact.
  Qed.

  Lemma skipn_app_le : forall (a b : list A) n,
    (length a = n)%nat -> skipn n (a ++ b) = b.
  Proof.
    intros. subst. apply skipn_app_exact.
  Qed.
End ListLemmas.

(* ================================================================ *)
(* Generic AbstractField.FElem length extraction                    *)
(* ================================================================ *)

Section GenericLength.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.

  Context {F : Type} {fp : FieldParameters F}
          {fr : @FieldRepresentation F fp width BW word mem}.

  Lemma generic_FElem_length pout (out : @felem F fp _ _ _ _ fr) m :
    @FElem F fp _ _ _ _ fr pout out m ->
    length out = @felem_size_in_words F fp _ _ _ _ fr.
  Proof.
    unfold FElem, Bignum.Bignum.
    intros [m1 [m2 [_ [[Hlen _] _]]]]. exact Hlen.
  Qed.
End GenericLength.

(* ================================================================ *)
(* Quadratic extension: 2-way split/join                            *)
(* ================================================================ *)

Section QuadraticSplitJoin.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.

  Context {BaseField : Type}.
  Context {base_fp : FieldParameters BaseField}.
  Context {base_repr : @FieldRepresentation BaseField base_fp width BW word mem}.
  Context {base_repr_ok : @FieldRepresentation_ok BaseField base_fp width BW word mem base_repr}.

  Variable nonresidue : BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Instance QE_fp := QE_field_parameters nonresidue prefix eq_dec_base
    (base_fp := base_fp).
  Local Instance QE_repr := QE_field_representation nonresidue
    (base_fp := base_fp) (base_repr := base_repr).

  Local Notation QE := (BaseField * BaseField)%type.
  Local Notation base_size := (@felem_size_in_words _ base_fp _ _ _ _ base_repr).
  Local Notation base_offset :=
    (Memory.bytes_per_word width * Z.of_nat base_size).
  Local Notation base_offset_word := (word.of_Z base_offset).

  (* List decomposition *)
  Lemma qe_list_decomp : forall l,
    qe_fst_felem l ++ qe_snd_felem l = l.
  Proof. intros. unfold qe_fst_felem, qe_snd_felem. apply firstn_skipn_app. Qed.

  (* Raw Bignum split: QE Bignum → two base Bignums *)
  Lemma qe_raw_FElem_split pout out m :
    @FElem _ QE_fp _ _ _ _ QE_repr pout out m ->
    (@FElem _ base_fp _ _ _ _ base_repr pout (qe_fst_felem out) *
     @FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word)
            (qe_snd_felem out))%sep m.
  Proof.
    intros H.
    unfold FElem, Bignum.Bignum in *.
    destruct H as [me [ma [Hms [[Hme Hlen] Ha]]]].
    subst me. assert (m = ma) by (apply Properties.map.split_empty_l in Hms; exact Hms). subst.
    change (@felem_size_in_words _ QE_fp _ _ _ _ QE_repr)
      with (2 * base_size)%nat in Hlen.
    assert (out = qe_fst_felem out ++ qe_snd_felem out) as Hdecomp
      by (symmetry; apply qe_list_decomp).
    rewrite Hdecomp in Ha.
    apply array_append' in Ha.
    destruct Ha as [m1 [m2 [Hms2 [Ha1 Ha2]]]].
    assert (Hlen1 : length (qe_fst_felem out) = base_size)
      by (unfold qe_fst_felem; apply length_firstn_ge; lia).
    rewrite Hlen1 in Ha2.
    rewrite <- (@word.ring_morph_mul _ _ word_ok) in Ha2.
    exists m1, m2. split; [exact Hms2 |]. split.
    - exists map.empty, m1. split. { apply Properties.map.split_empty_l. reflexivity. }
      split; [split; [exact eq_refl | exact Hlen1] | exact Ha1].
    - exists map.empty, m2. split. { apply Properties.map.split_empty_l. reflexivity. }
      split; [split; [exact eq_refl |] |].
      + unfold qe_snd_felem. apply length_skipn_double. lia.
      + exact Ha2.
  Qed.

  (* Raw Bignum join: two base Bignums → QE Bignum *)
  Lemma qe_raw_FElem_join pout out1 out2 m :
    length out1 = base_size ->
    length out2 = base_size ->
    (@FElem _ base_fp _ _ _ _ base_repr pout out1 *
     @FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word) out2)%sep m ->
    @FElem _ QE_fp _ _ _ _ QE_repr pout (out1 ++ out2) m.
  Proof.
    intros Hlen1 Hlen2 H.
    unfold FElem, Bignum.Bignum in *.
    destruct H as [m1 [m2 [Hms [H1 H2]]]].
    destruct H1 as [me1 [ma1 [Hms1 [[Hme1 Hlen1'] Ha1]]]].
    subst me1. assert (m1 = ma1) by (apply Properties.map.split_empty_l in Hms1; exact Hms1). subst.
    destruct H2 as [me2 [ma2 [Hms2 [[Hme2 Hlen2'] Ha2]]]].
    subst me2. assert (m2 = ma2) by (apply Properties.map.split_empty_l in Hms2; exact Hms2). subst.
    exists map.empty, m. split. { apply Properties.map.split_empty_l. reflexivity. }
    split.
    - split; [exact eq_refl |].
      rewrite app_length.
      change (@felem_size_in_words _ QE_fp _ _ _ _ QE_repr)
        with (2 * base_size)%nat. lia.
    - apply array_append'.
      exists ma1, ma2. split; [exact Hms |]. split; [exact Ha1 |].
      rewrite Hlen1'.
      rewrite <- (@word.ring_morph_mul _ _ word_ok).
      exact Ha2.
  Qed.

End QuadraticSplitJoin.

(* ================================================================ *)
(* Cubic extension: 3-way split/join                                *)
(* ================================================================ *)

Section CubicSplitJoin.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.

  Context {BaseField : Type}.
  Context {base_fp : FieldParameters BaseField}.
  Context {base_repr : @FieldRepresentation BaseField base_fp width BW word mem}.
  Context {base_repr_ok : @FieldRepresentation_ok BaseField base_fp width BW word mem base_repr}.

  Variable mul_by_nr : BaseField -> BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Instance CE_fp := CE_field_parameters mul_by_nr prefix eq_dec_base
    (base_fp := base_fp).
  Local Instance CE_repr := CE_field_representation mul_by_nr
    (base_fp := base_fp) (base_repr := base_repr).

  Local Notation CE := (BaseField * BaseField * BaseField)%type.
  Local Notation base_size := (@felem_size_in_words _ base_fp _ _ _ _ base_repr).
  Local Notation base_offset :=
    (Memory.bytes_per_word width * Z.of_nat base_size).
  Local Notation base_offset_word := (word.of_Z base_offset).

  (* List decomposition *)
  Lemma ce_list_decomp : forall l,
    ce_c0_felem l ++ ce_c1_felem l ++ ce_c2_felem l = l.
  Proof.
    intros.
    unfold ce_c0_felem, ce_c1_felem, ce_c2_felem.
    rewrite <- (firstn_skipn_app (skipn base_size l) base_size) at 2.
    rewrite <- (firstn_skipn_app l base_size) at 4.
    rewrite app_assoc. reflexivity.
  Qed.

  (* Raw Bignum split: CE Bignum → three base Bignums *)
  Lemma ce_raw_FElem_split pout out m :
    @FElem _ CE_fp _ _ _ _ CE_repr pout out m ->
    (@FElem _ base_fp _ _ _ _ base_repr pout (ce_c0_felem out) *
     (@FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word)
             (ce_c1_felem out) *
      @FElem _ base_fp _ _ _ _ base_repr
             (word.add pout (word.of_Z (2 * base_offset)))
             (ce_c2_felem out)))%sep m.
  Proof.
    intros H.
    unfold FElem, Bignum.Bignum in *.
    destruct H as [me [ma [Hms [[Hme Hlen] Ha]]]].
    subst me. assert (m = ma) by (apply Properties.map.split_empty_l in Hms; exact Hms). subst.
    change (@felem_size_in_words _ CE_fp _ _ _ _ CE_repr)
      with (3 * base_size)%nat in Hlen.
    (* Split into c0 ++ (c1 ++ c2) *)
    assert (out = ce_c0_felem out ++ ce_c1_felem out ++ ce_c2_felem out) as Hdecomp
      by (symmetry; apply ce_list_decomp).
    rewrite Hdecomp in Ha.
    rewrite app_assoc in Ha.
    apply array_append' in Ha.
    destruct Ha as [m0 [m12 [Hms0 [Ha0 Ha12]]]].
    assert (Hlen0 : length (ce_c0_felem out) = base_size)
      by (unfold ce_c0_felem; apply length_firstn_ge; lia).
    (* Split c1 ++ c2 *)
    rewrite Hlen0 in Ha12.
    rewrite <- (@word.ring_morph_mul _ _ word_ok) in Ha12.
    apply array_append' in Ha12.
    destruct Ha12 as [m1 [m2 [Hms12 [Ha1 Ha2]]]].
    assert (Hlen1 : length (ce_c1_felem out) = base_size).
    { unfold ce_c1_felem. apply length_firstn_ge.
      assert (length (skipn base_size out) = (3 * base_size - base_size)%nat)
        by (rewrite skipn_length; lia).
      lia. }
    rewrite Hlen1 in Ha2.
    (* Fix offset for c2: ptr + base_size + base_size = ptr + 2*base_size *)
    replace (word.add (word.add pout base_offset_word)
                      (word.mul (word.of_Z (Memory.bytes_per_word width))
                                (word.of_Z (Z.of_nat base_size))))
      with (word.add pout (word.of_Z (2 * base_offset))) in Ha2.
    2: { rewrite <- (@word.ring_morph_mul _ _ word_ok).
         rewrite word.add_assoc. f_equal.
         rewrite <- word.ring_morph_add. f_equal. lia. }
    (* Build the 3-way sep *)
    exists m0, (map.putmany m1 m2).
    split.
    { destruct Hms0 as [Hms0eq Hms0d].
      destruct Hms12 as [Hms12eq Hms12d].
      split.
      - rewrite Hms0eq, Hms12eq. reflexivity.
      - rewrite Hms12eq in Hms0d.
        apply map.disjoint_putmany_r in Hms0d. destruct Hms0d.
        apply map.disjoint_putmany_r. split; assumption. }
    split.
    - exists map.empty, m0. split. { apply Properties.map.split_empty_l. reflexivity. }
      split; [split; [exact eq_refl | exact Hlen0] | exact Ha0].
    - exists m1, m2. split.
      { exact Hms12. }
      split.
      + exists map.empty, m1. split. { apply Properties.map.split_empty_l. reflexivity. }
        split; [split; [exact eq_refl | exact Hlen1] | exact Ha1].
      + exists map.empty, m2. split. { apply Properties.map.split_empty_l. reflexivity. }
        split; [split; [exact eq_refl |] | exact Ha2].
        unfold ce_c2_felem. rewrite skipn_length. lia.
  Qed.

  (* Raw Bignum join: three base Bignums → CE Bignum *)
  Lemma ce_raw_FElem_join pout out0 out1 out2 m :
    length out0 = base_size ->
    length out1 = base_size ->
    length out2 = base_size ->
    (@FElem _ base_fp _ _ _ _ base_repr pout out0 *
     (@FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word) out1 *
      @FElem _ base_fp _ _ _ _ base_repr
             (word.add pout (word.of_Z (2 * base_offset))) out2))%sep m ->
    @FElem _ CE_fp _ _ _ _ CE_repr pout (out0 ++ out1 ++ out2) m.
  Proof.
    intros Hlen0 Hlen1 Hlen2 H.
    unfold FElem, Bignum.Bignum in *.
    destruct H as [m0 [m12 [Hms0 [H0 H12]]]].
    destruct H0 as [me0 [ma0 [Hms_0 [[Hme0 Hlen0'] Ha0]]]].
    subst me0. assert (m0 = ma0) by (apply Properties.map.split_empty_l in Hms_0; exact Hms_0). subst.
    destruct H12 as [m1 [m2 [Hms12 [H1 H2]]]].
    destruct H1 as [me1 [ma1 [Hms_1 [[Hme1 Hlen1'] Ha1]]]].
    subst me1. assert (m1 = ma1) by (apply Properties.map.split_empty_l in Hms_1; exact Hms_1). subst.
    destruct H2 as [me2 [ma2 [Hms_2 [[Hme2 Hlen2'] Ha2]]]].
    subst me2. assert (m2 = ma2) by (apply Properties.map.split_empty_l in Hms_2; exact Hms_2). subst.
    exists map.empty, m. split. { apply Properties.map.split_empty_l. reflexivity. }
    split.
    - split; [exact eq_refl |].
      rewrite !app_length.
      change (@felem_size_in_words _ CE_fp _ _ _ _ CE_repr)
        with (3 * base_size)%nat. lia.
    - (* Reconstruct array from three pieces *)
      rewrite app_assoc.
      apply array_append'.
      (* Combine m1, m2 into the c1++c2 array *)
      assert (Harray12 :
        array scalar (word.of_Z (Memory.bytes_per_word width))
              (word.add pout base_offset_word) (out1 ++ out2)
              (map.putmany ma1 ma2)).
      { apply array_append'.
        exists ma1, ma2. split; [exact Hms12 |]. split; [exact Ha1 |].
        rewrite Hlen1'.
        (* Fix offset: (ptr+off) + off = ptr + 2*off *)
        replace (word.add (word.add pout base_offset_word)
                          (word.mul (word.of_Z (Memory.bytes_per_word width))
                                    (word.of_Z (Z.of_nat base_size))))
          with (word.add pout (word.of_Z (2 * base_offset))).
        2: { rewrite <- (@word.ring_morph_mul _ _ word_ok).
             rewrite word.add_assoc. f_equal.
             rewrite <- word.ring_morph_add. f_equal. lia. }
        exact Ha2. }
      exists ma0, (map.putmany ma1 ma2).
      split.
      { destruct Hms0 as [Hms0eq Hms0d].
        destruct Hms12 as [Hms12eq Hms12d].
        split.
        - rewrite Hms0eq, Hms12eq. reflexivity.
        - rewrite Hms12eq in Hms0d.
          apply map.disjoint_putmany_r in Hms0d. destruct Hms0d.
          apply map.disjoint_putmany_r. split; assumption. }
      split; [exact Ha0 |].
      rewrite Hlen0'.
      rewrite <- (@word.ring_morph_mul _ _ word_ok).
      exact Harray12.
  Qed.

End CubicSplitJoin.

(* ================================================================ *)
(* Ltac: generic split/join tactics                                 *)
(* ================================================================ *)

(** [wp_qe_split H] — Split a quadratic extension FElem hypothesis H
    into two base-field FElem hypotheses + disjointness facts. *)
Ltac wp_qe_split H :=
  let m1 := fresh "m" in let m2 := fresh "m" in
  let Hsep := fresh "Hsep" in
  let H1 := fresh "Hfe" in let H2 := fresh "Hfe" in
  let Heq := fresh "Heq" in let Hd := fresh "Hd" in
  pose proof (qe_raw_FElem_split _ _ _ _ _ _ _ H)
    as [m1 [m2 [Hsep [H1 H2]]]];
  destruct Hsep as [Heq Hd]; try subst;
  split_all_disjointness.

(** [wp_qe_join ptr Hfst Hsnd m_fst m_snd] — Join two base-field
    FElem hypotheses back into a quadratic extension FElem. *)
Ltac wp_qe_join ptr Hfst Hsnd m_fst m_snd :=
  let Hlen_fst := fresh "Hlen" in
  let Hlen_snd := fresh "Hlen" in
  pose proof (generic_FElem_length _ _ _ Hfst) as Hlen_fst;
  pose proof (generic_FElem_length _ _ _ Hsnd) as Hlen_snd;
  let Hjoin := fresh "Hjoin" in
  assert (Hjoin : (@FElem _ _ _ _ _ _ _ ptr _ *
                   @FElem _ _ _ _ _ _ _ _ _)%sep (map.putmany m_fst m_snd))
    by (exists m_fst, m_snd; split;
        [split; [reflexivity | map_disjoint_auto] |];
        split; [exact Hfst | exact Hsnd]);
  let Hqe := fresh "Hqe" in
  pose proof (qe_raw_FElem_join _ _ _ _ _ _ ptr _ _ (map.putmany m_fst m_snd)
    Hlen_fst Hlen_snd Hjoin) as Hqe.

(** [wp_ce_split H] — Split a cubic extension FElem hypothesis H
    into three base-field FElem hypotheses + disjointness facts. *)
Ltac wp_ce_split H :=
  let m0 := fresh "m" in let m12 := fresh "m" in
  let m1 := fresh "m" in let m2 := fresh "m" in
  let Hsep0 := fresh "Hsep" in let Hsep12 := fresh "Hsep" in
  let H0 := fresh "Hfe" in let H12 := fresh "Hfe" in
  let H1 := fresh "Hfe" in let H2 := fresh "Hfe" in
  let Heq := fresh "Heq" in let Hd := fresh "Hd" in
  pose proof (ce_raw_FElem_split _ _ _ _ _ _ _ H)
    as [m0 [m12 [Hsep0 [H0 H12]]]];
  destruct Hsep0 as [Heq Hd]; try subst;
  destruct H12 as [m1 [m2 [Hsep12 [H1 H2]]]];
  destruct Hsep12 as [Heq Hd]; try subst;
  split_all_disjointness.

(** [wp_ce_join ptr H0 H1 H2 m0 m1 m2] — Join three base-field
    FElem hypotheses back into a cubic extension FElem. *)
Ltac wp_ce_join ptr H0 H1 H2 m0 m1 m2 :=
  let Hlen0 := fresh "Hlen" in
  let Hlen1 := fresh "Hlen" in
  let Hlen2 := fresh "Hlen" in
  pose proof (generic_FElem_length _ _ _ H0) as Hlen0;
  pose proof (generic_FElem_length _ _ _ H1) as Hlen1;
  pose proof (generic_FElem_length _ _ _ H2) as Hlen2;
  let Hjoin := fresh "Hjoin" in
  assert (Hjoin : (@FElem _ _ _ _ _ _ _ ptr _ *
                   (@FElem _ _ _ _ _ _ _ _ _ *
                    @FElem _ _ _ _ _ _ _ _ _))%sep
                  (map.putmany m0 (map.putmany m1 m2)))
    by (exists m0, (map.putmany m1 m2); split;
        [split; [reflexivity | map_disjoint_auto] |];
        split; [exact H0 |
                exists m1, m2; split;
                [split; [reflexivity | map_disjoint_auto] |];
                split; [exact H1 | exact H2]]);
  let Hce := fresh "Hce" in
  pose proof (ce_raw_FElem_join _ _ _ _ _ _ ptr _ _ _
    (map.putmany m0 (map.putmany m1 m2))
    Hlen0 Hlen1 Hlen2 Hjoin) as Hce.
