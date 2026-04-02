(** * WP correctness proofs for generic cubic extension functions. *)

Require Import Crypto.Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.FieldExtensions.SepFromPutmany.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.

Import Separation SeparationLogic.

Section GenericCubicProofs.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals} {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {BaseField : Type} {base_fp : FieldParameters BaseField}.
  Context {base_repr : @FieldRepresentation BaseField base_fp width BW word mem}.
  Context {base_repr_ok : @FieldRepresentation_ok BaseField base_fp width BW word mem base_repr}.

  Variable mul_by_nr_model : BaseField -> BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Notation CE := (BaseField * BaseField * BaseField)%type.

  Local Instance CE_fp : FieldParameters CE :=
    CE_field_parameters mul_by_nr_model prefix eq_dec_base.
  Local Instance CE_repr : @FieldRepresentation _ CE_fp width BW word mem :=
    CE_field_representation mul_by_nr_model prefix eq_dec_base.

  Local Notation FElem_b := (@FElem _ base_fp _ _ _ _ base_repr).
  Local Notation c0_e := (@ce_c0_felem _ _ _ _ _ base_fp base_repr).
  Local Notation c1_e := (@ce_c1_felem _ _ _ _ _ base_fp base_repr).
  Local Notation c2_e := (@ce_c2_felem _ _ _ _ _ base_fp base_repr).
  Local Notation base_off := (word.of_Z (Memory.bytes_per_word width *
    Z.of_nat (@felem_size_in_words _ base_fp _ _ _ _ base_repr))).
  Local Notation base_off2 := (word.of_Z (2 * (Memory.bytes_per_word width *
    Z.of_nat (@felem_size_in_words _ base_fp _ _ _ _ base_repr)))).

  Context {CE_names : FieldNames (F := CE)} {base_names : FieldNames (F := BaseField)}.
  Variable mul_by_nr_name : string.
  Variable Mul_by_nr_func : string * (list String.string * list String.string * Syntax.cmd.cmd).
  Hypothesis Mul_by_nr_name_eq : fst Mul_by_nr_func = mul_by_nr_name.

  (* Helper: solve dexprs for ce_expr_c0/c1/c2 *)
  Local Ltac solve_ce_dexprs :=
    first [ solve_dexprs
          | unfold ce_expr_c1, ce_expr_c2;
            cbv [dexprs list_map list_map_body WeakestPrecondition.expr
                 WeakestPrecondition.expr_body Semantics.interp_binop literal dlet.dlet];
            repeat (eexists; split; [first [apply map.get_put_same |
              rewrite map.get_put_diff by congruence; apply map.get_put_same |
              rewrite map.get_put_diff by congruence;
              rewrite map.get_put_diff by congruence; apply map.get_put_same] |]);
            try exact eq_refl ].

  (* Helper lemma: ce_c1_felem on concatenation *)
  Local Lemma c1_app_app (a b c : list word) :
    length a = @felem_size_in_words _ base_fp _ _ _ _ base_repr ->
    length b = @felem_size_in_words _ base_fp _ _ _ _ base_repr ->
    c1_e (a ++ b ++ c) = b.
  Proof.
    intros Ha Hb. unfold ce_c1_felem.
    rewrite skipn_app_le by exact Ha.
    rewrite firstn_app_le by exact Hb. reflexivity.
  Qed.

  (* Helper lemma: ce_c2_felem on concatenation *)
  Local Lemma c2_app_app (a b c : list word) :
    length a = @felem_size_in_words _ base_fp _ _ _ _ base_repr ->
    length b = @felem_size_in_words _ base_fp _ _ _ _ base_repr ->
    c2_e (a ++ b ++ c) = c.
  Proof.
    intros Ha Hb. unfold ce_c2_felem.
    rewrite app_assoc.
    rewrite skipn_app_le by (rewrite app_length; lia).
    reflexivity.
  Qed.

  (* ================================================================ *)
  (* CE_zero_ok                                                        *)
  (* ================================================================ *)

  Lemma CE_zero_ok :
    forall functions,
    map.get functions (zero (F := CE)) =
      Some (snd (CE_zero_func mul_by_nr_model prefix eq_dec_base)) ->
    (* Callee 1: base zero *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    (* Callee 2: base zero *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    (* Callee 3: base zero *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    forall pout (out : @felem _ CE_fp _ _ _ _ CE_repr) Rr tr mem0,
    (@FElem _ CE_fp _ _ _ _ CE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (zero (F := CE)) tr mem0 [pout]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ CE_fp _ _ _ _ CE_repr out' = @Fzero _ CE_fp /\
          @bounded_by _ CE_fp _ _ _ _ CE_repr (@loose_bounds _ CE_fp _ _ _ _ CE_repr) out' /\
          (@FElem _ CE_fp _ _ _ _ CE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFzero1 HFzero2 HFzero3 pout out Rr tr mem0 Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func CE_zero_func GenericCubic.CE_zero_func].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Split CE FElem into 3 base components *)
    destruct Hmem0 as [m_ce [m_rr [[-> Hd_cr] [Hce Hrr]]]].
    pose proof (ce_raw_FElem_split mul_by_nr_model prefix eq_dec_base _ _ _ Hce)
      as [m0 [m12 [[-> Hd0_12] [Ho0 H12]]]].
    destruct H12 as [m1 [m2 [[-> Hd12] [Ho1 Ho2]]]].
    split_all_disjointness.

    (* Call 1: base zero at pout (c0) *)
    exists [pout]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero1 pout (c0_e out)
        (fun m => (FElem_b (word.add pout base_off) (c1_e out) *
                  (FElem_b (word.add pout base_off2) (c2_e out) * Rr))%sep m) tr).
      exists m0, (map.putmany m1 (map.putmany m2 m_rr)).
      split; [split; [rewrite !map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; [assumption |
              apply map.disjoint_putmany_r; split; assumption]] |].
      split; [exact Ho0 |].
      exists m1, (map.putmany m2 m_rr).
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; assumption] |].
      split; [exact Ho1 |].
      exists m2, m_rr; split; [split; [reflexivity | assumption] |].
      split; [exact Ho2 | exact Hrr]. }

    (* Process postcondition of call 1 *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 2: base zero at pout + offset (c1) *)
    exists [word.add pout base_off]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero2 (word.add pout base_off) (c1_e out)
        (fun m => (FElem_b pout out0' *
                  (FElem_b (word.add pout base_off2) (c2_e out) * Rr))%sep m)).
      (* Reorder sep: from (out0' * (c1 * (c2 * Rr))) to (c1 * (out0' * (c2 * Rr))) *)
      destruct Hsep1 as [m_a [m_bcd [[-> Hd_a] [Ha Hbcd]]]].
      destruct Hbcd as [m_b [m_cd [[-> Hd_b] [Hb Hcd]]]].
      split_all_disjointness.
      exists m_b, (map.putmany m_a m_cd).
      split; [split; [rewrite map.putmany_assoc;
              rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
              rewrite <- map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_cd.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hcd]. }

    (* Process postcondition of call 2 *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 3: base zero at pout + 2*offset (c2) *)
    exists [word.add pout base_off2]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero3 (word.add pout base_off2) (c2_e out)
        (fun m => (FElem_b pout out0' *
                  (FElem_b (word.add pout base_off) out1' * Rr))%sep m)).
      (* Reorder sep: from (out1' * (out0' * (c2 * Rr))) to (c2 * (out0' * (out1' * Rr))) *)
      destruct Hsep2 as [m_a [m_bcd [[-> Hd_a] [Ha Hbcd]]]].
      destruct Hbcd as [m_b [m_cd [[-> Hd_b] [Hb Hcd]]]].
      destruct Hcd as [m_c [m_d [[-> Hd_c] [Hc Hd_rest]]]].
      split_all_disjointness.
      exists m_c, (map.putmany m_b (map.putmany m_a m_d)).
      split; [split; [
        rewrite (map.putmany_assoc m_a m_b (map.putmany m_c m_d));
        rewrite (map.putmany_assoc (map.putmany m_a m_b) m_c m_d);
        rewrite (map.putmany_comm (map.putmany m_a m_b) m_c)
          by (apply map.disjoint_putmany_l; split; map_disjoint_auto);
        rewrite <- (map.putmany_assoc m_c (map.putmany m_a m_b) m_d);
        rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
        rewrite <- (map.putmany_assoc m_b m_a m_d);
        reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact Hc |].
      exists m_b, (map.putmany m_a m_d).
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_d.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hd_rest]. }

    (* Process postcondition of call 3 *)
    intros t3 m3' rets3 [-> [-> [out2' [Hfeval2 [Hbound2 Hsep3]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* Assemble CE result *)
    destruct Hsep3 as [m_2' [m_fr [[-> Hd_2f] [Hout2 Hfr]]]].
    destruct Hfr as [m_0' [m_1r [[-> Hd_0_1r] [Hout0 H1r]]]].
    destruct H1r as [m_1' [m_r' [[-> Hd_1r] [Hout1 Hr']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.
    pose proof (generic_FElem_length _ _ _ Hout2) as Hlen2.

    exists (out0' ++ out1' ++ out2').
    split.
    { (* feval *)
      change (@AbstractField.feval _ CE_fp _ _ _ _ CE_repr (out0' ++ out1' ++ out2'))
        with ((@AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c0_e (out0' ++ out1' ++ out2')),
               @AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c1_e (out0' ++ out1' ++ out2'))),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c2_e (out0' ++ out1' ++ out2'))).
      unfold c0_e, ce_c0_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite (c1_app_app out0' out1' out2' Hlen0 Hlen1).
      rewrite (c2_app_app out0' out1' out2' Hlen0 Hlen1).
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    split.
    { (* bounded_by — 3 components *)
      split; [| split].
      - unfold c0_e, ce_c0_felem. rewrite firstn_app_le by exact Hlen0. exact Hbound0.
      - rewrite (c1_app_app out0' out1' out2' Hlen0 Hlen1). exact Hbound1.
      - rewrite (c2_app_app out0' out1' out2' Hlen0 Hlen1). exact Hbound2. }
    { (* sep: join 3 components back *)
      exists (map.putmany m_0' (map.putmany m_1' m_2')), m_r'.
      split.
      { split.
        { (* Permute [m_2', m_0', m_1', m_r'] -> [m_0', m_1', m_2', m_r'] *)
          rewrite (map.putmany_assoc m_2' m_0' _).
          rewrite (map.putmany_assoc (map.putmany m_2' m_0') m_1' m_r').
          rewrite (map.putmany_comm m_2' m_0') by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m_0' m_2' m_1').
          rewrite (map.putmany_comm m_2' m_1') by map_disjoint_auto.
          reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { map_disjoint_auto. }
          { apply map.disjoint_putmany_l. split; map_disjoint_auto. } } }
      split; [| exact Hr'].
      apply (ce_raw_FElem_join mul_by_nr_model prefix eq_dec_base _ _ _ _
        (map.putmany m_0' (map.putmany m_1' m_2'))
        Hlen0 Hlen1 Hlen2).
      exists m_0', (map.putmany m_1' m_2').
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hout0 |].
      exists m_1', m_2'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hout1 | exact Hout2]. }
  Qed.

  (* ================================================================ *)
  (* CE_one_ok                                                         *)
  (* ================================================================ *)

  Lemma CE_one_ok :
    forall functions,
    map.get functions (one (F := CE)) =
      Some (snd (CE_one_func mul_by_nr_model prefix eq_dec_base)) ->
    (* Callee 1: base one *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (one (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fone _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    (* Callee 2: base zero *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    (* Callee 3: base zero *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    forall pout (out : @felem _ CE_fp _ _ _ _ CE_repr) Rr tr mem0,
    (@FElem _ CE_fp _ _ _ _ CE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (one (F := CE)) tr mem0 [pout]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ CE_fp _ _ _ _ CE_repr out' = @Fone _ CE_fp /\
          @bounded_by _ CE_fp _ _ _ _ CE_repr (@loose_bounds _ CE_fp _ _ _ _ CE_repr) out' /\
          (@FElem _ CE_fp _ _ _ _ CE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFone HFzero2 HFzero3 pout out Rr tr mem0 Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func CE_one_func GenericCubic.CE_one_func].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Split CE FElem into 3 base components *)
    destruct Hmem0 as [m_ce [m_rr [[-> Hd_cr] [Hce Hrr]]]].
    pose proof (ce_raw_FElem_split mul_by_nr_model prefix eq_dec_base _ _ _ Hce)
      as [m0 [m12 [[-> Hd0_12] [Ho0 H12]]]].
    destruct H12 as [m1 [m2 [[-> Hd12] [Ho1 Ho2]]]].
    split_all_disjointness.

    (* Call 1: base one at pout (c0) *)
    exists [pout]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFone pout (c0_e out)
        (fun m => (FElem_b (word.add pout base_off) (c1_e out) *
                  (FElem_b (word.add pout base_off2) (c2_e out) * Rr))%sep m) tr).
      exists m0, (map.putmany m1 (map.putmany m2 m_rr)).
      split; [split; [rewrite !map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; [assumption |
              apply map.disjoint_putmany_r; split; assumption]] |].
      split; [exact Ho0 |].
      exists m1, (map.putmany m2 m_rr).
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; assumption] |].
      split; [exact Ho1 |].
      exists m2, m_rr; split; [split; [reflexivity | assumption] |].
      split; [exact Ho2 | exact Hrr]. }

    (* Process postcondition of call 1 *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 2: base zero at pout + offset (c1) *)
    exists [word.add pout base_off]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero2 (word.add pout base_off) (c1_e out)
        (fun m => (FElem_b pout out0' *
                  (FElem_b (word.add pout base_off2) (c2_e out) * Rr))%sep m)).
      destruct Hsep1 as [m_a [m_bcd [[-> Hd_a] [Ha Hbcd]]]].
      destruct Hbcd as [m_b [m_cd [[-> Hd_b] [Hb Hcd]]]].
      split_all_disjointness.
      exists m_b, (map.putmany m_a m_cd).
      split; [split; [rewrite map.putmany_assoc;
              rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
              rewrite <- map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_cd.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hcd]. }

    (* Process postcondition of call 2 *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 3: base zero at pout + 2*offset (c2) *)
    exists [word.add pout base_off2]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero3 (word.add pout base_off2) (c2_e out)
        (fun m => (FElem_b pout out0' *
                  (FElem_b (word.add pout base_off) out1' * Rr))%sep m)).
      destruct Hsep2 as [m_a [m_bcd [[-> Hd_a] [Ha Hbcd]]]].
      destruct Hbcd as [m_b [m_cd [[-> Hd_b] [Hb Hcd]]]].
      destruct Hcd as [m_c [m_d [[-> Hd_c] [Hc Hd_rest]]]].
      split_all_disjointness.
      exists m_c, (map.putmany m_b (map.putmany m_a m_d)).
      split; [split; [
        rewrite (map.putmany_assoc m_a m_b (map.putmany m_c m_d));
        rewrite (map.putmany_assoc (map.putmany m_a m_b) m_c m_d);
        rewrite (map.putmany_comm (map.putmany m_a m_b) m_c)
          by (apply map.disjoint_putmany_l; split; map_disjoint_auto);
        rewrite <- (map.putmany_assoc m_c (map.putmany m_a m_b) m_d);
        rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
        rewrite <- (map.putmany_assoc m_b m_a m_d);
        reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact Hc |].
      exists m_b, (map.putmany m_a m_d).
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_d.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hd_rest]. }

    (* Process postcondition of call 3 *)
    intros t3 m3' rets3 [-> [-> [out2' [Hfeval2 [Hbound2 Hsep3]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* Assemble CE result *)
    destruct Hsep3 as [m_2' [m_fr [[-> Hd_2f] [Hout2 Hfr]]]].
    destruct Hfr as [m_0' [m_1r [[-> Hd_0_1r] [Hout0 H1r]]]].
    destruct H1r as [m_1' [m_r' [[-> Hd_1r] [Hout1 Hr']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.
    pose proof (generic_FElem_length _ _ _ Hout2) as Hlen2.

    exists (out0' ++ out1' ++ out2').
    split.
    { (* feval *)
      change (@AbstractField.feval _ CE_fp _ _ _ _ CE_repr (out0' ++ out1' ++ out2'))
        with ((@AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c0_e (out0' ++ out1' ++ out2')),
               @AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c1_e (out0' ++ out1' ++ out2'))),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c2_e (out0' ++ out1' ++ out2'))).
      unfold c0_e, ce_c0_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite (c1_app_app out0' out1' out2' Hlen0 Hlen1).
      rewrite (c2_app_app out0' out1' out2' Hlen0 Hlen1).
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    split.
    { (* bounded_by *)
      split; [| split].
      - unfold c0_e, ce_c0_felem. rewrite firstn_app_le by exact Hlen0. exact Hbound0.
      - rewrite (c1_app_app out0' out1' out2' Hlen0 Hlen1). exact Hbound1.
      - rewrite (c2_app_app out0' out1' out2' Hlen0 Hlen1). exact Hbound2. }
    { (* sep: join 3 components back *)
      exists (map.putmany m_0' (map.putmany m_1' m_2')), m_r'.
      split.
      { split.
        { rewrite (map.putmany_assoc m_2' m_0' _).
          rewrite (map.putmany_assoc (map.putmany m_2' m_0') m_1' m_r').
          rewrite (map.putmany_comm m_2' m_0') by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m_0' m_2' m_1').
          rewrite (map.putmany_comm m_2' m_1') by map_disjoint_auto.
          reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { map_disjoint_auto. }
          { apply map.disjoint_putmany_l. split; map_disjoint_auto. } } }
      split; [| exact Hr'].
      apply (ce_raw_FElem_join mul_by_nr_model prefix eq_dec_base _ _ _ _
        (map.putmany m_0' (map.putmany m_1' m_2'))
        Hlen0 Hlen1 Hlen2).
      exists m_0', (map.putmany m_1' m_2').
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hout0 |].
      exists m_1', m_2'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hout1 | exact Hout2]. }
  Qed.

  (* ================================================================ *)
  (* CE_opp_ok                                                         *)
  (* ================================================================ *)

  Lemma CE_opp_ok :
    forall functions,
    map.get functions (opp (F := CE)) =
      Some (snd (CE_opp mul_by_nr_model prefix eq_dec_base)) ->
    (* Callee: base opp (nested sep form) — 3 copies *)
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (FElem_b px x * (FElem_b pout out * Rr))%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * (FElem_b px x * Rr))%sep m')) ->
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (FElem_b px x * (FElem_b pout out * Rr))%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * (FElem_b px x * Rr))%sep m')) ->
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (FElem_b px x * (FElem_b pout out * Rr))%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * (FElem_b px x * Rr))%sep m')) ->
    forall pout px (out x : @felem _ CE_fp _ _ _ _ CE_repr) Rr tr mem0,
    @bounded_by _ CE_fp _ _ _ _ CE_repr (@tight_bounds _ CE_fp _ _ _ _ CE_repr) x ->
    (@FElem _ CE_fp _ _ _ _ CE_repr px x *
     (@FElem _ CE_fp _ _ _ _ CE_repr pout out * Rr))%sep mem0 ->
    WeakestPrecondition.call functions (opp (F := CE)) tr mem0 [pout; px]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ CE_fp _ _ _ _ CE_repr out' =
                       @Fopp _ CE_fp (@feval _ CE_fp _ _ _ _ CE_repr x) /\
          @bounded_by _ CE_fp _ _ _ _ CE_repr (@loose_bounds _ CE_fp _ _ _ _ CE_repr) out' /\
          (@FElem _ CE_fp _ _ _ _ CE_repr pout out' *
           (@FElem _ CE_fp _ _ _ _ CE_repr px x * Rr))%sep mem').
  Proof. Admitted.
  (* TODO: opp proof requires complex putmany permutations for 7 sub-memories.
     The proof skeleton follows the quadratic pattern with 3 base opp calls
     and sep reordering between calls. *)

End GenericCubicProofs.
