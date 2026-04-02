(** * WP correctness proofs for generic quadratic extension functions. *)

Require Import Crypto.Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.FieldExtensions.SepFromPutmany.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.

Import Separation SeparationLogic.

Section GenericQuadProofs.
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

  Variable nonresidue : BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Instance QE_fp : FieldParameters (BaseField * BaseField) :=
    QE_field_parameters nonresidue prefix eq_dec_base.
  Local Instance QE_repr : @FieldRepresentation _ QE_fp width BW word mem :=
    QE_field_representation nonresidue prefix eq_dec_base.

  Local Notation QE := (BaseField * BaseField)%type.
  Local Notation FElem_b := (@FElem _ base_fp _ _ _ _ base_repr).
  Local Notation fst_e := (@qe_fst_felem _ _ _ _ _ base_fp base_repr).
  Local Notation snd_e := (@qe_snd_felem _ _ _ _ _ base_fp base_repr).
  Local Notation base_off := (word.of_Z (Memory.bytes_per_word width *
    Z.of_nat (@felem_size_in_words _ base_fp _ _ _ _ base_repr))).

  Context {QE_names : FieldNames (F := QE)} {base_names : FieldNames (F := BaseField)}.
  Variable mul_by_nr_name : string.
  Variable Mul_by_nr_func : string * (list String.string * list String.string * Syntax.cmd.cmd).
  Hypothesis Mul_by_nr_name_eq : fst Mul_by_nr_func = mul_by_nr_name.

  (* Helper: solve dexprs for qe_expr_2nd *)
  Local Ltac solve_qe_dexprs :=
    first [ solve_dexprs
          | unfold qe_expr_2nd;
            cbv [dexprs list_map list_map_body WeakestPrecondition.expr
                 WeakestPrecondition.expr_body Semantics.interp_binop literal dlet.dlet];
            repeat (eexists; split; [first [apply map.get_put_same |
              rewrite map.get_put_diff by congruence; apply map.get_put_same] |]);
            exact eq_refl ].

  (* Helper: reorder sep for the second call *)
  Local Ltac sep_reorder_for_second_call :=
    match goal with
    | Hsep : (_ ⋆ (fun m => (_ ⋆ _)%sep m))%sep ?mem |- (_ ⋆ (fun m => (_ ⋆ _)%sep m))%sep ?mem =>
      let m_a := fresh "m" in let m_bc := fresh "m" in
      let m_b := fresh "m" in let m_c := fresh "m" in
      destruct Hsep as [m_a [m_bc [[[= ->] ?] [?H_a [m_b [m_c [[[= ->] ?] [?H_b ?H_c]]]]]]]];
      split_all_disjointness;
      exists m_b, (map.putmany m_a m_c);
      (split; [split; [rewrite map.putmany_assoc; f_equal;
               apply map.putmany_comm; map_disjoint_auto |
               apply map.disjoint_putmany_r; split; map_disjoint_auto] |]);
      split; [assumption |];
      exists m_a, m_c;
      (split; [split; [reflexivity | map_disjoint_auto] |]);
      split; assumption
    end.

  (* ================================================================ *)
  (* QE_zero_ok                                                        *)
  (* ================================================================ *)

  Lemma QE_zero_ok :
    forall functions,
    map.get functions (zero (F := QE)) =
      Some (snd (QE_zero_func nonresidue prefix eq_dec_base)) ->
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    forall pout (out : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (zero (F := QE)) tr mem0 [pout]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' = @Fzero _ QE_fp /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFzero1 HFzero2 pout out Rr tr mem0 Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func QE_zero_func GenericQuadratic.QE_zero_func].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Split QE FElem *)
    destruct Hmem0 as [m_qe [m_rr [[-> Hd_qr] [Hqe Hrr]]]].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hqe)
      as [m0 [m1 [[-> Hd01] [Ho0 Ho1]]]].
    split_all_disjointness.

    (* Call 1: base zero at pout *)
    exists [pout]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero1 pout (fst_e out)
        (fun m => (FElem_b (word.add pout base_off) (snd_e out) * Rr)%sep m) tr).
      exists m0, (map.putmany m1 m_rr).
      split; [split; [rewrite map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; assumption] |].
      split; [exact Ho0 |].
      exists m1, m_rr; split; [split; [reflexivity | assumption] |].
      split; [exact Ho1 | exact Hrr]. }

    (* Process postcondition *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 2: base zero at pout + offset *)
    exists [word.add pout base_off]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero2 (word.add pout base_off) (snd_e out)
        (fun m => (FElem_b pout out0' * Rr)%sep m)).
      destruct Hsep1 as [m_a [m_bc [[-> Hd_abc] [Ha Hbc]]]].
      destruct Hbc as [m_b [m_c [[-> Hd_bc] [Hb Hc]]]].
      split_all_disjointness.
      exists m_b, (map.putmany m_a m_c).
      split; [split; [rewrite map.putmany_assoc;
              rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
              rewrite <- map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_c.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hc]. }

    (* Process postcondition *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* Assemble QE result — destruct sep first *)
    destruct Hsep2 as [m_1' [m_fr [[-> Hd_1f] [Hout1 Hfr]]]].
    destruct Hfr as [m_0' [m_r' [[-> Hd_0r] [Hout0 Hr']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.

    exists (out0' ++ out1').
    split.
    { (* feval *)
      change (@AbstractField.feval _ QE_fp _ _ _ _ QE_repr (out0' ++ out1'))
        with (@AbstractField.feval _ base_fp _ _ _ _ base_repr (fst_e (out0' ++ out1')),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr (snd_e (out0' ++ out1'))).
      unfold fst_e, qe_fst_felem, snd_e, qe_snd_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite skipn_app_le by exact Hlen0.
      rewrite Hfeval0, Hfeval1. reflexivity. }
    split.
    { (* bounded_by *)
      split; unfold fst_e, snd_e, qe_fst_felem, qe_snd_felem;
        [rewrite firstn_app_le | rewrite skipn_app_le]; try exact Hlen0; assumption. }
    { (* sep: join halves *)
      exists (map.putmany m_0' m_1'), m_r'.
      split.
      { split.
        { rewrite map.putmany_assoc.
          rewrite (map.putmany_comm m_1' m_0') by map_disjoint_auto.
          rewrite <- map.putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_l. split; [map_disjoint_auto | assumption]. } }
      split; [| exact Hr'].
      apply (qe_raw_FElem_join nonresidue prefix eq_dec_base _ _ _ _ Hlen0 Hlen1).
      exists m_0', m_1'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hout0 | exact Hout1]. }
  Qed.

  (* ================================================================ *)
  (* QE_one_ok                                                         *)
  (* ================================================================ *)

  Lemma QE_one_ok :
    forall functions,
    map.get functions (one (F := QE)) =
      Some (snd (QE_one_func nonresidue prefix eq_dec_base)) ->
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
    forall pout (out : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (one (F := QE)) tr mem0 [pout]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' = @Fone _ QE_fp /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFone HFzero pout out Rr tr mem0 Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func QE_one_func GenericQuadratic.QE_one_func].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Split QE FElem *)
    destruct Hmem0 as [m_qe [m_rr [[-> Hd_qr] [Hqe Hrr]]]].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hqe)
      as [m0 [m1 [[-> Hd01] [Ho0 Ho1]]]].
    split_all_disjointness.

    (* Call 1: base one at pout *)
    exists [pout]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFone pout (fst_e out)
        (fun m => (FElem_b (word.add pout base_off) (snd_e out) * Rr)%sep m) tr).
      exists m0, (map.putmany m1 m_rr).
      split; [split; [rewrite map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; assumption] |].
      split; [exact Ho0 |].
      exists m1, m_rr; split; [split; [reflexivity | assumption] |].
      split; [exact Ho1 | exact Hrr]. }

    (* Process postcondition *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 2: base zero at pout + offset *)
    exists [word.add pout base_off]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero (word.add pout base_off) (snd_e out)
        (fun m => (FElem_b pout out0' * Rr)%sep m)).
      destruct Hsep1 as [m_a [m_bc [[-> Hd_abc] [Ha Hbc]]]].
      destruct Hbc as [m_b [m_c [[-> Hd_bc] [Hb Hc]]]].
      split_all_disjointness.
      exists m_b, (map.putmany m_a m_c).
      split; [split; [rewrite map.putmany_assoc;
              rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
              rewrite <- map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_c.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hc]. }

    (* Process postcondition *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* Assemble QE result *)
    destruct Hsep2 as [m_1' [m_fr [[-> Hd_1f] [Hout1 Hfr]]]].
    destruct Hfr as [m_0' [m_r' [[-> Hd_0r] [Hout0 Hr']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.

    exists (out0' ++ out1').
    split.
    { (* feval *)
      change (@AbstractField.feval _ QE_fp _ _ _ _ QE_repr (out0' ++ out1'))
        with (@AbstractField.feval _ base_fp _ _ _ _ base_repr (fst_e (out0' ++ out1')),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr (snd_e (out0' ++ out1'))).
      unfold fst_e, qe_fst_felem, snd_e, qe_snd_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite skipn_app_le by exact Hlen0.
      rewrite Hfeval0, Hfeval1. reflexivity. }
    split.
    { (* bounded_by *)
      split; unfold fst_e, snd_e, qe_fst_felem, qe_snd_felem;
        [rewrite firstn_app_le | rewrite skipn_app_le]; try exact Hlen0; assumption. }
    { (* sep: join halves *)
      exists (map.putmany m_0' m_1'), m_r'.
      split.
      { split.
        { rewrite map.putmany_assoc.
          rewrite (map.putmany_comm m_1' m_0') by map_disjoint_auto.
          rewrite <- map.putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_l. split; [map_disjoint_auto | assumption]. } }
      split; [| exact Hr'].
      apply (qe_raw_FElem_join nonresidue prefix eq_dec_base _ _ _ _ Hlen0 Hlen1).
      exists m_0', m_1'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hout0 | exact Hout1]. }
  Qed.

  (* ================================================================ *)
  (* QE_opp_ok                                                         *)
  (* ================================================================ *)

  Lemma QE_opp_ok :
    forall functions,
    map.get functions (opp (F := QE)) =
      Some (snd (QE_opp nonresidue prefix eq_dec_base)) ->
    (* Callee: base opp (nested sep form) *)
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (FElem_b px x * (FElem_b pout out * Rr))%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * (FElem_b px x * Rr))%sep m')) ->
    (* Same callee for second component *)
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (FElem_b px x * (FElem_b pout out * Rr))%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * (FElem_b px x * Rr))%sep m')) ->
    forall pout px (out x : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@tight_bounds _ QE_fp _ _ _ _ QE_repr) x ->
    (@FElem _ QE_fp _ _ _ _ QE_repr px x *
     (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr))%sep mem0 ->
    WeakestPrecondition.call functions (opp (F := QE)) tr mem0 [pout; px]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' =
                       @Fopp _ QE_fp (@feval _ QE_fp _ _ _ _ QE_repr x) /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' *
           (@FElem _ QE_fp _ _ _ _ QE_repr px x * Rr))%sep mem').
  Proof.
    intros functions EnvContains HFopp1 HFopp2 pout px out x Rr tr mem0
           [Hbound_x0 Hbound_x1] Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func QE_opp GenericQuadratic.QE_opp].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Destruct the nested sep: (QE_x * (QE_out * Rr)) *)
    destruct Hmem0 as [m_x [m_or [[-> Hd_xor] [Hx Hor]]]].
    destruct Hor as [m_o [m_r [[-> Hd_or] [Ho Hr]]]].
    split_all_disjointness.

    (* Split QE FElems into base components *)
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hx)
      as [mx0 [mx1 [[-> Hdx01] [Hx0 Hx1]]]].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Ho)
      as [mo0 [mo1 [[-> Hdo01] [Ho0 Ho1]]]].
    split_all_disjointness.

    (* Call 1: base opp at (pout, px) for first components *)
    exists [pout; px]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFopp1 pout px (fst_e out) (fst_e x)
        (fun m => (FElem_b (word.add px base_off) (snd_e x) *
                  (FElem_b (word.add pout base_off) (snd_e out) * Rr))%sep m) tr).
      { exact Hbound_x0. }
      (* mem0 = putmany (putmany mx0 mx1) (putmany (putmany mo0 mo1) m_r) *)
      (* Need: (FElem_b px x0 * (FElem_b pout o0 * Frame)) mem0 *)
      exists mx0, (map.putmany mo0 (map.putmany mx1 (map.putmany mo1 m_r))).
      split.
      { split.
        - rewrite map.putmany_assoc.
          rewrite <- !map.putmany_assoc.
          rewrite (map.putmany_assoc mx1 mo0 _).
          rewrite (map.putmany_comm mx1 mo0) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc mo0 mx1 _). reflexivity.
        - apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; map_disjoint_auto]]. }
      split; [exact Hx0 |].
      exists mo0, (map.putmany mx1 (map.putmany mo1 m_r)).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact Ho0 |].
      exists mx1, (map.putmany mo1 m_r).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hx1 |].
      exists mo1, m_r.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ho1 | exact Hr]. }

    (* Process postcondition of call 1 *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 2: base opp at (pout+off, px+off) for second components *)
    exists [word.add pout base_off; word.add px base_off]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFopp2 (word.add pout base_off) (word.add px base_off)
                     (snd_e out) (snd_e x)
        (fun m => (FElem_b px (fst_e x) *
                  (FElem_b pout out0' * Rr))%sep m) t1).
      { exact Hbound_x1. }
      (* From Hsep1: (out0' * (x0 * (x1 * (o1 * Rr)))) on m1' *)
      (* Need: (x1 * (o1 * (x0 * (out0' * Rr)))) on m1' *)
      destruct Hsep1 as [ma [mb [[-> Hda'] [Ha' Hb']]]].
      destruct Hb' as [mc [md [[-> Hdb'] [Hc' Hd'']]]].
      destruct Hd'' as [me [mf [[-> Hdc'] [He' Hf']]]].
      destruct Hf' as [mg [mh [[-> Hdd'] [Hg' Hh']]]].
      split_all_disjointness.
      (* Permute [ma,mc,me,mg,mh] -> [me,mg,mc,ma,mh] *)
      exists me, (map.putmany mg (map.putmany mc (map.putmany ma mh))).
      split.
      { split.
        - rewrite (map.putmany_assoc mc me _).
          rewrite (map.putmany_comm mc me) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc me mc _).
          rewrite (map.putmany_assoc ma me _).
          rewrite (map.putmany_comm ma me) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc me ma _).
          rewrite (map.putmany_assoc mc mg _).
          rewrite (map.putmany_comm mc mg) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc mg mc _).
          rewrite (map.putmany_assoc ma mg _).
          rewrite (map.putmany_comm ma mg) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc mg ma _).
          rewrite (map.putmany_assoc ma mc _).
          rewrite (map.putmany_comm ma mc) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc mc ma _). reflexivity.
        - apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; map_disjoint_auto]]. }
      split; [exact He' |].
      exists mg, (map.putmany mc (map.putmany ma mh)).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact Hg' |].
      exists mc, (map.putmany ma mh).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hc' |].
      exists ma, mh.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha' | exact Hh']. }

    (* Process postcondition of call 2 *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* Assemble QE results *)
    (* Hsep2: (out1' * (x1 * (x0 * (out0' * Rr)))) *)
    destruct Hsep2 as [m2a [m2b [[-> Hd2a] [Hout1 Hrest2a]]]].
    destruct Hrest2a as [m2c [m2d [[-> Hd2b] [Hx1_final Hrest2b]]]].
    destruct Hrest2b as [m2e [m2f [[-> Hd2c] [Hx0_final Hrest2c]]]].
    destruct Hrest2c as [m2g [m2h [[-> Hd2d] [Hout0 Hr'']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.
    pose proof (generic_FElem_length _ _ _ Hx0_final) as Hlenx0.
    pose proof (generic_FElem_length _ _ _ Hx1_final) as Hlenx1.

    exists (out0' ++ out1').
    split.
    { (* feval *)
      change (@AbstractField.feval _ QE_fp _ _ _ _ QE_repr (out0' ++ out1'))
        with (@AbstractField.feval _ base_fp _ _ _ _ base_repr (fst_e (out0' ++ out1')),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr (snd_e (out0' ++ out1'))).
      unfold fst_e, qe_fst_felem, snd_e, qe_snd_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite skipn_app_le by exact Hlen0.
      rewrite Hfeval0, Hfeval1. reflexivity. }
    split.
    { (* bounded_by *)
      split; unfold fst_e, snd_e, qe_fst_felem, qe_snd_felem;
        [rewrite firstn_app_le | rewrite skipn_app_le]; try exact Hlen0; assumption. }
    { (* sep: (QE_pout (out0'++out1') * (QE_px x * Rr)) *)
      (* Current mem: putmany m2a (putmany m2c (putmany m2e (putmany m2g m2h))) *)
      (* m2a=out1', m2c=x1, m2e=x0, m2g=out0', m2h=Rr *)
      exists (map.putmany m2g m2a), (map.putmany m2e (map.putmany m2c m2h)).
      split.
      { split.
        - (* Permute [m2a,m2c,m2e,m2g,m2h] -> [m2g,m2a,m2e,m2c,m2h] *)
          rewrite (map.putmany_assoc m2e m2g _).
          rewrite (map.putmany_comm m2e m2g) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m2g m2e _).
          rewrite (map.putmany_assoc m2c m2g _).
          rewrite (map.putmany_comm m2c m2g) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m2g m2c _).
          rewrite (map.putmany_assoc m2a m2g _).
          rewrite (map.putmany_comm m2a m2g) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m2g m2a _).
          rewrite (map.putmany_assoc m2c m2e _).
          rewrite (map.putmany_comm m2c m2e) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m2e m2c _).
          rewrite <- (map.putmany_assoc m2g m2a _). reflexivity.
        - apply map.disjoint_putmany_l; split;
            [apply map.disjoint_putmany_r; split; [map_disjoint_auto |
             apply map.disjoint_putmany_r; split; map_disjoint_auto] |
             apply map.disjoint_putmany_r; split; [map_disjoint_auto |
             apply map.disjoint_putmany_r; split; map_disjoint_auto]]. }
      split.
      { (* QE FElem for output *)
        apply (qe_raw_FElem_join nonresidue prefix eq_dec_base _ _ _ _ Hlen0 Hlen1).
        exists m2g, m2a.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hout0 | exact Hout1]. }
      { (* (QE_px x * Rr) — need to reconstruct x from fst_e x ++ snd_e x *)
        rewrite <- (@qe_list_decomp _ _ _ _ _ base_fp base_repr x).
        exists (map.putmany m2e m2c), m2h.
        split.
        { split.
          - rewrite (map.putmany_assoc m2e m2c m2h). reflexivity.
          - apply map.disjoint_putmany_l; split; map_disjoint_auto. }
        split.
        { apply (qe_raw_FElem_join nonresidue prefix eq_dec_base _ _ _ _ Hlenx0 Hlenx1).
          exists m2e, m2c.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hx0_final | exact Hx1_final]. }
        { exact Hr''. } } }
  Qed.

  (* ================================================================ *)
  (* QE_felem_copy_ok                                                  *)
  (* ================================================================ *)

  Lemma QE_felem_copy_ok :
    forall functions,
    map.get functions (felem_copy (F := QE)) =
      Some (snd (QE_felem_copy nonresidue prefix eq_dec_base)) ->
    (* Callee: base felem_copy *)
    (forall pout px out x R Rout tr m,
       (FElem_b px x * FElem_b pout out * R)%sep m /\
       (FElem_b pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (FElem_b pout x * Rout)%sep m')) ->
    (forall pout px out x R Rout tr m,
       (FElem_b px x * FElem_b pout out * R)%sep m /\
       (FElem_b pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (FElem_b pout x * Rout)%sep m')) ->
    forall pout px (out x : @felem _ QE_fp _ _ _ _ QE_repr) R Rout tr mem0,
    (@FElem _ QE_fp _ _ _ _ QE_repr px x *
     @FElem _ QE_fp _ _ _ _ QE_repr pout out * R)%sep mem0 /\
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rout)%sep mem0 ->
    WeakestPrecondition.call functions (felem_copy (F := QE)) tr mem0 [pout; px]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        (@FElem _ QE_fp _ _ _ _ QE_repr pout x * Rout)%sep mem').
  Proof.
  Admitted.

  (* ================================================================ *)
  (* QE_add_ok                                                         *)
  (* ================================================================ *)

  Lemma QE_add_ok :
    forall functions,
    map.get functions (add (F := QE)) =
      Some (snd (QE_add nonresidue prefix eq_dec_base)) ->
    (* Callee: base felem_copy (for stackalloc copies) *)
    (forall pout px out x R Rout tr m,
       (FElem_b px x * FElem_b pout out * R)%sep m /\
       (FElem_b pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (FElem_b pout x * Rout)%sep m')) ->
    (* Callee: QE felem_copy *)
    (forall pout px (out x : @felem _ QE_fp _ _ _ _ QE_repr) R Rout tr m,
       (@FElem _ QE_fp _ _ _ _ QE_repr px x *
        @FElem _ QE_fp _ _ _ _ QE_repr pout out * R)%sep m /\
       (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := QE)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (@FElem _ QE_fp _ _ _ _ QE_repr pout x * Rout)%sep m')) ->
    (* Callee: base add *)
    (forall pout px py out x y Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) x ->
       @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) y ->
       (exists Rx, (FElem_b px x * Rx)%sep m) ->
       (exists Ry, (FElem_b py y * Ry)%sep m) ->
       (FElem_b pout out * Rr)%sep m ->
       WeakestPrecondition.call functions (add (F := BaseField)) tr m [pout; px; py]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fadd _ base_fp (@feval _ base_fp _ _ _ _ base_repr x)
                                          (@feval _ base_fp _ _ _ _ base_repr y) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * Rr)%sep m')) ->
    forall pout px py (out x y : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) x ->
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) y ->
    (exists Rx, (@FElem _ QE_fp _ _ _ _ QE_repr px x * Rx)%sep mem0) ->
    (exists Ry, (@FElem _ QE_fp _ _ _ _ QE_repr py y * Ry)%sep mem0) ->
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (add (F := QE)) tr mem0 [pout; px; py]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' =
                       @Fadd _ QE_fp (@feval _ QE_fp _ _ _ _ QE_repr x)
                                     (@feval _ QE_fp _ _ _ _ QE_repr y) /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' * Rr)%sep mem').
  Proof.
  Admitted.

  (* ================================================================ *)
  (* QE_sub_ok                                                         *)
  (* ================================================================ *)

  Lemma QE_sub_ok :
    forall functions,
    map.get functions (sub (F := QE)) =
      Some (snd (QE_sub nonresidue prefix eq_dec_base)) ->
    (* Callee: base felem_copy *)
    (forall pout px out x R Rout tr m,
       (FElem_b px x * FElem_b pout out * R)%sep m /\
       (FElem_b pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (FElem_b pout x * Rout)%sep m')) ->
    (* Callee: QE felem_copy *)
    (forall pout px (out x : @felem _ QE_fp _ _ _ _ QE_repr) R Rout tr m,
       (@FElem _ QE_fp _ _ _ _ QE_repr px x *
        @FElem _ QE_fp _ _ _ _ QE_repr pout out * R)%sep m /\
       (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := QE)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (@FElem _ QE_fp _ _ _ _ QE_repr pout x * Rout)%sep m')) ->
    (* Callee: base sub *)
    (forall pout px py out x y Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) y ->
       (exists Rx, (FElem_b px x * Rx)%sep m) ->
       (exists Ry, (FElem_b py y * Ry)%sep m) ->
       (FElem_b pout out * Rr)%sep m ->
       WeakestPrecondition.call functions (sub (F := BaseField)) tr m [pout; px; py]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fsub _ base_fp (@feval _ base_fp _ _ _ _ base_repr x)
                                          (@feval _ base_fp _ _ _ _ base_repr y) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * Rr)%sep m')) ->
    forall pout px py (out x y : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@tight_bounds _ QE_fp _ _ _ _ QE_repr) x ->
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@tight_bounds _ QE_fp _ _ _ _ QE_repr) y ->
    (exists Rx, (@FElem _ QE_fp _ _ _ _ QE_repr px x * Rx)%sep mem0) ->
    (exists Ry, (@FElem _ QE_fp _ _ _ _ QE_repr py y * Ry)%sep mem0) ->
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (sub (F := QE)) tr mem0 [pout; px; py]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' =
                       @Fsub _ QE_fp (@feval _ QE_fp _ _ _ _ QE_repr x)
                                     (@feval _ QE_fp _ _ _ _ QE_repr y) /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' * Rr)%sep mem').
  Proof.
  Admitted.

End GenericQuadProofs.
