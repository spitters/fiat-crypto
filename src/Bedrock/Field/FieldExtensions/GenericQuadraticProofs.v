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

End GenericQuadProofs.
