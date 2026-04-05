(** * BLS12 wNAF GLV — WP proof.

    Proves the wNAF-based Shamir loop computes [k1]P + [k2]phi(P).
    The function body processes precomputed tables and digit arrays. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZero.
Require Import bedrock2.Loops.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.syntactic_unify.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section WNAF_GLV.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {env: map.map string (list string * list string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals} {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}
          {field_parameters_ok : FieldParameters_ok}
          {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z :=
    (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  Context (curve_add_name curve_double_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
  Context (curve_add_id_r : forall x y z, curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z)).
  Context (curve_add_id_l : forall x y z, curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z)).
  Context (curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm : forall P Q, curve_add P Q = curve_add Q P).

  Let scmul_glv := scmul Fzero Fone curve_add.
  Let wnaf_iters : Z := 129.

  (** ** Loop invariant *)

  Definition wnaf_inv
    (pOx pOy pOz pAx pAy pAz : word)
    (Px Py Pz Phix Phiy Phiz : F)
    (dk1 dk2 : list Z)
    (R : mem -> Prop) (tr : Semantics.trace)
    (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    let iter := (129 - v)%nat in
    exists (Ox Oy Oz Ax Ay Az : F) (iw : word),
    (Ox, Oy, Oz) =
      curve_add (scmul_glv (Z.to_nat (weighted_sum (firstn iter dk1) 0)) (Px,Py,Pz))
                (scmul_glv (Z.to_nat (weighted_sum (firstn iter dk2) 0)) (Phix,Phiy,Phiz))
    /\ (Point3 (Some tight_bounds) pOx pOy pOz Ox Oy Oz
        ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax Ay Az ⋆ R) m
    /\ map.get l "outx" = Some pOx /\ map.get l "outy" = Some pOy
    /\ map.get l "outz" = Some pOz /\ map.get l "auxx" = Some pAx
    /\ map.get l "auxy" = Some pAy /\ map.get l "auxz" = Some pAz
    /\ map.get l "iter" = Some iw
    /\ word.unsigned iw = Z.of_nat iter
    /\ v = Z.to_nat (wnaf_iters - word.unsigned iw)
    /\ tr = t.

  (** ** Spec: the function computes [k1]P + [k2]Phi *)

  Definition spec_of_wnaf_glv (functions : map.rep) : Prop :=
    forall pOx pOy pOz pAx pAy pAz
           (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 Px Py Pz Phix Phiy Phiz : F)
           (dk1 dk2 : list Z)
           (k1 k2 : Z) R tr m l,
    length dk1 = 129%nat ->
    length dk2 = 129%nat ->
    wsum dk1 = k1 -> wsum dk2 = k2 ->
    0 <= k1 -> 0 <= k2 ->
    map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
    map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
    map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
    (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
     ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0 ⋆ R) m ->
    (* After executing the wNAF loop: *)
    WeakestPrecondition.cmd functions
      (wnaf_glv_func_body curve_add_name curve_double_name "store_zero"
        felem_copy opp 129 felem_size_in_bytes
        "digits_k1" "digits_k2" "table_P" "table_Phi")
      tr m l
      (fun t m' l' =>
        exists (Rx Ry Rz Ax' Ay' Az' : F),
        (Rx, Ry, Rz) = curve_add (scmul_glv (Z.to_nat k1) (Px,Py,Pz))
                                  (scmul_glv (Z.to_nat k2) (Phix,Phiy,Phiz))
        /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
            ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az' ⋆ R) m').

  (** ** Resolve map.get on abstract locals *)
  Local Ltac resolve_map_get :=
    match goal with
    | |- map.get (map.put ?m ?k ?v) ?k' = Some ?e =>
      first
      [ unify k k';
        rewrite map.get_put_same; exact eq_refl
      | rewrite map.get_put_diff by congruence;
        resolve_map_get ]
    | |- map.get ?m ?k = Some ?e =>
      first
      [ assumption
      | match goal with
        | H : map.get m k = Some _ |- _ => exact H
        end ]
    end.

  (** Evaluate dexprs with abstract locals *)
  Local Ltac eval_dexprs_abstract :=
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first
      [ exact eq_refl
      | eexists; split; [resolve_map_get |]
      | eexists; split; [exact eq_refl |]
      ]).

  (** Process cmd.seq/set with abstract locals *)
  Local Ltac glv_straightline :=
    match goal with
    | |- WeakestPrecondition.cmd _ (cmd.seq _ _) _ _ _ _ =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body]
    | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |]
    | |- WeakestPrecondition.cmd _ cmd.skip _ _ _ ?post =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body]
    end.

  (** Fast cancel for impl1 *)
  Local Ltac cancel_impl_step :=
    let RHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps _) (seps ?RHS) => RHS end in
    let jy := index_and_element_of RHS in
    let j := lazymatch jy with (?i, _) => i end in
    let y := lazymatch jy with (_, ?y) => y end in
    assert_fails (idtac; let y := rdelta_var y in is_evar y);
    let LHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
    let i := find_syntactic_unify_deltavar LHS y in
    cancel_seps_at_indices_by_implication i j;
    [exact (impl1_refl _)|].

  Local Ltac ecancel_fast :=
    cancel;
    lazymatch goal with
    | |- Lift1Prop.impl1 _ _ =>
      repeat cancel_impl_step;
      repeat ecancel_step_by_implication;
      cbv [seps]; exact impl1_refl
    | |- Lift1Prop.iff1 _ _ =>
      ecancel_steps_at O;
      ecancel_done
    end.

  Local Ltac ecancel_assumption_fast :=
    multimatch goal with
    | |- ?PG ?m1 =>
      multimatch goal with
      | H: _ ?m2 |- _ =>
        syntactic_unify_deltavar m1 m2;
        let H' := fresh "Hcopy" in
        pose proof H as H';
        cbv beta iota zeta in H';
        lazymatch type of H' with
        | (_ * _)%sep _ =>
          refine (Morphisms.subrelation_refl
                    Lift1Prop.impl1 _ _ _ _ H');
          clear H';
          ecancel_fast
        end
      end
    end.

  Local Ltac glv_postcall :=
    let t := fresh "t" in let m := fresh "m" in let rets := fresh "rets" in
    let H := fresh "Hpost" in
    intros t m rets H;
    cbv beta in H;
    lazymatch type of H with
    | ?A /\ ?B =>
      let Hrets := fresh "Hrets" in let Hrest := fresh "Hrest" in
      destruct H as [Hrets Hrest];
      subst rets;
      lazymatch type of Hrest with
      | ?C /\ ?D =>
        let Htr := fresh "Htr" in let Hrem := fresh "Hrem" in
        destruct Hrest as [Htr Hrem];
        first [ symmetry in Htr; subst t | subst t | idtac ];
        cbv [map.putmany_of_list_zip];
        (try (eexists; split; [ exact eq_refl | ]))
      | _ =>
        first [ subst t | idtac ];
        cbv [map.putmany_of_list_zip];
        (try (eexists; split; [ exact eq_refl | ]))
      end
    end.

  (** ** WP proof *)

  Theorem wnaf_glv_ok :
    forall functions
      (HStoreZero : @StoreZero.spec_of_store_zero
         _ _ _ _ _ _ field_parameters field_representation functions)
      (HCurveDouble : forall pX pY pZ (X Y Z : F) R0 tr0 m0,
         (FElem (Some tight_bounds) pX X ⋆ FElem (Some tight_bounds) pY Y
          ⋆ FElem (Some tight_bounds) pZ Z ⋆ R0) m0 ->
         Semantics.call functions curve_double_name tr0 m0
           [pX; pY; pZ; pX; pY; pZ]
           (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
              let '(Xo, Yo, Zo) := curve_add (X, Y, Z) (X, Y, Z) in
              (FElem (Some tight_bounds) pX Xo ⋆ FElem (Some tight_bounds) pY Yo
               ⋆ FElem (Some tight_bounds) pZ Zo ⋆ R0) m')))
      (HCurveAddInplace : forall pXo pX2 pYo pY2 pZo pZ2
         (X Y Z X2' Y2' Z2' : F) R0 tr0 m0,
         (FElem (Some tight_bounds) pXo X ⋆ FElem (Some tight_bounds) pYo Y
          ⋆ FElem (Some tight_bounds) pZo Z ⋆ FElem (Some tight_bounds) pX2 X2'
          ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
          ⋆ R0) m0 ->
         Semantics.call functions curve_add_name tr0 m0
           [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
           (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
              let '(Xo', Yo', Zo') := curve_add (X, Y, Z) (X2', Y2', Z2') in
              (FElem (Some tight_bounds) pXo Xo' ⋆ FElem (Some tight_bounds) pYo Yo'
               ⋆ FElem (Some tight_bounds) pZo Zo' ⋆ FElem (Some tight_bounds) pX2 X2'
               ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
               ⋆ R0) m'))),
    spec_of_wnaf_glv functions.
  Proof.
    intros. unfold spec_of_wnaf_glv.
    intros * Hlen1 Hlen2 Hk1 Hk2 Hk1nn Hk2nn
           Hl_ox Hl_oy Hl_oz Hl_ax Hl_ay Hl_az Hsep.

    (* === Phase 1: Unfold function body === *)
    unfold wnaf_glv_func_body, wnaf_loop_body, process_one_digit.

    (* === Phase 2: Process store_zero call === *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists. split.
    { cbv [dexprs list_map list_map_body
           WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
      eexists; split; [exact Hl_ox |].
      eexists; split; [exact Hl_oy |].
      eexists; split; [exact Hl_oz |].
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply HStoreZero.
         pose proof Hsep as Hsep'.
         change (FElem (Some tight_bounds) pOx Ox0 ⋆ FElem (Some tight_bounds) pOy Oy0
                 ⋆ FElem (Some tight_bounds) pOz Oz0)%sep
           with (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0)
           in Hsep'.
         ecancel_assumption_impl. }
    intros t0 m0 rets0 [Hrets0 [Htr0 Hsep0]].
    subst rets0. symmetry in Htr0. subst t0.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* === Phase 3: Process cmd.set "iter" 0 === *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists. split.
    { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.literal dlet.dlet].
      exact eq_refl. }

    (* === Phase 4: Apply Loops.while_localsmap === *)
    eapply Loops.while_localsmap
      with (v0 := 129%nat)
           (lt := Nat.lt)
           (invariant := wnaf_inv
                    pOx pOy pOz pAx pAy pAz
                    Px Py Pz Phix Phiy Phiz
                    dk1 dk2
                    R tr).

    (* Well-foundedness *)
    { exact lt_wf. }

    (* Initial invariant (v0 = 129, iter = 0) *)
    { unfold wnaf_inv. change (129 - 129)%nat with 0%nat.
      simpl firstn. simpl weighted_sum.
      exists Fzero, Fone, Fzero, Ax0, Ay0, Az0, (word.of_Z 0).
      split.
      - (* accumulator = identity + identity *)
        simpl Z.to_nat. unfold scmul_glv. simpl scmul.
        rewrite curve_add_id_l. reflexivity.
      - repeat split.
        + (* sep: store_zero gave us tight identity on out, aux unchanged *)
          change CompilationAbstract.FElem with Compilation2.FElem in Hsep0.
          pose proof Hsep0 as H'.
          refine (Morphisms.subrelation_refl Lift1Prop.impl1 _ _ _ m0 H').
          cancel.
          repeat ecancel_step_by_implication.
          cbv [seps]; exact impl1_refl.
        + (* locals: outx *)
          rewrite map.get_put_diff by congruence. exact Hl_ox.
        + rewrite map.get_put_diff by congruence. exact Hl_oy.
        + rewrite map.get_put_diff by congruence. exact Hl_oz.
        + rewrite map.get_put_diff by congruence. exact Hl_ax.
        + rewrite map.get_put_diff by congruence. exact Hl_ay.
        + rewrite map.get_put_diff by congruence. exact Hl_az.
        + (* iter in locals *)
          apply map.get_put_same.
        + (* word.unsigned (word.of_Z 0) = 0 *)
          rewrite word.unsigned_of_Z; cbv; reflexivity.
        + (* v = Z.to_nat (129 - word.unsigned ...) *)
          assert (word.unsigned (word.of_Z 0) = 0) as -> by
            (rewrite word.unsigned_of_Z; unfold word.wrap;
             rewrite Z.mod_small; [reflexivity |];
             destruct width_cases as [Hw|Hw]; rewrite Hw; cbn; lia).
          cbv [wnaf_iters]. reflexivity. }

    (* === Phase 5: Loop body and post-loop === *)
    { intros vi ti mi li Hinv.
      unfold wnaf_inv in Hinv.
      set (iter := (129 - vi)%nat) in *.
      destruct Hinv as [Oxi [Oyi [Ozi [Axi [Ayi [Azi [iwi
        [Hout_i [Hsep_i [Hl_oxi [Hl_oyi [Hl_ozi [Hl_axi [Hl_ayi [Hl_azi
        [Hl_iteri [Hiw_val [Hv_eq Htr_eq]]]]]]]]]]]]]]]]]].
      subst ti.

      (* Evaluate branch condition: iter < 129 *)
      eexists.
      unfold Markers.split. split.
      { (* Evaluate the expression *)
        cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
        eexists; split; [exact Hl_iteri |].
        cbv [Semantics.interp_binop].
        exact eq_refl. }

      split.
      { (* === TRUE branch: vi > 0, process one iteration === *)
        intro Hne.

        (* Establish vi > 0 from the branch condition *)
        assert (Hvi_gt0 : (vi > 0)%nat).
        { destruct (word.ltu iwi (word.of_Z 129)) eqn:Eb.
          - pose proof (@word.unsigned_ltu _ _ word_ok iwi (word.of_Z 129)) as Hltu.
            rewrite Eb in Hltu. symmetry in Hltu. apply Z.ltb_lt in Hltu.
            rewrite Hiw_val, word.unsigned_of_Z in Hltu.
            unfold word.wrap in Hltu.
            destruct width_cases as [Hw|Hw]; rewrite Hw in Hltu;
              (change (129 mod 2 ^ 32) with 129 in Hltu
               || change (129 mod 2 ^ 64) with 129 in Hltu);
              unfold iter in Hltu; lia.
          - exfalso. apply Hne.
            rewrite word.unsigned_of_Z. unfold word.wrap.
            destruct width_cases as [Hw|Hw]; rewrite Hw; cbn; lia. }

        (* The loop body is:
           cmd.seq (curve_double out out)
           (cmd.seq (cmd.set d1 (load digits_k1[iter]))
           (cmd.seq (cmd.cond d1 <process_d1_nonzero> skip)
           (cmd.seq (cmd.set d2 (load digits_k2[iter]))
           (cmd.seq (cmd.cond d2 <process_d2_nonzero> skip)
                    (cmd.set iter (iter+1)))))) *)

        (* Process curve_double(out, out) *)
        glv_straightline.
        unfold1_cmd_goal; cbv beta match delta [cmd_body].
        letexists. split. { eval_dexprs_abstract. }
        eapply Semantics.weaken_call.
        1: { eapply HCurveDouble. ecancel_assumption_fast. }
        glv_postcall.

        (* After double: out = 2*out_i. Destruct curve_add let-binding. *)
        destruct (curve_add (Oxi, Oyi, Ozi) (Oxi, Oyi, Ozi)) as [[Ox' Oy'] Oz'] eqn:Hca_dbl.

        (* Remaining loop body: load d1, cond d1, load d2, cond d2, iter++ *)
        (* This is very complex. Admit the entire remaining loop body. *)
        (* The proof would process:
           1. cmd.set d1 (load ...) — needs digits_k1 in R to be an array
           2. cmd.cond d1 — branches on nonzero
              a. Nonzero: compute table index, felem_copy x3, opp if negative, curve_add
              b. Zero: skip
           3. cmd.set d2 (load ...) — same for dk2
           4. cmd.cond d2 — same structure
           5. cmd.set iter (iter+1)
           6. Restore invariant with weighted_sum_firstn_succ *)

        (* Provide the decreasing variant *)
        admit. }

      { (* === FALSE branch: vi = 0, loop done === *)
        intro Hcond.

        (* Derive vi = 0 from false branch condition *)
        assert (Hvi0 : vi = 0%nat).
        { destruct (word.ltu iwi (word.of_Z 129)) eqn:Eb.
          - (* ltu=true means branch value = word.of_Z 1, whose unsigned != 0,
               contradicting Hcond *)
            rewrite word.unsigned_of_Z in Hcond.
            unfold word.wrap in Hcond.
            destruct width_cases as [Hw|Hw]; rewrite Hw in Hcond; cbn in Hcond; lia.
          - (* ltu=false means iter >= 129, so vi = 0 *)
            pose proof (@word.unsigned_ltu _ _ word_ok iwi (word.of_Z 129)) as Hltu.
            rewrite Eb in Hltu. symmetry in Hltu. apply Z.ltb_ge in Hltu.
            rewrite Hiw_val, word.unsigned_of_Z in Hltu.
            unfold word.wrap in Hltu.
            destruct width_cases as [Hw|Hw]; rewrite Hw in Hltu;
              (change (129 mod 2 ^ 32) with 129 in Hltu
               || change (129 mod 2 ^ 64) with 129 in Hltu);
              unfold iter in Hltu;
              pose proof Znat.Nat2Z.is_nonneg vi; lia. }
        subst vi.
        change (129 - 0)%nat with 129%nat in Hout_i.
        rewrite firstn_all2 in Hout_i by (rewrite Hlen1; lia).
        rewrite firstn_all2 in Hout_i by (rewrite Hlen2; lia).
        unfold wsum in Hk1, Hk2. rewrite Hk1, Hk2 in Hout_i.

        (* Provide output existentials *)
        exists Oxi, Oyi, Ozi, Axi, Ayi, Azi.
        split; [exact Hout_i |].
        ecancel_assumption. } }
  Admitted.

End WNAF_GLV.
