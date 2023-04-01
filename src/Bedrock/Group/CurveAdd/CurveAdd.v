Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
(* Require Import Crypto.Bedrock.Specs.Field. *)
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Local Open Scope Z_scope.

Section Gallina.

Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
Context {F : Type} {field_parameters : Field.FieldParameters F}
        {field_parameters_ok : Field.FieldParameters_ok F}.
Context {field_representation : FieldRepresentation F}
        {field_representation_ok : FieldRepresentation_ok F}
        {three_b : felem}.

    Local Infix "+F" := Fadd (at level 100).
    Local Infix "-F" := Fsub (at level 100).
    Local Infix "*F" := Fmul (at level 90).
    Local Notation "x ^F2" := (Fmul x x) (at level 90).
    Check Fadd.

  Definition ladderstep_gallina
             (X1 X2 Y1 Y2 Z1 Z2 : F) : \<< F, F, F \>> :=
    let/n three_b := stack (feval (three_b)) in
    let/n t0 := stack (X1 *F X2) in
    let/n t1 := stack (Y1 *F Y2) in
    let/n t2 := stack (Z1 *F Z2) in
    let/n t3 := stack (X1 +F Y1) in
    let/n t4 := stack (X2 +F Y2) in
    let/n t3 := (t3 *F t4) in
    let/n t4 := (t0 +F t1) in
    let/n t3 := (t3 -F t4) in
    let/n t4 := (X1 +F Z1) in
    let/n t5 := stack (X2 +F Z2) in
    let/n t4 := (t4 *F t5) in
    let/n t5 := (t0 +F t2) in
    let/n t4 := (t4 -F t5) in
    let/n t5 := (Y1 +F Z1) in
    let/n Xout := (Y2 +F Z2) in
    let/n t5 := (t5 *F Xout) in
    let/n Xout:= (t1 +F t2) in
    let/n t5 := (t5 -F Xout) in
    let/n Zout := (three_b *F t2) in
    let/n Xout := (t1 -F Zout) in
    let/n Zout := (Zout +F t1) in
    let/n Yout := (Xout *F Zout) in
    let/n t1 := (t0 +F t0) in
    let/n t1 := (t1 +F t0) in
    let/n t4 := (three_b *F t4) in
    let/n t0 := (t1 *F t4) in
    let/n Yout := (Yout +F t0) in
    let/n t0 := (t5 *F t4) in
    let/n Xout := (t3 *F Xout) in
    let/n Xout := (Xout -F t0) in
    let/n t0 := (t3 *F t1) in
    let/n Zout := (t5 *F Zout) in
    let/n Zout := (Zout +F t0) in
    \<Xout, Yout, Zout\>.
End Gallina.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type} {field_parameters : Field.FieldParameters F}
          {field_parameters_ok : Field.FieldParameters_ok F}.
  Context {field_names : FieldNames F}.

  Context {field_representation : FieldRepresentation F}
          {field_representation_ok : FieldRepresentation_ok F}.

  Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context (Hbounds_eq : loose_bounds = tight_bounds).
  Context (three_b : felem).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Instance spec_of_ladderstep : spec_of "ladderstep" :=
    fnspec! "ladderstep"
          (pX1 pX2 pY1 pY2 pZ1 pZ2 pXout pYout pZout : word)
          / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pX1 X1
         * FElem (Some tight_bounds) pX2 X2
         * FElem (Some tight_bounds) pY1 Y1
         * FElem (Some tight_bounds) pY2 Y2
         * FElem (Some tight_bounds) pZ1 Z1
         * FElem (Some tight_bounds) pZ2 Z2
         * FElem (Some tight_bounds) pXout Xoutold
         * FElem (Some tight_bounds) pYout Youtold
         * FElem (Some tight_bounds) pZout Zoutold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Xout Yout Zout (* output values *)
                  : F ,
                  (@ladderstep_gallina _ _ _ _ _ _ _ three_b X1 X2 Y1 Y2 Z1 Z2
           = \<Xout, Yout, Zout\>)
          /\ (FElem (Some tight_bounds) pX1 X1
                * FElem (Some tight_bounds) pX2 X2
                * FElem (Some tight_bounds) pY1 Y1
                * FElem (Some tight_bounds) pY2 Y2
                * FElem (Some tight_bounds) pZ1 Z1
                * FElem (Some tight_bounds) pZ2 Z2
                * FElem (Some tight_bounds) pXout Xout
                * FElem (Some tight_bounds) pYout Yout
                * FElem (Some tight_bounds) pZout Zout * R)%sep mem'}.

  Lemma compile_ladderstep {tr m l functions}
        (x1 x2 y1 y2 z1 z2 xout1 yout1 zout1 : F) :
    let v := @ladderstep_gallina _ _ _ _ _ _ _ three_b x1 x2 y1 y2 z1 z2 in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           Rout
           X1_ptr X1_var X2_ptr X2_var Y1_ptr Y1_var Y2_ptr Y2_var
           Z1_ptr Z1_var Z2_ptr Z2_var Xout_ptr Xout_var Yout_ptr Yout_var Zout_ptr Zout_var,

      spec_of_ladderstep functions ->

      (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) X2_ptr x2 *
       FElem (Some tight_bounds) Y1_ptr y1 * FElem (Some tight_bounds) Y2_ptr y2 *
       FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) Z2_ptr z2 *
       FElem (Some tight_bounds) Xout_ptr xout1 * 
       FElem (Some tight_bounds) Yout_ptr yout1 * FElem (Some tight_bounds) Zout_ptr zout1 * Rout)%sep m ->

      map.get l X1_var = Some X1_ptr ->
      map.get l X2_var = Some X2_ptr ->
      map.get l Y1_var = Some Y1_ptr ->
      map.get l Y2_var = Some Y2_ptr ->
      map.get l Z1_var = Some Z1_ptr ->
      map.get l Z2_var = Some Z2_ptr ->
      map.get l Xout_var = Some Xout_ptr ->
      map.get l Yout_var = Some Yout_ptr ->
      map.get l Zout_var = Some Zout_ptr ->

      (let v := v in
       forall (* output values *) m',
       let '\<Xout', Yout', Zout'\> := @ladderstep_gallina _ _ _ _ _ _ _ three_b x1 x2 y1 y2 z1 z2 in
            (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) X2_ptr x2 *
            FElem (Some tight_bounds) Y1_ptr y1 * FElem (Some tight_bounds) Y2_ptr y2 *
            FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) Z2_ptr z2 *
            FElem (Some tight_bounds) Xout_ptr Xout' * 
            FElem (Some tight_bounds) Yout_ptr Yout' * FElem (Some tight_bounds) Zout_ptr Zout' * Rout)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->

      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq
        (cmd.call [] "ladderstep"
                  [ expr.var X1_var; expr.var X2_var;
                  expr.var Y1_var; expr.var Y2_var;
                  expr.var Z1_var; expr.var Z2_var;
                  expr.var Xout_var; expr.var Yout_var;
                  expr.var Zout_var])
        k_impl
      <{ pred (nlet_eq
                 [Xout_var; Yout_var; Zout_var]
                 v k) }>.
  Proof.
    repeat straightline'.
    handle_call.
    apply H10.
    rewrite H13.
    ecancel_assumption.
  Qed.

  Local Ltac ecancel_assumption ::=  repeat rewrite <- Hbounds_eq in *; ecancel_assumption_impl.

  (*Why must these instances be included?*)

  Instance spec_of_mul : spec_of mul.
  Proof.
    pose proof (binop_spec bin_mul). cbv [spec_of]. eapply X.
  Defined.

  (* Instance spec_of_square : spec_of (@square field_parameters).
  Proof.
    pose proof (unop_spec un_square). cbv [spec_of]. eapply X.
  Defined. *)

  Instance spec_of_add : spec_of add.
  Proof.
    pose proof (binop_spec bin_add). cbv [spec_of]. eapply X.
  Defined.

  Instance spec_of_sub : spec_of sub.
  Proof.
    pose proof (binop_spec bin_sub). cbv [spec_of]. eapply X.
  Defined.

  Instance spec_of_from_list : spec_of from_list.
  Proof.
    pose proof (spec_of_from_list (feval three_b)). exact X.
  Defined.

  (* Instance spec_of_scmula24 : spec_of (@scmula24 prime_field_parameters).
  Proof.
    pose proof (unop_spec un_scmula24). cbv [spec_of]. eapply X.
  Defined. *)

  Lemma relax_bounds_FElem_R : forall R x x_ptr, Lift1Prop.impl1 ((FElem (Some tight_bounds) x_ptr x * R)%sep) ((FElem (Some loose_bounds) x_ptr x * R)%sep).
  Proof.
    intros. cbv [Lift1Prop.impl1]. intros.
    destruct H, H, H, H0.
    eexists; eexists; split; [eapply H | ]. split; eauto. eapply relax_bounds_FElem. auto.
  Qed.

  Lemma relax_bounds_binop : forall R x x_ptr y y_ptr, Lift1Prop.impl1 ((FElem (Some tight_bounds) x_ptr x * FElem (Some tight_bounds) y_ptr y * R)%sep) ((FElem (Some loose_bounds) x_ptr x * FElem (Some loose_bounds) y_ptr y * R)%sep).
  Proof.
    intros. cbv [Lift1Prop.impl1]. intros. eapply sep_assoc. eapply relax_bounds_FElem_R.
    eapply sep_comm, sep_assoc. eapply relax_bounds_FElem_R. ecancel_assumption.
  Qed.

  (*tactics for applying field operations*)

  Ltac find_in_map :=
    repeat first [ erewrite map.get_put_diff; [| intros contra; discriminate] |
      eapply map.get_put_same].

  (* Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ ^ 2)%F _))) =>
    let Hsquare := (fresh "Hsquare") in pose proof compile_square as Hsquare;
    rewrite F.pow_2_r; cbv [ Field.prime_field_parameters] in Hsquare;
    eapply Hsquare; clear Hsquare; shelve : compiler.

    Local Hint Extern 6 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (a24 * _)%F _))) =>
    let Hscmul := (fresh "Hscmul") in epose proof compile_scmula24 as Hscmul;
    cbv [Compilation2.field_parameters Field.prime_field_parameters] in *;
    eapply Hscmul; clear Hscmul; shelve : compiler.

  Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ * _)%F _))) =>
    let Hmul := (fresh "Hmul") in pose proof compile_mul as Hmul;
    cbv [Compilation2.field_parameters Field.prime_field_parameters] in Hmul;
    eapply Hmul; [| | | try (eapply relax_bounds_binop; ecancel_assumption) | | |]; clear Hmul; shelve : compiler.

    Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ - _)%F _))) =>
    let Hsub := (fresh "Hsub") in epose proof compile_sub as Hsub;
    cbv [Compilation2.field_parameters Field.prime_field_parameters] in *;
    eapply Hsub; clear Hsub; shelve : compiler.

  Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ + _)%F _))) =>
    let Hadd := (fresh "Hadd") in epose proof compile_add as Hadd;
    cbv [Compilation2.field_parameters Field.prime_field_parameters] in *;
    eapply Hadd; clear Hadd; shelve : compiler.

  Local Hint Extern 9 ((FElem (Some loose_bounds) _ _ ⋆ FElem (Some loose_bounds) _ _ ⋆ _)%sep _) =>
    eapply relax_bounds_binop; ecancel_assumption : compiler.

  Local Hint Extern 9 =>
  simple eapply (@compile_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((@FElem width BW word mem prime_field_parameters field_representaton
    (@None (@bounds field_parameters width BW word mem field_representaton)))));
    [ecancel_assumption | shelve] : compiler. *)


  Lemma FElem_bounds_None : forall x x_ptr R, Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x * R)%sep (FElem None x_ptr x * R)%sep.
  Proof.
    intros. cbv [Lift1Prop.impl1]; intros m Hsep.
    destruct Hsep as [m1 [m2 [Hsep1 [Hsep2 Hsep3]]]].
    do 2 eexists. split; eauto. split; eauto.
    cbv [FElem Lift1Prop.ex1] in *. sepsimpl. simpl.
    exists x0. sepsimpl; auto.
  Qed.

  Local Hint Extern 9 ((FElem None _ _ ⋆ _ )%sep _) =>
  eapply FElem_bounds_None; ecancel_assumption : compiler_cleanup_post.

  Ltac clear_pred_seps' :=   
  unfold pred_sep;
  repeat change (fun x => ?h x) with h;
  repeat match goal with
         | [ H : _ ?m |- _ ?m] =>
           eapply Proper_sep_impl1;
           [ eapply P_to_bytes | clear H m; intros H m |
            try (eapply FElem_bounds_None; ecancel_assumption);
            try (eapply FElem_bounds_None; eapply relax_bounds_FElem_R; ecancel_assumption)]
         end.

  Hint Extern 1 (pred_sep _ _ _ _ _ _) =>
         clear_pred_seps'; shelve : compiler_cleanup_post.

  Hint Extern 1 (Some tight_bounds) =>
         rewrite <- Hbounds_eq : compiler.

  Derive ladderstep_body SuchThat
         (defn! "ladderstep" ("X1", "X2", "Y1", "Y2", "Z1", "Z2", "Xout", "Yout", "Zout")
              { ladderstep_body },
           implements @ladderstep_gallina _ _ _ _ _ _ _ three_b
                      using [mul; add; sub; from_list])
         As ladderstep_correct.
  Proof.
    assert (1 + 1 = 2) by lia. 
    compile_setup.
    compile_step.
    compile_step.

    epose proof compile_from_list.
    eapply H7.
    5: {
      ecancel_assumption.
    }
    4: {
       eapply map.get_put_same.
    }
    2: {
      repeat compile_step.
    }
    1: {
      (*What is this goal??*)
      compile_step. repeat compile_step.
    }
    1: auto.


    compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
  Qed.

End __.

Existing Instance spec_of_ladderstep.

Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (ladderstep_gallina _ _ _ _ _ _ _) _))) =>
       simple eapply compile_ladderstep; shelve : compiler.

Import Syntax.
Local Unset Printing Coercions.
Local Set Printing Depth 70.
(* Set the printing width so that arguments are printed on 1 line.
   Otherwise the build breaks.
*)
Local Set Printing Width 140.
Redirect "Crypto.Bedrock.Group.ScalarMult.LadderStep.ladderstep_body" Print ladderstep_body.
