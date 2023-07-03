Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.

Import Syntax BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type} {field_parameters : FieldParameters F}
          {field_parameters_ok : Field.FieldParameters_ok F}.
  Context {field_names : FieldNames F}.
  Context {field_representation : FieldRepresentation F}
    {field_representation_ok : FieldRepresentation_ok F}
    {group_cmov : string}.

  Notation F_cmov := select_znz.

  Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

  Instance spec_of_group_cmov : spec_of group_cmov :=
    fnspec! group_cmov
      (pXout pYout pZout pX1 pY1 pZ1 pX2 pY2 pZ2 pc : word)
      / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) c R,
      { requires tr mem :=
          (FElem (Some tight_bounds) pX1 X1
           * FElem (Some tight_bounds) pX2 X2
           * FElem (Some tight_bounds) pY1 Y1
           * FElem (Some tight_bounds) pY2 Y2
           * FElem (Some tight_bounds) pZ1 Z1
           * FElem (Some tight_bounds) pZ2 Z2
           * FElem (Some tight_bounds) pXout Xoutold
           * FElem (Some tight_bounds) pYout Youtold
           * FElem (Some tight_bounds) pZout Zoutold
           * scalar pc c
           * R)%sep mem /\
            ZRange.is_bounded_by_bool (word.unsigned c) bit_range = true;
        ensures tr' mem' :=
          exists Xout Yout Zout (* output values *)
            : F , exists cout,
            (
              (if ((word.unsigned c) =? 1)
               then (Xout = X2)
               else (Xout = X1))
              /\
                (if ((word.unsigned c) =? 1)
                 then (Yout = Y2)
                 else (Yout = Y1))
              /\
                (if ((word.unsigned c) =? 1)
                 then (Zout = Z2)
                 else (Zout = Z1))
            )
            /\ (FElem (Some tight_bounds) pX1 X1
               * FElem (Some tight_bounds) pX2 X2
               * FElem (Some tight_bounds) pY1 Y1
               * FElem (Some tight_bounds) pY2 Y2
               * FElem (Some tight_bounds) pZ1 Z1
               * FElem (Some tight_bounds) pZ2 Z2
               * FElem (Some tight_bounds) pXout Xout
               * FElem (Some tight_bounds) pYout Yout
               * FElem (Some tight_bounds) pZout Zout
               * scalar pc cout
               * R)%sep mem'}.


  Definition cmov_func : bedrock2.Syntax.func :=
    (group_cmov, (["outx"; "outy"; "outz"; "x1"; "y1"; "z1"; "x2"; "y2"; "z2"; "pc"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (F_cmov) [expr.var ("outx"); expr.load access_size.word (expr.var ("pc")); expr.var ("x1"); expr.var("x2")]);
      coq:(cmd.call [] (F_cmov) [expr.var ("outy"); expr.load access_size.word (expr.var ("pc")); expr.var ("y1"); expr.var("y2")]);
      coq:(cmd.call [] (F_cmov) [expr.var ("outz"); expr.load access_size.word (expr.var ("pc")); expr.var ("z1"); expr.var("z2")])))).

  (* From bedrock2 Require Import ToCString Bytedump. *)
  (* Definition c_mod := (c_module (cmov_func :: nil)). *)
  (* Eval native_compute in c_mod. *)

  Ltac solve_locals l1 := subst l1; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

  Local Instance spec_of_select_znz : spec_of select_znz := spec_of_selectznz.

  (* TODO: Move? *)
  Lemma bignum_1_scalar pc c :
    forall m R, (@Bignum.Bignum width word mem 1 pc [c] ⋆ R) m <-> (scalar pc c ⋆ R) m.
  intros. apply Util.iff1_sep_cancel_both.
    unfold Bignum.Bignum. simpl. split.
    - rewrite sep_emp_l, sep_emp_r. easy.
    - rewrite sep_emp_l, sep_emp_r. easy.
    - easy.
  Qed.

  Lemma cmov_ok : program_logic_goal_for_function! cmov_func.
  Proof.
    cbv [cmov_func]. cbv [program_logic_goal_for].
    cbv [spec_of_group_cmov].
    repeat straightline.
    unfold1_call_goal.
    cbv match beta delta [call_body].
    assert ((group_cmov =? group_cmov)%string = true).
    { eapply eqb_eq. auto. }
    rewrite H4.
    cbv match beta delta [func].
    repeat straightline.

    eexists; split.
    1: {
      repeat straightline. eexists; split.
      - solve_locals l.
      - repeat straightline. eexists; split; [solve_locals l| ].
        repeat straightline. eexists. split; [solve_locals l| ].
        repeat straightline. eexists; split; [solve_locals l| ].
        repeat straightline.
    }
    straightline_call.
    split.
    ecancel_assumption_impl.
    split.
    ecancel_assumption_impl.
    split.
    ecancel_assumption_impl.
    eassumption.

    repeat straightline.
    eexists; split.
    1: {
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split.
      { destruct (word.unsigned c =? 1).
        - eapply load_word_of_sep.
          ecancel_assumption.
        - eapply load_word_of_sep.
          ecancel_assumption. }
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline.
      }

    destruct (word.unsigned c =? 1) eqn:eq.
    {
      straightline_call.
      split.
      ecancel_assumption_impl.
      split.
      ecancel_assumption_impl.
      split.
      ecancel_assumption_impl.
      eassumption.
      rewrite eq in *.

      eexists; split.
      repeat straightline. eexists.
      repeat straightline. eexists. split.
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline.

      straightline_call.
      split.
      ecancel_assumption_impl.
      split.
      ecancel_assumption_impl.
      split.
      ecancel_assumption_impl.
      eassumption.
      rewrite eq in *.

      eexists; split.
      repeat straightline. eexists.
      repeat straightline. split; auto.
      do 4 eexists. split.
      eauto.
      ecancel_assumption. }
    {
      straightline_call.
      split.
      ecancel_assumption_impl.
      split.
      ecancel_assumption_impl.
      split.
      ecancel_assumption_impl.
      eassumption.
      rewrite eq in *.

      eexists; split.
      repeat straightline. eexists.
      repeat straightline. eexists. split.
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline.

      straightline_call.
      split.
      ecancel_assumption_impl.
      split.
      ecancel_assumption.
      split.
      ecancel_assumption.
      eassumption.
      rewrite eq in *.

      eexists; split.
      repeat straightline. eexists.
      repeat straightline. split; auto.
      do 4 eexists. split.
      eauto.
      ecancel_assumption. }
  Qed.

End __.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type} {field_parameters : FieldParameters F}
          {field_parameters_ok : Field.FieldParameters_ok F}.
  Context {field_names : FieldNames F}.
  Context {field_representation : FieldRepresentation F}
    {field_representation_ok : FieldRepresentation_ok F}
    {group_cmov_alt : string}.

  Notation F_cmov := select_znz.

  Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

  Instance spec_of_group_cmov_alt : spec_of group_cmov_alt :=
    fnspec! group_cmov_alt
      (pXout pYout pZout pX1 pY1 pZ1 pX2 pY2 pZ2 pc : word)
      / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) c R1 R2 Rc Rout,
      { requires tr mem :=
          (FElem (Some tight_bounds) pX1 X1
           ⋆ FElem (Some tight_bounds) pY1 Y1
           ⋆ FElem (Some tight_bounds) pZ1 Z1
           ⋆ R1) mem
           /\ (FElem (Some tight_bounds) pX2 X2
              ⋆ FElem (Some tight_bounds) pY2 Y2
              ⋆ FElem (Some tight_bounds) pZ2 Z2
              ⋆ R2) mem
           /\ (FElem (Some tight_bounds) pXout Xoutold
              ⋆ FElem (Some tight_bounds) pYout Youtold
              ⋆ FElem (Some tight_bounds) pZout Zoutold
              ⋆ Rout) mem
          /\ (scalar pc c ⋆ Rc) mem
          /\ ZRange.is_bounded_by_bool (word.unsigned c) bit_range = true;
        ensures tr' mem' :=
          tr = tr' /\
          exists Xout Yout Zout (* output values *),
            ((if ((word.unsigned c) =? 1)
               then (Xout = X2)
               else (Xout = X1))
              /\ (if ((word.unsigned c) =? 1)
                 then (Yout = Y2)
                 else (Yout = Y1))
              /\ (if ((word.unsigned c) =? 1)
                 then (Zout = Z2)
                 else (Zout = Z1)))
            /\ (FElem (Some tight_bounds) pXout Xout
               * FElem (Some tight_bounds) pYout Yout
               * FElem (Some tight_bounds) pZout Zout
               * Rout)%sep mem'}.

  Definition cmov_alt_func : bedrock2.Syntax.func :=
    (group_cmov_alt, (["outx"; "outy"; "outz"; "x1"; "y1"; "z1"; "x2"; "y2"; "z2"; "pc"], []:list String.string, bedrock_func_body:(
      stackalloc felem_size_in_bytes as auxx;
      stackalloc felem_size_in_bytes as auxy;
      stackalloc felem_size_in_bytes as auxz;
      coq:(cmd.call [] (F_cmov) [expr.var ("auxx"); expr.load access_size.word (expr.var ("pc")); expr.var ("x1"); expr.var("x2")]);
      coq:(cmd.call [] (F_cmov) [expr.var ("auxy"); expr.load access_size.word (expr.var ("pc")); expr.var ("y1"); expr.var("y2")]);
      coq:(cmd.call [] (F_cmov) [expr.var ("auxz"); expr.load access_size.word (expr.var ("pc")); expr.var ("z1"); expr.var("z2")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("outx"); expr.var ("auxx")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("outy"); expr.var ("auxy")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("outz"); expr.var ("auxz")])))).

  (* From bedrock2 Require Import ToCString Bytedump. *)
  (* Definition c_mod := (c_module (cmov_func :: nil)). *)
  (* Eval native_compute in c_mod. *)

  Ltac solve_locals l1 := subst l1; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

  Local Instance spec_of_select_znz' : spec_of select_znz := spec_of_selectznz.
  Local Instance spec_of_felem_copy : spec_of felem_copy := spec_of_felem_copy.

   Ltac collect4 H1 H2 H3 H4 := let Hnew := (fresh "Hnew") in
                            eassert (Hnew : id (fun m => (_ m) /\ (_ m) /\ (_ m) /\ (_ m)) _) by (cbv [id]; repeat split; [eapply H1| eapply H2|eapply H3|eapply H4]); clear H1 H2 H3 H4.

   Ltac update_mem :=
     match goal with
     | Hsplit : map.split ?comb ?mem ?stack |- _ =>
         match goal with
           Hold_mem : ?p mem,
             Hstack : Memory.anybytes ?a felem_size_in_bytes stack
           |- _ =>
             let x := fresh "x" in
             let Hmem := fresh "Hmem" in
             eapply FElem_from_bytes in Hstack as [x Hstack]
             ; eassert (Hnew_mem : (p ⋆ FElem None a x) comb) by (eexists; eauto)
             ; clear dependent mem
             ; clear dependent stack
             ; rename Hnew_mem into Hmem
         end
     end.

  Ltac straightline' :=
    match goal with
    | _ => update_mem
    | _ => straightline
    | l := _ : map.rep |- _ => subst l
    | l := _ : list word.rep |- _ => subst l
    | |- Some _ = Some _ => try reflexivity
    | |- exists _, _ => eexists
    | |- _ /\ _ => split
    | |- felem_size_in_bytes mod _ = 0 => eapply felem_size_in_bytes_mod
    | |- map.get _ _ = _ => repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same
    end.

  Ltac sep_and_fwd :=
    cbn [id] in *;
    match goal with
    | H : context[fun m => _] |- _ =>
        let Hnew1 := fresh "Hmem" in
        let Hnew2 := fresh "Hmem" in
        eassert (Hnew1 : ((fun m => _) ⋆ _) _) by ecancel_assumption;
        eapply sep_and_l_fwd in Hnew1 as [Hnew1 Hnew2];
        clear H
    end.

  Lemma cmov_alt_ok : program_logic_goal_for_function! cmov_alt_func.
  Proof.
    cbv [cmov_alt_func]. cbv [program_logic_goal_for].
    cbv [spec_of_group_cmov_alt].
    repeat straightline.
    unfold1_call_goal.
    cbv match beta delta [call_body].
    rewrite String.eqb_refl.
    cbv match beta delta [func].
    collect4 H5 H6 H7 H8.
    repeat straightline'.

    1: {
      eapply load_word_of_sep.
      repeat sep_and_fwd.
      ecancel_assumption.
      }

    (* eexists; split. *)
    (* 1: { *)
    (*   repeat straightline. eexists; split. *)
    (*   - solve_locals l. *)
    (*   - repeat straightline. eexists; split; [solve_locals l| ]. *)
    (*     repeat straightline. eexists. split; [solve_locals l| ]. *)
    (*     repeat straightline. eexists; split; [solve_locals l| ]. *)
    (*     repeat straightline. *)
    (* } *)
      straightline_call.
      sepsimpl.
    ecancel_assumption_impl.
      repeat sep_and_fwd.
    ecancel_assumption_impl.
      repeat sep_and_fwd.
    ecancel_assumption_impl.
    eassumption.
    clear dependent mCombined.
    destruct (word.unsigned c =? 1) eqn:eq.

    {
      repeat straightline'.
      eapply load_word_of_sep.
      repeat sep_and_fwd.
      ecancel_assumption.

      (* eexists; split. *)
      (* 1: { *)
      (*   repeat straightline. eexists. split; [solve_locals l| ]. *)
      (*   repeat straightline. eexists. split; [solve_locals l| ]. *)
      (*   repeat straightline. eexists. split. *)
      (*   { destruct (word.unsigned c =? 1). *)
      (*     - eapply load_word_of_sep. *)
      (*       ecancel_assumption. *)
      (*     - eapply load_word_of_sep. *)
      (*       ecancel_assumption. } *)
      (*   repeat straightline. eexists. split; [solve_locals l| ]. *)
      (*   repeat straightline. eexists. split; [solve_locals l| ]. *)
      (*   repeat straightline. *)
      (*   } *)

      straightline_call.
      sepsimpl.
      ecancel_assumption_impl.
      repeat sep_and_fwd.
      ecancel_assumption_impl.
      repeat sep_and_fwd.
      ecancel_assumption_impl.
      eassumption.
      clear dependent a3.
      rewrite eq in *.

      repeat straightline'.

      eapply load_word_of_sep.
      repeat sep_and_fwd.
      ecancel_assumption.

      straightline_call.
      sepsimpl.
      ecancel_assumption_impl.
      repeat sep_and_fwd.
      ecancel_assumption_impl.
      repeat sep_and_fwd.
      ecancel_assumption_impl.
      eassumption.
      clear dependent a5.
      rewrite eq in *.

      repeat straightline'.

      straightline_call.
      repeat sep_and_fwd.
      sepsimpl.
      ecancel_assumption_impl.
      ecancel_assumption_impl.
      clear dependent a3.

      repeat straightline'.

      straightline_call.
      repeat sep_and_fwd.
      sepsimpl.
      ecancel_assumption_impl.
      ecancel_assumption_impl.
      clear dependent a5.

      repeat straightline'.

      straightline_call.
      repeat sep_and_fwd.
      sepsimpl.
      ecancel_assumption_impl.
      ecancel_assumption_impl.
      clear dependent a3.

      repeat straightline.

      eassert (h1 : (FElem _ a1 _ * _)%sep a5).
      {
        ecancel_assumption.
      }
      destruct h1 as [mq [mr [h1 [h2 h3]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      eassert (h4 : (FElem _ a0 _  * _)%sep mr).
      {
        ecancel_assumption.
      }
      (* clear H18. *)

      destruct h4 as [mq' [mr' [h4 [h5 h6]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      eassert (h7 : (FElem _ a _  * _)%sep mr').
      {
        ecancel_assumption.
      }
      (* clear H18. *)

      destruct h7 as [mq'' [mr'' [h7 [h8 h9]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      repeat straightline.
      split; auto.
      split; auto.

      eexists. eexists. eexists.
      split.
      2: ecancel_assumption.
      auto.
    }
    (* HACK: this is duplicated from the previous case, generalize somehow *)
    {
      repeat straightline'.
      eapply load_word_of_sep.
      repeat sep_and_fwd.
      ecancel_assumption.

      straightline_call.
      sepsimpl.
      ecancel_assumption_impl.
      repeat sep_and_fwd.
      ecancel_assumption_impl.
      repeat sep_and_fwd.
      ecancel_assumption_impl.
      eassumption.
      clear dependent a3.
      rewrite eq in *.

      repeat straightline'.

      eapply load_word_of_sep.
      repeat sep_and_fwd.
      ecancel_assumption.

      straightline_call.
      sepsimpl.
      ecancel_assumption_impl.
      repeat sep_and_fwd.
      ecancel_assumption_impl.
      repeat sep_and_fwd.
      ecancel_assumption_impl.
      eassumption.
      clear dependent a5.
      rewrite eq in *.

      repeat straightline'.

      straightline_call.
      repeat sep_and_fwd.
      sepsimpl.
      ecancel_assumption_impl.
      ecancel_assumption_impl.
      clear dependent a3.

      repeat straightline'.

      straightline_call.
      repeat sep_and_fwd.
      sepsimpl.
      ecancel_assumption_impl.
      ecancel_assumption_impl.
      clear dependent a5.

      repeat straightline'.

      straightline_call.
      repeat sep_and_fwd.
      sepsimpl.
      ecancel_assumption_impl.
      ecancel_assumption_impl.
      clear dependent a3.

      repeat straightline.

      eassert (h1 : (FElem _ a1 _ * _)%sep a5).
      {
        ecancel_assumption.
      }
      destruct h1 as [mq [mr [h1 [h2 h3]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      eassert (h4 : (FElem _ a0 _  * _)%sep mr).
      {
        ecancel_assumption.
      }
      (* clear H18. *)

      destruct h4 as [mq' [mr' [h4 [h5 h6]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      eassert (h7 : (FElem _ a _  * _)%sep mr').
      {
        ecancel_assumption.
      }
      (* clear H18. *)

      destruct h7 as [mq'' [mr'' [h7 [h8 h9]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      repeat straightline.
      split; auto.
      split; auto.

      eexists. eexists. eexists.
      split.
      2: ecancel_assumption.
      auto.
    }
  Qed.

End __.
Existing Instance spec_of_group_cmov.
Existing Instance spec_of_group_cmov_alt.
