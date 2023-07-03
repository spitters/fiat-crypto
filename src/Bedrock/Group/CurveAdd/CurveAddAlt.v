Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZeroGSpec.
Require Import Crypto.Bedrock.Specs.Field.
(* Require Import Crypto.Bedrock.Specs.Field. *)
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAdd.
Require Import Crypto.Bedrock.Group.CurveAdd.BignumShift.
Require Import Crypto.Bedrock.Group.CurveAdd.CondMoveGroup.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Local Open Scope Z_scope.

(* redefining ltac *)
(* Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax. *)
(* From coqutil.Tactics Require Import letexists eabstract rdelta ident_of_string. *)
(* Require Import bedrock2.WeakestPrecondition. *)
(* Require Import bedrock2.WeakestPreconditionProperties. *)
(* Require Import bedrock2.Loops. *)
(* Require Import bedrock2.Map.SeparationLogic bedrock2.Scalars. *)
(* Import WeakestPrecondition. *)
(* Import coqutil.Map.Interface. *)
(* Ltac straightline_stackalloc ::= *)
(*   match goal with Hanybytes: Memory.anybytes ?a ?n ?mStack |- _ => *)
(*                     let m := match goal with H : map.split ?mCobined ?m mStack |- _ => m end in *)
(*                     let mCombined := match goal with H : map.split ?mCobined ?m mStack |- _ => mCobined end in *)
(*                     let Hsplit := match goal with H : map.split ?mCobined ?m mStack |- _ => H end in *)
(*                     let Hm := multimatch goal with H : _ m |- _ => H end in *)
(*                     let Hm' := fresh Hm in *)
(*                     let Htmp := fresh in *)
(*                     let Pm := match type of Hm with ?P m => P end in *)
(*                     assert_fails (idtac; match goal with Halready : (Separation.sep Pm (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a _) mCombined) |- _ => idtac end); *)
(*                     rename Hm into Hm'; *)
(*                     let stack := fresh "stack" in *)
(*                     let stack_length := fresh "length_" stack in (* MUST remain in context for deallocation *) *)
(*                     destruct (Array.anybytes_to_array_1 mStack a n Hanybytes) as (stack&Htmp&stack_length); *)
(*                     epose proof (ex_intro _ m (ex_intro _ mStack (conj Hsplit (conj Hm' Htmp))) *)
(*                         : Separation.sep _ (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a _) mCombined) as Hm; *)
(*                     clear Htmp; (* note: we could clear more here if we assumed only one separation-logic description of each memory is present *) *)
(*                     try (let m' := fresh m in rename m into m'); rename mCombined into m; *)
(*                     ( assert (BinInt.Z.of_nat (Datatypes.length stack) = n) *)
(*                       by (rewrite stack_length; eauto with stack_hdb) *)
(*                          || fail 2 "negative stackalloc of size" n ) *)
(*   end. *)
(* (* end redefining ltac *) *)

Lemma felem_size_in_bytes_pos
  {F : Type}
  {width: Z}
  {BW: Bitwidth width}
  {word: word.word width}
  {mem: map.map word Byte.byte}
  {word_ok : word.ok word} {mem_ok : map.ok mem}
  {field_parameters : FieldParameters F}
  {field_representation : FieldRepresentation F} :
  0 <= felem_size_in_bytes.
Proof.
  unfold felem_size_in_bytes.
  pose proof bytes_per_word_range.
  nia.
Qed.

(* Lemma FElem_equiv *)
(*   {F : Type} *)
(*   {width: Z} *)
(*   {BW: Bitwidth width} *)
(*   {word: word.word width} *)
(*   {mem: map.map word Byte.byte} *)
(*   {word_ok : word.ok word} {mem_ok : map.ok mem} *)
(*   {field_parameters : FieldParameters F} *)
(*   {field_representation : FieldRepresentation F} *)
(*   m p x *)
(*   : FElem (Some tight_bounds) p x m <-> (exists f, Field.FElem p f m /\ bounded_by tight_bounds f /\ feval f = x). *)
(* Proof. *)
(*   intros; split. *)
(*   - intros [f]. *)
(*     rewrite sep_emp_l in H. *)
(*     exists f. intuition subst. *)
(*   - intros [f]. *)
(*     exists f. *)
(*     rewrite sep_emp_l. *)
(*     intuition subst. *)
(* Qed. *)

Hint Resolve felem_size_in_bytes_pos : stack_hdb.

Ltac straightline_stackalloc ::=
  match goal with Hanybytes: Memory.anybytes ?a ?n ?mStack |- _ =>
  let m := match goal with H : map.split ?mCobined ?m mStack |- _ => m end in
  let mCombined := match goal with H : map.split ?mCobined ?m mStack |- _ => mCobined end in
  let Hsplit := match goal with H : map.split ?mCobined ?m mStack |- _ => H end in
  let Hm := multimatch goal with H : _ m |- _ => H end in
  let Hm' := fresh Hm in
  let Htmp := fresh in
  let Pm := match type of Hm with ?P m => P end in
  assert_fails (idtac; match goal with Halready : (Separation.sep Pm (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a _) mCombined) |- _ => idtac end);
  rename Hm into Hm';
  let stack := fresh "stack" in
  let stack_length := fresh "length_" stack in (* MUST remain in context for deallocation *)
  destruct (Array.anybytes_to_array_1 mStack a n Hanybytes) as (stack&Htmp&stack_length);
  epose proof (ex_intro _ m (ex_intro _ mStack (conj Hsplit (conj Hm' Htmp)))
  : Separation.sep _ (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a _) mCombined) as Hm;
  clear Htmp; (* note: we could clear more here if we assumed only one separation-logic description of each memory is present *)
  try (let m' := fresh m in rename m into m'); rename mCombined into m;
  assert (BinInt.Z.of_nat (Datatypes.length stack) = n)
  by (rewrite stack_length, Z2Nat.id; eauto with stack_hdb
  || fail 2 "negative stackalloc of size" n )
  end.

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
          {field_representation_ok : FieldRepresentation_ok F}
          {curve_add_alt : string}.

  Hint Resolve relax_bounds : compiler.
  (* Instance my_field_representation : FieldRepresentation F. *)
  (* Proof. *)
  (*     exact field_representation. *)
  (* Defined. *)

  Context (three_b : felem).


  Instance spec_of_felem_copy : spec_of "felem_copy" := spec_of_felem_copy.
  (* Proof. *)
  (*    pose proof spec_of_felem_copy. eapply X. *)
  (*  Defined. *)

   Instance spec_of_curve_add : spec_of "curve_add" := spec_of_ladderstep three_b.
   (* Proof. *)
   (*    pose proof spec_of_ladderstep. specialize (X three_b). exact X. *)
   (* Defined. *)

  Instance spec_of_curve_add_alt : spec_of curve_add_alt :=
  fnspec! curve_add_alt
        (pX1 pX2 pY1 pY2 pZ1 pZ2 pXout pYout pZout : word)
        / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) R1 R2 Rout,
  { requires tr mem :=
      (FElem (Some tight_bounds) pX1 X1
       * FElem (Some tight_bounds) pY1 Y1
       * FElem (Some tight_bounds) pZ1 Z1
       * R1)%sep mem /\
      (FElem (Some tight_bounds) pX2 X2
       * FElem (Some tight_bounds) pY2 Y2
       * FElem (Some tight_bounds) pZ2 Z2
       * R2)%sep mem /\
       (FElem (Some tight_bounds) pXout Xoutold
       * FElem (Some tight_bounds) pYout Youtold
       * FElem (Some tight_bounds) pZout Zoutold * Rout)%sep mem;
    ensures tr' mem' :=
      tr = tr' /\
         exists Xout Yout Zout (* output values *)
                : F ,
                (@ladderstep_gallina _ _ _ _ _ _ _ three_b X1 X2 Y1 Y2 Z1 Z2
         = \<Xout, Yout, Zout\>)
        /\
          (* (FElem (Some tight_bounds) pX1 X1 *)
          (*       * FElem (Some tight_bounds) pX2 X2 *)
          (*       * FElem (Some tight_bounds) pY1 Y1 *)
          (*       * FElem (Some tight_bounds) pY2 Y2 *)
          (*       * FElem (Some tight_bounds) pZ1 Z1 *)
          (*       * FElem (Some tight_bounds) pZ2 Z2 *)
        (* (FElem (Some tight_bounds) pX1 X1
              * FElem (Some tight_bounds) pY1 Y1
              * FElem (Some tight_bounds) pZ1 Z1 * R1)%sep mem' /\
           (FElem (Some tight_bounds) pX2 X2
              * FElem (Some tight_bounds) pY2 Y2
              * FElem (Some tight_bounds) pZ2 Z2 * R2)%sep mem' /\ *)
              (FElem (Some tight_bounds) pXout Xout
              * FElem (Some tight_bounds) pYout Yout
              * FElem (Some tight_bounds) pZout Zout * Rout)%sep mem'}.

   Require Import bedrock2.NotationsCustomEntry.
   Require Import bedrock2.WeakestPrecondition.
   Import Syntax BinInt String List.ListNotations.
   Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.


   Definition curve_add_alt_func : bedrock2.Syntax.func :=
   (curve_add_alt, (["px1"; "px2"; "py1"; "py2"; "pz1"; "pz2"; "outx"; "outy"; "outz"], []:list String.string, bedrock_func_body:(
      stackalloc felem_size_in_bytes as px1a;
      stackalloc felem_size_in_bytes as py1a;
      stackalloc felem_size_in_bytes as pz1a;
      stackalloc felem_size_in_bytes as px2a;
      stackalloc felem_size_in_bytes as py2a;
      stackalloc felem_size_in_bytes as pz2a;
      coq:(cmd.call [] (felem_copy) [expr.var ("px1a"); expr.var ("px1")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("px2a"); expr.var ("px2")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("py1a"); expr.var ("py1")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("py2a"); expr.var ("py2")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("pz1a"); expr.var ("pz1")]);
      coq:(cmd.call [] (felem_copy) [expr.var ("pz2a"); expr.var ("pz2")]);
      coq:(cmd.call [] ("curve_add") [expr.var ("px1a"); expr.var ("px2a"); expr.var ("py1a"); expr.var ("py2a"); expr.var ("pz1a"); expr.var ("pz2a"); expr.var ("outx"); expr.var ("outy"); expr.var ("outz")])
   ))).

    (* From bedrock2 Require Import ToCString Bytedump. *)
    (* Definition c_mod := (c_module (curve_add_alt_func :: nil)). *)
    (* Eval native_compute in c_mod. *)

   Opaque felem_size_in_bytes.
    (* Print c_mod. *)

   Ltac collect H1 H2 H3 := let Hnew := (fresh "Hnew") in
                            eassert (Hnew : id (fun m => (_ m) /\ (_ m) /\ (_ m)) _) by (cbv [id]; repeat split; [eapply H1| eapply H2|eapply H3]); clear H1 H2 H3.

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

  Instance spec_of_F_felem_copy : spec_of felem_copy := spec_of_felem_copy.

   Lemma curve_add_alt_ok : program_logic_goal_for_function! curve_add_alt_func.
   Proof.
      enter curve_add_alt_func.

      repeat straightline'.
      (* cbv [curve_add_alt]. *)

      remember ((FElem (Some tight_bounds) pX1 X1 ⋆ FElem (Some tight_bounds) pY1 Y1
      ⋆ FElem (Some tight_bounds) pZ1 Z1 ⋆ R1))%sep as P1.

      remember ((FElem (Some tight_bounds) pX2 X2 ⋆ FElem (Some tight_bounds) pY2 Y2
      ⋆ FElem (Some tight_bounds) pZ2 Z2 ⋆ R2))%sep as P2.

      remember ((FElem (Some tight_bounds) pXout Xoutold
      ⋆ FElem (Some tight_bounds) pYout Youtold
      ⋆ FElem (Some tight_bounds) pZout Zoutold ⋆ Rout))%sep as P3.

      (* assert (id ((fun m => (P1 m /\ P2 m /\ P3 m)) mem0)) by (simpl; auto). *)
      (* clear H8 H7 H6. *)

      (* rewrite String.eqb_refl. *)
      (* clear H0 H1 H2 H3 H4. *)
      (* do 3 straightline'. *)
      collect H6 H7 H8.
      (* rename H0 into Hmem. *)
      (* clear H6 H7 H8. *)
      repeat straightline'.

      simpl.
      rewrite String.eqb_refl.
      repeat straightline'.

      (* eassert (Htemp : forall m, array ptsto (word.of_Z 1) a stack17 m <-> exists f, Field.FElem a f m). *)
      (* intros. split. *)
      (* { admit. } *)
      (*   (* intros. eapply array_1_to_anybytes in H65. *) *)
      (*   (* pose proof alloc_to_FElem a m. *) *)

      (*   (* exists (Util.encode_bytes stack17). *) *)
      (*   (* split. *) *)
      (*   (* eapply alloc_to_FElem. rewrite <- H54. assumption. } *) *)
      (* { intros. pose proof anybytes_to_array_1 m a felem_size_in_bytes. *)
      (*   destruct H65 as [f]. *)
      (*   eapply FElem_to_anybytes in H65. *)
      (*   apply H66 in H65 as []. *)
      (* } *)
      (* try destruct Htemp. try rewrite H65 in *. *)

      (* try eassert (Htemp : exists f, array ptsto (word.of_Z 1) a0 stack18 = Field.FElem a f) by admit. *)
      (* try destruct Htemp. try rewrite H66 in *. *)

      (* try eassert (Htemp : exists f, array ptsto (word.of_Z 1) a1 stack19 = Field.FElem a f) by admit. *)
      (* try destruct Htemp. try rewrite H67 in *. *)

      (* try eassert (Htemp : exists f, array ptsto (word.of_Z 1) a2 stack20 = Field.FElem a f) by admit. *)
      (* try destruct Htemp. try rewrite H68 in *. *)

      (* try eassert (Htemp : exists f, array ptsto (word.of_Z 1) a3 stack21 = Field.FElem a f) by admit. *)
      (* try destruct Htemp. try rewrite H69 in *. *)

      (* try eassert (Htemp : exists f, array ptsto (word.of_Z 1) a4 stack22 = Field.FElem a f) by admit. *)
      (* try destruct Htemp. try rewrite H70 in *. *)
      (* assert (Hequiv : forall p x, exists f, FElem (Some tight_bounds) p x = emp (bounded_by tight_bounds f /\ feval f = x) ⋆ (Field.FElem p f)). *)
      (* intros. *)
      (* destruct (FElem (Some tight_bounds) p x). *)
      (* pose proof FElem_equiv mem0 pX1 X1. *)
      (* rewrite H65 in H10. *)

      (* rewrite (FElem_equiv) in H10. *)
      (* eassert (Htemp : forall m, FElem (Some tight_bounds) pX1 X1 m <-> (exists f, Field.FElem pX1 f m /\ bounded_by tight_bounds f /\ feval f = X1)). *)
      (* intros; split. *)
      (* { intros. destruct H65 as [f]. *)
      (*   rewrite sep_emp_l in H65. *)
      (*   unfold maybe_bounded in H65. *)
      (*   exists f. intuition subst. } *)
      (* { intros [f]. *)
      (*   exists f. *)
      (*   rewrite sep_emp_l. *)
      (* intuition subst. } *)

      (* eauto. *)
      (*   eauto. *)
      (*   sep eauto. assumption. } *)
      (* try destruct Htemp, H71, H72. try rewrite H71 in *. *)

      (* try eassert (Htemp : exists f, FElem (Some tight_bounds) pX2 X2 = Field.FElem pX2 f /\ bounded_by tight_bounds f /\ feval f = X2) by admit. *)
      (* try destruct Htemp, H73, H74. try rewrite H73 in *. *)

      (* try eassert (Htemp : exists f, FElem (Some tight_bounds) pY1 Y1 = Field.FElem pY1 f /\ bounded_by tight_bounds f /\ feval f = Y1) by admit. *)
      (* try destruct Htemp, H75, H76. try rewrite H75 in *. *)

      (* try eassert (Htemp : exists f, FElem (Some tight_bounds) pY2 Y2 = Field.FElem pY2 f /\ bounded_by tight_bounds f /\ feval f = Y2) by admit. *)
      (* try destruct Htemp, H77, H78. try rewrite H77 in *. *)

      (* try eassert (Htemp : exists f, FElem (Some tight_bounds) pZ1 Z1 = Field.FElem pZ1 f /\ bounded_by tight_bounds f /\ feval f = Z1) by admit. *)
      (* try destruct Htemp, H79, H80. try rewrite H79 in *. *)

      straightline_call.
      {
        (* simpl in Hmem. *)
        split.
        (* NB: In goal 2, doing sep_and_fwd first does not preserve all memory for after the call (it uses the wrong ambient memory for FElem None a out) *)
        2: ecancel_assumption.
        do 2 sep_and_fwd.
        subst P1 P2 P3.
        ecancel_assumption.
      }
      clear dependent mCombined0.

      repeat straightline'.

      straightline_call.
      {
        repeat split.
        2: ecancel_assumption.
        repeat sep_and_fwd.
        subst P1 P2 P3.
        ecancel_assumption.
      }
      clear dependent a6.

      repeat straightline'.

      straightline_call.
      {
        repeat split.
        2: ecancel_assumption.
        repeat sep_and_fwd.
        subst P1 P2 P3.
        ecancel_assumption.
      }
      clear dependent a8.

      repeat straightline'.

      straightline_call.
      {
        repeat split.
        2: ecancel_assumption.
        repeat sep_and_fwd.
        subst P1 P2 P3.
        ecancel_assumption.
      }
      clear dependent a6.

      repeat straightline'.

      straightline_call.
      {
        repeat split.
        2: ecancel_assumption.
        repeat sep_and_fwd.
        subst P1 P2 P3.
        ecancel_assumption.
      }
      clear dependent a8.

      repeat straightline'.

      straightline_call.
      {
        repeat split.
        2: ecancel_assumption.
        repeat sep_and_fwd.
        subst P1 P2 P3.
        ecancel_assumption.
      }
      clear dependent a6.

      repeat straightline'.

      straightline_call.
      {
        repeat split.
        (* 2: ecancel_assumption. *)
        repeat sep_and_fwd.
        subst P3.
        ecancel_assumption.
      }
      clear dependent a8.

      repeat straightline.
      eexists.
      split.
      straightline'.
      straightline'.
      straightline'.
      reflexivity.

      eassert (h1 : (FElem _ a4 _ ⋆ _) a6) by ecancel_assumption.

      destruct h1 as [mq [mr [h1 [h2 h3]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      eassert (h4 : (FElem _ a3 _ ⋆ _) mr) by ecancel_assumption.

    destruct h4 as [mq' [mr' [h4 [h5 h6]]]].

    eexists. eexists. split.
    1: {
      eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
    }
    split; [eapply map.split_comm; eauto| ].

    eassert (h7 : (FElem _ a2 _ ⋆ _) mr') by ecancel_assumption.

    destruct h7 as [mq'' [mr'' [h7 [h8 h9]]]].
    eexists. eexists. split.
    1: {
      eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
    }
    split; [eapply map.split_comm; eauto| ].

    eassert (h10 : (FElem _ a1 _ ⋆ _) mr'') by ecancel_assumption.

    destruct h10 as [mq''' [mr''' [h10 [h11 h12]]]].
    eexists. eexists. split.
    1: {
      eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
    }
    split; [eapply map.split_comm; eauto| ].

    eassert (h13 : (FElem _ a0 _ ⋆ _) mr''') by ecancel_assumption.

    destruct h13 as [mq'''' [mr'''' [h13 [h14 h15]]]].
    eexists. eexists. split.
    1: {
      eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
    }
    split; [eapply map.split_comm; eauto| ].

    eassert (h16 : (FElem _ a _ ⋆ _) mr'''') by ecancel_assumption.

    destruct h16 as [mq''''' [mr''''' [h16 [h17 h18]]]].
    eexists. eexists. split.
    1: {
      eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
    }
    split; [eapply map.split_comm; eauto| ].

    split; auto.

    split; auto.

    do 3 eexists.
    split.
    eassumption.

    ecancel_assumption.

   Qed.



End __.
