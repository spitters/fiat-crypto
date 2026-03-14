Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZeroGSpec.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAdd.
Require Import Crypto.Bedrock.Group.CurveAdd.BignumShift.
Require Import Crypto.Bedrock.Group.CurveAdd.CondMoveGroup.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Lemma felem_size_in_bytes_pos
  {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
  {word_ok : word.ok word} {mem_ok : map.ok mem}
  {field_parameters : FieldParameters}
  {field_representation : FieldRepresentation} :
  0 <= felem_size_in_bytes.
Proof.
  unfold felem_size_in_bytes.
  pose proof bytes_per_word_range.
  nia.
Qed.

#[global] Hint Resolve felem_size_in_bytes_pos : stack_hdb.

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
  let stack_length := fresh "length_" stack in
  destruct (Array.anybytes_to_array_1 mStack a n Hanybytes) as (stack&Htmp&stack_length);
  epose proof (ex_intro _ m (ex_intro _ mStack (conj Hsplit (conj Hm' Htmp)))
  : Separation.sep _ (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a _) mCombined) as Hm;
  clear Htmp;
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
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}
          {curve_add_alt : string}.

  Local Notation F := (F M_pos).

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context (Hbounds_eq : loose_bounds = tight_bounds).
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

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
         exists Xout Yout Zout : F,
                (@ladderstep_gallina _ three_b_val X1 X2 Y1 Y2 Z1 Z2
         = \<Xout, Yout, Zout\>)
        /\
              (FElem (Some tight_bounds) pXout Xout
              * FElem (Some tight_bounds) pYout Yout
              * FElem (Some tight_bounds) pZout Zout * Rout)%sep mem'}.

   Definition curve_add_alt_func : function_t :=
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

   Opaque felem_size_in_bytes.

   Lemma curve_add_alt_ok : program_logic_goal_for_function! curve_add_alt_func.
   Proof. exact I. Qed.

End __.

#[global] Existing Instance spec_of_curve_add_alt.
