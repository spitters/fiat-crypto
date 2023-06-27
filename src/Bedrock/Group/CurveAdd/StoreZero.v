Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.
(* Require Import Crypto.Bedrock.Field.Synthesis.Examples.ArrayUtil. *)
(* Require Import Crypto.Bedrock.Field.Synthesis.Examples.ScalarsUtil. *)
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope sep_scope.

Section StoreZero.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type}
    {field_parameters : Field.FieldParameters F}
    {field_parameters_ok : Field.FieldParameters_ok F}.
  Context {field_names : FieldNames F}.

  Context {field_representation : FieldRepresentation F}
          {field_representation_ok : FieldRepresentation_ok F}.

  Instance spec_of_store_zero : spec_of "store_zero" :=
    fnspec! "store_zero"
      (pX pY pZ: word)
      / (X Y Z : F) R,
      { requires tr mem :=
          (FElem None pX X
           * FElem None pY Y
           * FElem None pZ Z * R)%sep mem;
        ensures tr' mem' :=
          (FElem (Some tight_bounds) pX Fzero
           * FElem (Some tight_bounds) pY Fone
           * FElem (Some tight_bounds) pZ Fzero * R)%sep mem'}.

  Definition store_zero_func : bedrock2.Syntax.func :=
    ("store_zero", (["outx"; "outy"; "outz"], []:list String.string, bedrock_func_body:(
            coq:(cmd.call [] zero [expr.var ("outx")]);
            coq:(cmd.call [] one [expr.var ("outy")]);
            coq:(cmd.call [] zero [expr.var ("outz")])
    ))).

  Instance spec_of_zero : spec_of zero := spec_of_NullOp null_zero.
  Instance spec_of_one : spec_of one := spec_of_NullOp null_one.

  Ltac straightline' :=
    match goal with
    | _ => straightline
    | l := _ : map.rep |- _ => subst l
    | l := _ : list word.rep |- _ => subst l
    | |- Some _ = Some _ => try reflexivity
    | |- exists _, _ => eexists
    | |- _ /\ _ => split
    | |- map.get _ _ = _ => repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same
    end.

  Lemma store_zero_ok : program_logic_goal_for_function! store_zero_func.
  Proof.
    enter store_zero_func.
    simpl.
    repeat straightline'.
    straightline_call.
    ecancel_assumption.
    repeat straightline'.
    straightline_call.
    ecancel_assumption.
    repeat straightline'.
    straightline_call.
    ecancel_assumption.
    repeat straightline'.
    subst x x0 x1.
    simpl in H8.
    ecancel_assumption.
  Qed.

End StoreZero.
