(** * Rocq 9 compatibility shim for program_logic_goal_for_function!

    bedrock2 v0.0.9's Ltac2 eagerly looks up callee specs during goal
    generation. This fails for P-256 because function names in cmd.call
    ("br_full_sub") don't match spec instance names ("full_sub").

    This shim generates goals WITHOUT callee premises. The callee specs
    are provided via Local Existing Instances in the proof context.
*)

From Coq Require Import String List.
From coqutil.Tactics Require Import reference_to_string.
Require Import bedrock2.Syntax.
Require Import bedrock2.ProgramLogic.

(* Override: generate goal without callee premises *)
Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc ltac:(
    let fname := constr:(ltac:(
      constr_string_basename_of_constr_reference_cps proc
        ltac:(fun s => exact s))) in
    let spec := lazymatch constr:(_ : spec_of fname) with ?s => s end in
    exact (forall (functions : @Interface.map.rep _ _ Semantics.env),
      Interface.map.get functions fname = Some proc ->
      spec functions)))
  (at level 10, only parsing).
