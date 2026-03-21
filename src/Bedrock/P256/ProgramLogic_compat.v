(** * Rocq 9 compatibility shim for program_logic_goal_for_function!

    bedrock2 v0.0.9's Ltac2 eagerly looks up callee specs during goal
    generation. This fails for P-256 because:
    1. unfold_const doesn't fully reduce cross-module func! definitions
    2. After eval cbv, Ltac2 instance_of fails for normalized strings

    This shim generates goals WITHOUT callee premises. Use it only for
    functions that have no cross-module callees (e.g., u256_set_p256_minushalf_conditional).
    For functions with cross-module callees (p256_coord_sub, p256_coord_add),
    state the lemma explicitly with callee premises.
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
