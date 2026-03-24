(* WP proof stubs for BLS12-377 Fp2 operations.
   Bodies from bls12_377_Fp2.v, instances from bls12_377_instances.v.
   All proofs are Admitted — to be filled in later. *)

Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_Fp2.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_instances.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section Proofs.
  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls377_prime_parameters bls377_prime_parameters_ok
    bls377_field_representation bls377_field_representation_ok.
  Existing Instance prime_field_parameters.

  (* Re-declare Fp2 instances from bls12_377_instances *)
  Existing Instances
    bls377_Fp2_params bls377_Fp2_rep bls377_Fp2_rep_ok bls377_Fp2_names.

  Local Notation F := (F PrimeField.M_pos).
  Local Notation Fp2 := (F * F)%type.

  (* ================================================================ *)
  (* spec_of instances for Fp-level callees                            *)
  (* ================================================================ *)
  Existing Instances
    spec_of_bls377_add spec_of_bls377_sub spec_of_bls377_mul
    spec_of_bls377_sqr spec_of_bls377_inv spec_of_bls377_copy.

  (* ================================================================ *)
  (* spec_of instances for Fp2-level operations                        *)
  (* (mul/add/sub/copy from bls12_377_instances; sqr/inv/mul_xi/conj  *)
  (*  defined here)                                                    *)
  (* ================================================================ *)
  Existing Instances
    spec_of_bls377_Fp2_add spec_of_bls377_Fp2_sub
    spec_of_bls377_Fp2_mul spec_of_bls377_Fp2_copy.

  Instance spec_of_bls377_Fp2_sqr : spec_of (AbstractField.square (F:=Fp2)) :=
    AbstractField.unop_spec AbstractField.un_square (F:=Fp2).
  Instance spec_of_bls377_Fp2_inv : spec_of (AbstractField.inv (F:=Fp2)) :=
    AbstractField.unop_spec AbstractField.un_inv (F:=Fp2).

  (* ================================================================ *)
  (* program_logic_goal_for_function! macro                            *)
  (* Must be defined locally per file (Ltac2 does not export across   *)
  (* Section boundaries).                                              *)
  (* ================================================================ *)

  Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
  Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.

  Local Ltac2 Notation "instance_of" type(constr) :=
    lazy_match! Ltac2.Constr.pretype (preterm:(_ : $type)) with ?instance => instance end.

  Local Ltac2 rec callee_specs_ft (cmd : constr) : constr list :=
    multi_match! cmd with
      | cmd.cond _ ?c1 ?c2 => List.append (callee_specs_ft c1) (callee_specs_ft c2)
      | cmd.seq ?c1 ?c2 => List.append (callee_specs_ft c1) (callee_specs_ft c2)
      | cmd.while _ ?c => callee_specs_ft c
      | cmd.stackalloc _ _ ?c => callee_specs_ft c
      | cmd.call _ ?f _ => [instance_of (spec_of $f)]
      | _ => []
    end.

  Local Ltac2 program_logic_goal_for_ft (proc : constr) : unit :=
    let unfolded := eval hnf in $proc in
    lazy_match! unfolded with
    | (?fname, (?params, ?rets, ?body)) =>
      let fname_spec := instance_of (spec_of $fname) in
      let specs := callee_specs_ft body in
      let goal := (fun (functions : constr) =>
        List.fold_right (fun ps c => '(($ps $functions) -> $c)) specs '($fname_spec $functions)) in
      exact (forall functions (EnvContains : map.get functions $fname = Some ($params, $rets, $body)),
        ltac2:(let g := goal &functions in exact $g))
    end.

  Local Notation "program_logic_goal_for_function! proc" := (program_logic_goal_for proc ltac2:(
     Control.plus (fun () => program_logic_goal_for_ft (Ltac2.Constr.pretype proc)) (fun _ => exact True)))
    (at level 10, only parsing).

  (* ================================================================ *)
  (* WP proof stubs                                                    *)
  (* ================================================================ *)

  Lemma bls377_Fp2_mul_ok :
    program_logic_goal_for_function! Fp2_mul.
  Proof. admit. Admitted.

  Lemma bls377_Fp2_sqr_ok :
    program_logic_goal_for_function! Fp2_sqr.
  Proof. admit. Admitted.

  Lemma bls377_Fp2_inv_ok :
    program_logic_goal_for_function! Fp2_inv.
  Proof. admit. Admitted.

  Lemma bls377_Fp2_mul_xi_ok :
    program_logic_goal_for_function! Fp2_mul_xi.
  Proof. admit. Admitted.

  Lemma bls377_Fp2_conjugate_ok :
    program_logic_goal_for_function! Fp2_conjugate.
  Proof. admit. Admitted.

End Proofs.
