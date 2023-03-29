Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.Field.
Import ListNotations.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Syntax.
Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.
Local Notation function_t := ((String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type).
Local Notation functions_t := (list function_t).
Local Open Scope sep_scope.
Local Open Scope Z_scope.

(* Parameters for bls12 field. *)
Section Field.
  Definition n : nat := 6.
  Definition u := -0xd201000000010000.
  Definition p_of_u u := (((u - 1)^2 * (u^4 - u^2 + 1)) / 3) + u.
  Definition m := Eval compute in (p_of_u u).

  Eval compute in m.

  Existing Instances Defaults64.default_parameters
           Defaults64.default_parameters_ok.
  Existing Instances no_select_size split_mul_to split_multiret_to.
  Definition prefix : string := "bls12_"%string.

  Instance prime_parameters : PrimeParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos (m))) in
    exact (Build_PrimeParameters M).
    (* (* curve 'A' parameter *) *)
    (* let a := constr:(F.of_Z M (m - 3)) in *)
    (* let prefix := constr:("bls12_"%string) in *)
    (* eapply *)
    (*   (field_parameters_prefixed *)
    (*      M ((a - F.of_Z _ 2) / F.of_Z _ 4)%F prefix). *)
  Defined.

  Local Notation F := (F (Z.to_pos m)).

  Instance field_names : FieldNames := field_names_prefixed prefix.
  Instance field_parameters : FieldParameters F := prime_field_parameters.
  (* Existing Instance prime_field_parameters. *)

  Definition to_mont_string := prefix ++ "to_mont".
  Definition from_mont_string := prefix ++ "from_mont".

  (* Call fiat-crypto pipeline on all field operations *)
Instance bls12_ops : @word_by_word_Montgomery_ops from_mont_string to_mont_string _ _ _ _ _ _ _ _ _ _ _ _ (WordByWordMontgomery.n m machine_wordsize) m.
Proof using Type. Time constructor; make_computed_op. Defined.

  (**** Translate each field operation into bedrock2 and apply bedrock2 backend
        field pipeline proofs to prove the bedrock2 functions are correct. ****)

        Local Ltac begin_derive_bedrock2_func :=
        lazymatch goal with
        | |- context [spec_of_BinOp bin_mul] => eapply mul_func_correct
        | |- context [spec_of_UnOp un_square] => eapply square_func_correct
        | |- context [spec_of_BinOp bin_add] => eapply add_func_correct
        | |- context [spec_of_BinOp bin_sub] => eapply sub_func_correct
        | |- context [spec_of_UnOp un_opp] => eapply opp_func_correct
        (* | |- context [spec_of_UnOp un_scmula24] => eapply scmula24_func_correct *)
        | |- context [spec_of_from_bytes] => eapply from_bytes_func_correct
        | |- context [spec_of_to_bytes] => eapply to_bytes_func_correct
        end.
      
      Ltac derive_bedrock2_func op :=
        begin_derive_bedrock2_func;
        (* this goal fills in the evar, so do it first for [abstract] to be happy *)
        try lazymatch goal with
            | |- _ = b2_func _ => vm_compute; reflexivity
            end;
        (* solve all the remaining goals *)
        lazymatch goal with
        | |- _ = @ErrorT.Success ?ErrT unit tt =>
          abstract (vm_cast_no_check (@eq_refl _ (@ErrorT.Success ErrT unit tt)))
        | |- Func.valid_func _ =>
          eapply Func.valid_func_bool_iff;
          abstract vm_cast_no_check (eq_refl true)
        | |- (_ = _)%Z => vm_compute; reflexivity
        end.

  Derive bls12_from_bytes
         SuchThat (forall functions,
                      spec_of_from_bytes
                        (field_representation:=field_representation_raw m)
                        (bls12_from_bytes :: functions))
         As bls12_from_bytes_correct.
  Proof. Time derive_bedrock2_func from_bytes_op. Qed.

  Derive bls12_to_bytes
         SuchThat (forall functions,
                      spec_of_to_bytes
                        (field_representation:=field_representation_raw m)
                        (bls12_to_bytes :: functions))
         As bls12_to_bytes_correct.
  Proof. Time derive_bedrock2_func to_bytes_op. Qed.

  Derive bls12_mul
         SuchThat (forall functions,
                      spec_of_BinOp bin_mul
                        (field_representation:=field_representation m)
                        (bls12_mul :: functions))
         As bls12_mul_correct.
  Proof. Time derive_bedrock2_func mul_op. Qed.

  Derive bls12_square
         SuchThat (forall functions,
                      spec_of_UnOp un_square
                        (field_representation:=field_representation m)
                        (bls12_square :: functions))
         As bls12_square_correct.
  Proof. Time derive_bedrock2_func square_op. Qed.

  Derive bls12_add
         SuchThat (forall functions,
                      spec_of_BinOp bin_add
                        (field_representation:=field_representation m)
                        (bls12_add :: functions))
         As bls12_add_correct.
  Proof. Time derive_bedrock2_func add_op. Qed.

  Derive bls12_sub
         SuchThat (forall functions,
                      spec_of_BinOp bin_sub
                        (field_representation:=field_representation m)
                        (bls12_sub :: functions))
         As bls12_sub_correct.
  Proof. Time derive_bedrock2_func sub_op. Qed.

  (*TODO: adapt derive_bedrock2_func to also derive the remaining functions.*)
  Derive bls12_from_mont
         SuchThat (forall functions,
                      spec_of_UnOp un_from_mont
                        (field_representation:=field_representation m)
                        (bls12_from_mont :: functions))
         As bls12_from_mont_correct.
  Proof.
    eapply (from_mont_func_correct _ _ _ from_mont_string to_mont_string); auto.
        - vm_compute; reflexivity.
        - eapply Func.valid_func_bool_iff. abstract vm_cast_no_check (eq_refl true).
          Unshelve.
            + auto.
            + auto.
  Qed.

  Derive bls12_to_mont
         SuchThat (forall functions,
                      spec_of_UnOp un_to_mont
                        (field_representation:=field_representation m)
                        (bls12_to_mont :: functions))
         As to_from_mont_correct.
  Proof.
    eapply (to_mont_func_correct _ _ _ from_mont_string to_mont_string); auto.
        - vm_compute; reflexivity.
        - eapply Func.valid_func_bool_iff. abstract vm_cast_no_check (eq_refl true).
          Unshelve. all: auto.
     Qed.

  Derive bls12_select_znz
           SuchThat (forall functions,
                      spec_of_selectznz
                        (field_representation:=field_representation m)
                        (bls12_select_znz :: functions))
         As select_znz_correct.
  Proof.
    eapply select_znz_func_correct; auto.
        - vm_compute; reflexivity.
        - eapply Func.valid_func_bool_iff. abstract vm_cast_no_check (eq_refl true).
     Qed.
(* 
     Require Import bedrock2.Syntax.
     Require Import compiler.Pipeline.
     Require Import compiler.MMIO.
     
     Definition funcs : list func :=
       [ bls12_select_znz].
     
     Compute compile (compile_ext_call (funname_env:=SortedListString.map)) (map.of_list funcs).




     From bedrock2 Require Import ToCString Bytedump.
     Check c_module.
     Definition mul_fun := Eval vm_compute in (bls12_mul).
     
     Definition c_mod := Eval vm_compute in c_module (mul_fun :: nil).

     Local Open Scope bytedump_scope.
     Import Syntax BinInt String List.ListNotations.
     Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
     Eval cbv in c_mod. *)

End Field.
