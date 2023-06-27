Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
Require Import Crypto.Bedrock.Group.CurveAdd.StorePointAtInfinity.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_G1.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_G1_alt.
Require Import Crypto.Bedrock.Group.CurveAdd.BignumShift.
Require Import Crypto.Bedrock.Group.CurveAdd.CondMoveGroup.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAddAlt.
(* why is this called p224? *)
Require Import Crypto.Bedrock.Field.Synthesis.Examples.felem_copy_p224.
Require Import Crypto.Bedrock.Group.CurveAdd.LoopBody.
Require Import Crypto.Bedrock.Group.CurveAdd.ScalarMult.

     (* Require Import bedrock2.Syntax. *)
     (* Require Import compiler.MMIO. *)

     Require Import compiler.Pipeline.
     From bedrock2 Require Import ToCString Bytedump.

     Require Import bedrock2.Syntax.
     Require Import compiler.MMIO.
     Definition funcs : list func :=
       [ bls12_select_znz].

     Compute compile (compile_ext_call (funname_env:=SortedListString.map)) (map.of_list funcs).
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Open Scope sep_scope.


Existing Instance bls12_field_names.

From bedrock2 Require Import ToCString Bytedump.
Definition c_mod := (c_module (store_zero_func:: nil)).
(* Definition mul_fun := Eval vm_compute in (bls12_mul). *)
(* Definition mul_fun := Eval vm_compute in (bls12_mul). *)
Eval compute in bls12_select_znz.
(* Eval compute in cmov_func (group_cmov:="group_cmov"). *)

Definition c_test :=
  Eval vm_compute in
    c_module (bls12_add
                :: bls12_sub
                :: bls12_mul
                :: bls12_from_list
                :: bls12_G1_add
                :: felem_copy_func
                :: G1_add_alt
                :: bls12_zero
                :: bls12_one
                :: store_zero_func
                :: shift_scalar
                :: bls12_select_znz
                :: cmov_func (group_cmov:="group_cmov") (* set the name somewhere consistent *)
                :: (loop_body_func "G1_add_alt")
                :: scalar_mult_func
                :: nil).
Redirect "c_test" Eval cbv in c_test.

(* Local Open Scope bytedump_scope. *)
(* Import Syntax BinInt String List.ListNotations. *)
(* Local Open Scope string_scope. *)
(* Local Open Scope Z_scope. *)
(* Local Open Scope list_scope. *)
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_G1.
(* Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F. *)
Require Import Crypto.Bedrock.Group.CurveAdd.StorePointAtInfinity.

Section test.

  (* Existing Instance bls12_field_names. *)
  (* Existing Instance bls12_field_parameters. *)
  (* Existing Instance bls12_field_representation. *)

  (* Definition three_b := 0. *)
  (*   Definition uw := (uweight 64). *)
  (*   Definition n := felem_size_in_words. *)
  (*   Definition three_b_list := Partition.partition uw n three_b. *)
  (*   Definition word := BasicC64Semantics.word. *)
  (*   Definition three_b_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n m (@m' bls12_prime.field_parameters 64) three_b_list). *)
  (*   Definition three_b_words := List.map (@word.of_Z 64 word) three_b_mont. *)

  (*     Instance spec_of_store_zero : spec_of "store_zero_G" := *)
  (*     fnspec! "store_zero_G" *)
  (*           (pX pY pZ: word) *)
  (*           / (X Y Z : F) R, *)
  (*     { requires tr mem := *)
  (*           (FElem (Some tight_bounds) pX X *)
  (*           * FElem (Some tight_bounds) pY Y *)
  (*           * FElem (Some tight_bounds) pZ Z * R)%sep mem; *)
  (*           ensures tr' mem' := *)
  (*                 (FElem (Some tight_bounds) pX Fzero *)
  (*           * FElem (Some tight_bounds) pY Fone *)
  (*           * FElem (Some tight_bounds) pZ Fzero * R)%sep mem'}. *)

          (* Definition from_list_func : Syntax.func := ("store_zero_F", (["out"], (nil : list string), bedrock_func_body:(
                coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_b_mont 0)));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (nth 1 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (nth 2 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (nth 3 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (nth 4 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (nth 5 three_b_mont 0))
              ))).

        Definition store_zero_func : bedrock2.Syntax.func :=
        ("store_zero", (["outx"; "outy"; "outz"], []:list String.string, bedrock_func_body:(
                coq:(cmd.call [] "store_zero_F" [expr.var ("outx")]);
                coq:(cmd.call [] "store_one_F" [expr.var ("outy")]);
                coq:(cmd.call [] "store_zero_F" [expr.var ("outz")])
        ))).

        From bedrock2 Require Import ToCString Bytedump.
        Definition c_mod := (c_module (store_zero_func:: nil)).

        Eval native_compute in c_mod. *)


Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

From bedrock2 Require Import ToCString Bytedump.
Definition c_mod := (c_module (bls12_G1_add :: nil)).
Eval native_compute in c_mod.

    Existing Instances Defaults64.default_parameters Defaults64.default_parameters_ok.

    (* Local Notation F := (F M_pos). *)

    Check CurveAdd.ladderstep_body.

    Existing Instance bls12_prime_parameters.
    Existing Instance bls12_field_names.
    Existing Instance bls12_field_parameters.
    Existing Instance WordByWordMontgomery.field_representation.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

From bedrock2 Require Import ToCString Bytedump.
Definition c_mod := (c_module (bls12_G1_add :: nil)).

Eval native_compute in c_mod.
