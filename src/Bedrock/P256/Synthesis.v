(* Synthesis-level correctness for P-256 mul/sqr.
   Uses native_compute for valid_func proofs (compact proof terms). *)
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_bridge.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.Bedrock.Specs.Field.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Map.Interface.
From Stdlib Require Import Lia.
Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.

Local Ltac solve_valid_func :=
  repeat first [apply Func.validf_Abs | apply Func.validf_base];
  repeat first [constructor | lia];
  try reflexivity; try discriminate;
  try (cbv; reflexivity); try (cbv; discriminate);
  try exact I; try lia.

Lemma p256_mul_synthesis_ok :
  forall functions,
    Interface.map.get functions Field.mul = Some (ComputedOp.b2_func mul_op) ->
    spec_of_BinOp bin_mul functions.
Proof.
  intros functions Hget.
  eapply mul_func_correct; try eassumption; try reflexivity.
  - let v := eval cbv in felem_size_in_bytes in change felem_size_in_bytes with v.
    cbv. discriminate.
  - cbv [ComputedOp.res mul_op]; solve_valid_func.
Qed.

Lemma p256_sqr_synthesis_ok :
  forall functions,
    Interface.map.get functions Field.square = Some (ComputedOp.b2_func square_op) ->
    spec_of_UnOp un_square functions.
Proof.
  intros functions Hget.
  eapply square_func_correct; try eassumption; try reflexivity.
  - let v := eval cbv in felem_size_in_bytes in change felem_size_in_bytes with v.
    cbv. discriminate.
  - cbv [ComputedOp.res square_op]; solve_valid_func.
Qed.
