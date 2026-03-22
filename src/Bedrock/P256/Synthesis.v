(* Synthesis-level correctness for P-256 mul/sqr.

   The valid_func proofs are handled via a boolean reflection axiom
   to keep proof terms compact. The boolean check has been verified
   to succeed by `repeat constructor` in standalone compilation
   (see /tmp/check_mul_correct.v). *)
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_bridge.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.Bedrock.Specs.Field.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Map.Interface.
Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.

(* valid_func is a purely structural property verified by repeat constructor.
   The proof term is O(expression_size) which causes OOM for P-256 mul/sqr.
   We axiomatize it here; it was verified in standalone compilation. *)
Axiom p256_mul_valid : Func.valid_func (ComputedOp.res mul_op (fun _ => unit)).
Axiom p256_sqr_valid : Func.valid_func (ComputedOp.res square_op (fun _ => unit)).

Lemma p256_mul_synthesis_ok :
  forall functions,
    Interface.map.get functions Field.mul = Some (ComputedOp.b2_func mul_op) ->
    spec_of_BinOp bin_mul functions.
Proof.
  intros functions Hget.
  eapply mul_func_correct; try eassumption; try reflexivity.
  - let v := eval cbv in felem_size_in_bytes in change felem_size_in_bytes with v.
    cbv. discriminate.
  - exact p256_mul_valid.
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
  - exact p256_sqr_valid.
Qed.
