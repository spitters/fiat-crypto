(* Representation bridge lemmas: coord.to_bytes ↔ FElem.
   Does NOT depend on Synthesis.v — only on Specs.Field + p256_prime.
   Compile with: rocq c -Q src Crypto -time src/Bedrock/P256/Repr.v *)

From Crypto.Bedrock.P256 Require Import Specs.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.ArrayCasts.
Require Import coqutil.Map.Interface.
From Stdlib Require Import ZArith Lia.
Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.
Local Existing Instances
  Bitwidth64.BW64
  Defaults64.default_parameters
  Defaults64.default_parameters_ok
  p256_field_parameters
  p256_field_parameters_ok
  p256_frep
  p256_frep_ok.

Import Specs.NotationsCustomEntry Specs.coord.
Import LittleEndianList PrimeFieldTheorems.
Import coqutil.Byte Lists.List.
Import Word.Interface Separation SeparationLogic.
Import BasicC64Semantics.
Import OfListWord.

Local Open Scope Z_scope.
Local Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").

(* ================================================================ *)
(* coord.to_bytes length matches felem_size_in_bytes                 *)
(* ================================================================ *)

Lemma coord_length_felem (x : coord) :
  length (coord.to_bytes x) = BinInt.Z.to_nat felem_size_in_bytes.
Proof. rewrite coord.length_coord. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* coord.to_bytes → FElem via felem_from_bytes                       *)
(* ================================================================ *)

Lemma coord_to_FElem (x : coord) px :
  Lift1Prop.impl1 ((coord.to_bytes x)$@px) (FElem px (bs2felem (coord.to_bytes x))).
Proof.
  intros m H.
  apply (felem_from_bytes px (coord.to_bytes x) (coord_length_felem x)).
  exact H.
Qed.

(* ================================================================ *)
(* coord_feval: feval (bs2felem (coord.to_bytes x)) = x              *)
(*                                                                    *)
(* Chain: feval ws = F.of_Z _ (eval(from_mont(map word.unsigned ws))) *)
(*   coord.to_bytes x = le_split 32 (F.to_Z(x*R))                   *)
(*   bs2felem converts bytes→words, from_mont undoes Montgomery,     *)
(*   result is F.of_Z _ (F.to_Z x) = x.                             *)
(* ================================================================ *)

(* All three bridge lemmas need the Montgomery encoding chain.
   Direct cbv creates terms that OOM (~10GB needed).
   We use small targeted unfoldings + abstract lemmas instead. *)

(* Helper: feval for WBW Montgomery = F.of_Z _ (eval(from_mont(map word.unsigned ws)))
   This avoids cbv-unfolding feval which creates huge terms. *)
(* feval ws = F.of_Z _ (Positional.eval weight n (eval_trans (map word.unsigned ws)))
   where eval_trans = from_montgomerymod for WBW Montgomery. *)

Lemma coord_feval : forall (x : coord),
  feval (bs2felem (coord.to_bytes x)) = x.
Proof. admit. Admitted.

Lemma coord_bounded : forall (x : coord),
  bounded_by loose_bounds (bs2felem (coord.to_bytes x)).
Proof. admit. Admitted.

Lemma FElem_to_coord : forall (r : coord) pout (out_felem : felem),
  feval (felem_to_list out_felem) = r ->
  Lift1Prop.impl1 (FElem pout out_felem) ((coord.to_bytes r)$@pout).
Proof. admit. Admitted.
