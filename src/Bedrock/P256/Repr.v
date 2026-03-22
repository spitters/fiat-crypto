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

Lemma coord_feval : forall (x : coord),
  feval (bs2felem (coord.to_bytes x)) = x.
Proof.
  intro x.
  cbv [feval p256_frep
       Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.field_representation
       Signature.field_representation
       Representation.frep Representation.eval_words
       felem_to_list bs2felem proj1_sig
       eval_trans coord.to_bytes].
  (* Goal: F.of_Z M_pos (Positional.eval weight n
       (from_montgomerymod (map word.unsigned (bs2ws 8 (le_split 32 (F.to_Z (x * R))))))) = x *)
  rewrite <- (F.of_Z_to_Z x).
  apply F.eq_of_Z_iff.
  rewrite Z.mod_small by (apply F.to_Z_range; reflexivity).
  (* Goal: Positional.eval ... (from_montgomerymod ...) mod M = F.to_Z x *)
  (* The from_montgomerymod applies: eval(from_mont(v)) mod m = eval(v) * r'^n mod m
     And eval(v) = F.to_Z(x*R) since the words encode x*R.
     Then F.to_Z(x*R) * r'^n mod m = F.to_Z(x*R) * R^(-1) mod m
     = F.to_Z x * R * R^(-1) mod m = F.to_Z x mod m = F.to_Z x. *)
  admit.
Admitted.

(* ================================================================ *)
(* coord_bounded: bounded_by loose_bounds (bs2felem (coord.to_bytes x)) *)
(* ================================================================ *)

Lemma coord_bounded : forall (x : coord),
  bounded_by loose_bounds (bs2felem (coord.to_bytes x)).
Proof.
  intro x.
  cbv [bounded_by p256_frep
       Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.field_representation
       Signature.field_representation
       Representation.frep
       felem_to_list bs2felem proj1_sig
       list_in_bounds coord.to_bytes].
  (* Goal: WordByWordMontgomery.valid 64 4 m (map word.unsigned (bs2ws 8 (le_split 32 (F.to_Z (x*R))))) *)
  (* valid a = small a /\ 0 <= eval a < m
     - small: a = partition weight 4 (eval a). The words from bs2ws(le_split 32 z)
       are the canonical partition of z when z < 2^256 = weight 4.
     - 0 <= eval a < m: eval a = F.to_Z(x*R) which is in [0, m). *)
  admit.
Admitted.

(* ================================================================ *)
(* FElem_to_coord: FElem → coord.to_bytes (reverse direction)        *)
(* ================================================================ *)

Lemma FElem_to_coord : forall (r : coord) pout (out_felem : felem),
  feval (felem_to_list out_felem) = r ->
  Lift1Prop.impl1 (FElem pout out_felem) ((coord.to_bytes r)$@pout).
Proof.
  intros r pout out_felem Heval m Hfelem.
  apply (felem_to_bytes pout out_felem) in Hfelem.
  (* Goal: (coord.to_bytes r)$@pout m *)
  (* Have: (ws2bs 8 out_felem)$@pout m *)
  (* Need: ws2bs 8 out_felem = coord.to_bytes r *)
  (* Since feval out = r, by reverse Montgomery:
     eval(out) = F.to_Z(r * R) and ws2bs(out) = le_split 32 (eval(out))
     = le_split 32 (F.to_Z(r*R)) = coord.to_bytes r. *)
  admit.
Admitted.
