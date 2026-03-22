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
Require Import Crypto.Arithmetic.UniformWeight.
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
(* Helper: feval = F.of_Z (Positional.eval (eval_trans (map unsigned ws))) *)
(* Proved by reflexivity — avoids expanding the huge record *)
(* ================================================================ *)

Local Definition feval_expand (ws : list word.rep) : coord :=
  let zs := List.map (@word.unsigned _ word) ws in
  let decoded := @eval_trans 64 m zs in
  F.of_Z M_pos (Core.Positional.eval (uweight 64) 4%nat decoded).

Local Lemma feval_eq : @feval _ _ _ _ _ p256_frep = feval_expand.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* coord.to_bytes length = felem_size_in_bytes                       *)
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
  intros m0 H.
  apply (felem_from_bytes px (coord.to_bytes x) (coord_length_felem x)).
  exact H.
Qed.

(* ================================================================ *)
(* Core helper: the word representation of coord.to_bytes matches    *)
(* the canonical partition used by the Montgomery arithmetic.        *)
(*                                                                    *)
(* map word.unsigned (bs2ws 8 (le_split 32 z))                       *)
(* = partition (uweight 64) 4 z     (when 0 <= z)                   *)
(*                                                                    *)
(* This is the key fact connecting byte-level and word-level reprs.  *)
(* ================================================================ *)

(* We prove this via the ArrayCasts roundtrip:
   bs2zs 8 (le_split 32 z) gives the 4 limbs,
   and word.unsigned ∘ word.of_Z is identity on [0, 2^64). *)

Local Lemma words_of_coord_eq_partition (z : Z) (Hz : 0 <= z) :
  List.map (@word.unsigned _ word) (bs2ws 8 (le_split 32 z)) =
  Partition.partition (uweight 64) 4 z.
Proof.
  (* Both sides compute the 4 limbs of z in base 2^64.
     This should be provable by showing bs2zs 8 (le_split 32 z) = partition ... z
     and that word.unsigned ∘ word.of_Z is identity on the range. *)
  admit.
Admitted.

(* ================================================================ *)
(* coord_feval: feval (bs2felem (coord.to_bytes x)) = x              *)
(* ================================================================ *)

Lemma coord_feval : forall (x : coord),
  feval (bs2felem (coord.to_bytes x)) = x.
Proof.
  intro x.
  rewrite feval_eq.
  unfold feval_expand.
  (* Use felem_to_list_bs2felem to resolve the bs2felem + felem_to_list chain *)
  rewrite (felem_to_list_bs2felem (coord.to_bytes x) (coord_length_felem x)).
  unfold coord.to_bytes.
  rewrite words_of_coord_eq_partition by (apply F.to_Z_range; reflexivity).
  rewrite <- (F.of_Z_to_Z x).
  apply F.eq_of_Z_iff.
  admit.
Admitted.

(* ================================================================ *)
(* coord_bounded: bounded_by loose_bounds (bs2felem (coord.to_bytes x)) *)
(* ================================================================ *)

Lemma coord_bounded : forall (x : coord),
  bounded_by loose_bounds (bs2felem (coord.to_bytes x)).
Proof.
  intro x.
  change (@bounded_by _ _ _ _ _ p256_frep) with
    (fun (b : @bounds _ _ _ _ _ p256_frep) (ws : list word.rep) =>
       @list_in_bounds 64 m b (List.map (@word.unsigned _ word) ws)).
  change (@loose_bounds _ _ _ _ _ p256_frep) with wordlist.
  cbv beta.
  rewrite (felem_to_list_bs2felem (coord.to_bytes x) (coord_length_felem x)).
  unfold coord.to_bytes. cbv [list_in_bounds].
  rewrite words_of_coord_eq_partition by (apply F.to_Z_range; reflexivity).
  (* Goal: valid (partition (uweight 64) 4 z) *)
  (* valid a = small a /\ 0 <= eval a < m
     small a = (a = partition (uweight 64) 4 (eval a))
     eval (partition w n z) = z mod w(n) = z mod 2^256 = z (since z < 2^256 < m is wrong, z < m < 2^256)
     So eval(partition(z)) = z, and partition(z) = partition(eval(partition(z))), so small holds.
     And 0 <= z < m since z = F.to_Z(x*R) and F.to_Z gives [0, m). *)
  admit.
Admitted.

(* ================================================================ *)
(* FElem_to_coord: FElem → coord.to_bytes (reverse direction)        *)
(* ================================================================ *)

Lemma FElem_to_coord : forall (r : coord) pout (out_felem : felem),
  feval (felem_to_list out_felem) = r ->
  Lift1Prop.impl1 (FElem pout out_felem) ((coord.to_bytes r)$@pout).
Proof.
  intros r pout out_felem Heval m0 Hfelem.
  apply (felem_to_bytes pout out_felem) in Hfelem.
  (* Have: (ws2bs 8 out_felem)$@pout m0 *)
  (* Need: (coord.to_bytes r)$@pout m0 *)
  (* Suffices: ws2bs 8 (proj1_sig out_felem) = coord.to_bytes r *)
  (* From Heval: feval (proj1_sig out_felem) = r.
     By feval_eq: F.of_Z M_pos (Positional.eval ... (eval_trans (map word.unsigned (proj1_sig out_felem)))) = r.
     The words of out_felem satisfy bounded_by (from the synthesis postcondition),
     so map word.unsigned gives a valid partition.
     eval_trans(partition) gives the Montgomery-decoded value.
     The reverse: ws2bs 8 out = le_split 32 (Positional.eval (map word.unsigned out))
                              = le_split 32 (F.to_Z (r * R))
                              = coord.to_bytes r. *)
  admit.
Admitted.
