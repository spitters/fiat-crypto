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
(* Helper: feval = F.of_Z (Positional.eval (eval_trans (map unsigned ws))) *)
(* Proved by reflexivity — avoids expanding the huge FieldRepresentation record *)
(* ================================================================ *)

Local Definition feval_expand (ws : list word.rep) : coord :=
  let zs := List.map (@word.unsigned _ word) ws in
  let decoded := @eval_trans 64 m zs in
  F.of_Z M_pos (Core.Positional.eval (UniformWeight.uweight 64) 4%nat decoded).

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
(* coord_feval: feval (bs2felem (coord.to_bytes x)) = x              *)
(* ================================================================ *)

Lemma coord_feval : forall (x : coord),
  feval (bs2felem (coord.to_bytes x)) = x.
Proof.
  intro x.
  rewrite feval_eq.
  unfold feval_expand.
  cbv [bs2felem proj1_sig coord.to_bytes felem_to_list].
  cbv beta.
  rewrite <- (F.of_Z_to_Z x).
  apply F.eq_of_Z_iff.
  (* Goal: Positional.eval ... (eval_trans ...) mod Z.pos M_pos
         = F.to_Z x mod Z.pos M_pos *)
  (* RHS: F.to_Z x is in [0, M), so mod is identity *)
  (* LHS: eval_trans = from_montgomerymod, applied to the canonical
     partition of F.to_Z(x*R). The result mod M = F.to_Z(x*R) * r'^n mod M = F.to_Z x. *)
  (* For now this is admitted — closing requires eval_from_montgomerymod
     + eval_partition + the Montgomery inverse identity R * R^{-1} = 1 mod M. *)
  admit.
Admitted.

(* ================================================================ *)
(* coord_bounded: bounded_by loose_bounds (bs2felem (coord.to_bytes x)) *)
(* ================================================================ *)

Lemma coord_bounded : forall (x : coord),
  bounded_by loose_bounds (bs2felem (coord.to_bytes x)).
Proof.
  intro x.
  (* bounded_by takes bounds_type and felem (sig type).
     Use change to replace it without expanding the record. *)
  change (@bounded_by _ _ _ _ _ p256_frep (@loose_bounds _ _ _ _ _ p256_frep))
    with (fun ws : felem => @list_in_bounds 64 m wordlist
       (List.map (@word.unsigned _ word) (@felem_to_list _ _ _ _ _ p256_frep ws))).
  cbv beta.
  cbv [felem_to_list bs2felem proj1_sig coord.to_bytes list_in_bounds].
  (* Goal: WordByWordMontgomery.valid 64 4 m (map word.unsigned (bs2ws 8 (le_split 32 (F.to_Z (x * R))))) *)
  (* valid a = small a /\ 0 <= eval a < m
     - small: a = partition weight 4 (eval a), true because bs2ws(le_split 32 z) is canonical
     - 0 <= eval a < m: eval a = F.to_Z(x*R) in [0, m) *)
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
  (* Suffices: ws2bs 8 out_felem = coord.to_bytes r *)
  (* From Heval + feval_eq: the words encode r in Montgomery form,
     so ws2bs gives le_split 32 (F.to_Z (r * R)) = coord.to_bytes r *)
  admit.
Admitted.
