(* Representation bridge lemmas: coord.to_bytes ↔ FElem.
   These do NOT depend on Synthesis.v — only on Specs.Field + p256_prime.
   Should compile with moderate memory (~2-3GB). *)

From Crypto.Bedrock.P256 Require Import Specs.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.ArrayCasts.
Require Import coqutil.Map.Interface.
From Stdlib Require Import ZArith Lia.
Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.

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
(* Montgomery identity: from_mont(x*R) = x                          *)
(* ================================================================ *)

Lemma coord_feval : forall (x : coord),
  feval (bs2felem (coord.to_bytes x)) = x.
Proof.
  intro x.
  (* The proof chain:
     1. feval ws = F.of_Z _ (Positional.eval weight 4 (from_montgomerymod (map word.unsigned ws)))
     2. ws = bs2ws 8 (le_split 32 (F.to_Z (x * R)))
     3. map word.unsigned (bs2ws 8 (le_split 32 z)) reconstructs partition (uweight 64) 4 z
     4. Positional.eval weight 4 (partition 4 z) = z mod 2^256  [eval_partition]
     5. from_montgomerymod(z) mod m = z * r'^4 mod m  [eval_from_montgomerymod]
     6. F.to_Z(x*R) * r'^4 = F.to_Z x (mod m)  [Montgomery: R * R^(-1) = 1]
     7. F.of_Z _ (F.to_Z x) = x  [F.of_Z_to_Z] *)
  admit.
Admitted.

(* ================================================================ *)
(* coord_bounded: bounded_by loose_bounds (bs2felem (coord.to_bytes x)) *)
(* Canonical encoding satisfies WBW valid                            *)
(* ================================================================ *)

Lemma coord_bounded : forall (x : coord),
  bounded_by loose_bounds (bs2felem (coord.to_bytes x)).
Proof.
  intro x.
  (* bounded_by loose_bounds = WordByWordMontgomery.valid 64 4 m (map word.unsigned ws)
     valid a = small a /\ 0 <= eval a < m
     - small: a = partition weight 4 (eval a), holds because words from le_split are canonical
     - 0 <= eval a < m: F.to_Z(x*R) is in [0, m) by F.to_Z_range *)
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
  (* From felem_to_bytes: FElem pout out_felem ↔ (ws2bs 8 out_felem)$@pout *)
  apply (felem_to_bytes pout out_felem) in Hfelem.
  (* Need: ws2bs 8 out_felem = coord.to_bytes r
     Since feval out = r means from_mont(eval(out)) = r,
     we get eval(out) = to_mont(r) = F.to_Z(r * R).
     Then ws2bs 8 out = le_split 32 (eval(out)) = le_split 32 (F.to_Z(r*R)) = coord.to_bytes r *)
  admit.
Admitted.
