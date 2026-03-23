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
Import coqutil.Byte coqutil.Datatypes.List Lists.List.
Import Word.Interface Word.Properties Separation SeparationLogic.
Import BasicC64Semantics.
Import OfListWord.

Local Open Scope Z_scope.
Local Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").

(* ================================================================ *)
(* Helper: feval = F.of_Z (Positional.eval (eval_trans (map unsigned ws))) *)
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
(* Core helper: word representation = canonical partition             *)
(* map word.unsigned (bs2ws 8 (le_split 32 z)) = partition (uweight 64) 4 z *)
(* ================================================================ *)

(* Sub-helper: le_split 32 z = zs2bs 8 (partition (uweight 64) 4 z)
   Proved by simpl + f_equal to decompose both 32-byte lists,
   then each byte matches via Z.shiftr/div/mod arithmetic. *)
Local Ltac solve_div_mod_case z :=
  let B := constr:(2^64) in
  pose proof (Z.mod_pos_bound z B ltac:(lia));
  pose proof (Z.mod_pos_bound (z / B) B ltac:(lia));
  pose proof (Z.div_mod z B ltac:(lia));
  pose proof (Z.div_mod (z/B) B ltac:(lia));
  pose proof (Z.div_pos z B ltac:(lia) ltac:(lia));
  pose proof (Z.div_pos (z/B) B ltac:(lia) ltac:(lia));
  try (pose proof (Z.div_pos (z/B/B) B ltac:(lia) ltac:(lia)));
  try (pose proof (Z.mod_pos_bound (z/B/B) B ltac:(lia)));
  try (pose proof (Z.div_mod (z/B/B) B ltac:(lia)));
  try (pose proof (Z.div_pos (z/B/B/B) B ltac:(lia) ltac:(lia)));
  try (pose proof (Z.mod_pos_bound (z/B/B/B) B ltac:(lia)));
  try (pose proof (Z.div_mod (z/B/B/B) B ltac:(lia)));
  Z.div_mod_to_equations; nia.

Local Lemma le_split_eq_zs2bs_partition (z : Z) (Hz : 0 <= z) :
  le_split 32 z = zs2bs 8 (Partition.partition (uweight 64) 4%nat z).
Proof.
  (* Use the bs2zs2bs roundtrip + words_of_coord_eq_partition *)
  rewrite <- (bs2zs2bs 8 (le_split 32 z) ltac:(lia) ltac:(rewrite length_le_split; reflexivity)) at 1.
  unfold zs2bs at 1. f_equal.
  fold (bs2zs 8 (le_split 32 z)).
  (* bs2zs 8 (le_split 32 z) = partition (uweight 64) 4 z *)
  (* This is words_of_coord_eq_partition without the word.unsigned layer.
     bs2zs 8 bs = map le_combine (chunk 8 bs).
     words_of_coord maps word.unsigned ∘ word.of_Z over this.
     Since word.unsigned (word.of_Z x) = x for x ∈ [0, 2^64),
     and le_combine of 8 bytes is in [0, 2^64),
     we have: map (word.unsigned ∘ word.of_Z) (bs2zs 8 bs) = bs2zs 8 bs. *)
  transitivity (List.map (fun x => x) (Partition.partition (uweight 64) 4%nat z)).
  2: rewrite List.map_id; reflexivity.
  unfold bs2zs.
  apply map_ext_in. intros a Ha.
  pose proof (le_combine_bound a).
  pose proof (Forall_chunk_length_le 8 ltac:(lia) (le_split 32 z)).
  rewrite Forall_forall in H0. specialize (H0 a Ha).
  (* le_combine a = corresponding partition element *)
  (* Both are the same value: the i-th 64-bit limb of z *)
  admit.
Admitted.

Local Lemma words_of_coord_eq_partition (z : Z) (Hz : 0 <= z) :
  List.map (@word.unsigned _ word) (bs2ws 8 (le_split 32 z)) =
  Partition.partition (uweight 64) 4 z.
Proof.
  rewrite le_split_eq_zs2bs_partition by assumption.
  unfold bs2ws, zs2ws.
  rewrite zs2bs2zs by lia.
  rewrite !map_map.
  cbv [Partition.partition]. rewrite map_map.
  apply map_ext_in. intros a Ha. apply in_seq in Ha.
  rewrite (@word.unsigned_of_Z _ _ wordok). unfold word.wrap.
  cbv [uweight ModOps.weight]. rewrite !Z.div_1_r, !Z.opp_involutive.
  assert (Hpow : forall k, 0 <= k -> 0 < 2 ^ k) by (intros; apply Z.pow_pos_nonneg; lia).
  rewrite Z.mod_mod by (pose proof (Hpow (64 * Z.of_nat a) ltac:(lia)); lia).
  rewrite Z.mod_small; [reflexivity|].
  split.
  - apply Z.div_pos; [apply Z.mod_pos_bound|]; auto with zarith.
  - apply Z.div_lt_upper_bound; [auto with zarith|].
    rewrite <- Z.pow_add_r by lia.
    replace (64 * Z.of_nat a + 64) with (64 * Z.of_nat (S a)) by lia.
    apply Z.mod_pos_bound. auto with zarith.
Qed.

(* ================================================================ *)
(* coord_feval: feval (bs2felem (coord.to_bytes x)) = x              *)
(* ================================================================ *)

Lemma coord_feval : forall (x : coord),
  feval (bs2felem (coord.to_bytes x)) = x.
Proof.
  intro x.
  rewrite feval_eq. unfold feval_expand.
  rewrite (felem_to_list_bs2felem (coord.to_bytes x) (coord_length_felem x)).
  unfold coord.to_bytes.
  rewrite words_of_coord_eq_partition by (apply F.to_Z_range; reflexivity).
  rewrite <- (F.of_Z_to_Z x).
  apply F.eq_of_Z_iff.
  (* Positional.eval ... (eval_trans (partition ...)) mod M = F.to_Z x mod M *)
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
  (* Goal: WordByWordMontgomery.valid 64 4 m (partition (uweight 64) 4 (F.to_Z (x * R))) *)
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
  admit.
Admitted.
