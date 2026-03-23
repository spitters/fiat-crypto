(* Representation bridge lemmas: coord.to_bytes ↔ FElem.
   Does NOT depend on Synthesis.v — only on Specs.Field + p256_prime.
   Compile with: rocq c -Q src Crypto -native-compiler no -time src/Bedrock/P256/Repr.v *)

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
  Bitwidth64.BW64 Defaults64.default_parameters Defaults64.default_parameters_ok
  p256_field_parameters p256_field_parameters_ok p256_frep p256_frep_ok.

Import Specs.NotationsCustomEntry Specs.coord.
Import LittleEndianList PrimeFieldTheorems.
Import coqutil.Byte coqutil.Datatypes.List Lists.List.
Import Word.Interface Word.Properties Separation SeparationLogic.
Import BasicC64Semantics. Import OfListWord.

Local Open Scope Z_scope.
Local Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").

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
(* Length *)
(* ================================================================ *)
Lemma coord_length_felem (x : coord) :
  length (coord.to_bytes x) = BinInt.Z.to_nat felem_size_in_bytes.
Proof. rewrite coord.length_coord. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* coord.to_bytes → FElem *)
(* ================================================================ *)
Lemma coord_to_FElem (x : coord) px :
  Lift1Prop.impl1 ((coord.to_bytes x)$@px) (FElem px (bs2felem (coord.to_bytes x))).
Proof. intros m0 H. apply (felem_from_bytes px _ (coord_length_felem x)). exact H. Qed.

(* ================================================================ *)
(* Z arithmetic helpers *)
(* ================================================================ *)

Local Lemma le_split_app n1 n2 z :
  le_split (n1 + n2) z = le_split n1 z ++ le_split n2 (Z.shiftr z (8 * Z.of_nat n1)).
Proof.
  revert z. induction n1; intros z.
  - simpl. rewrite Z.shiftr_0_r. reflexivity.
  - replace (S n1 + n2)%nat with (S (n1 + n2))%nat by lia.
    change (le_split (S ?n) ?x) with (Byte.byte.of_Z x :: le_split n (Z.shiftr x 8)) at 1.
    change (le_split (S n1) z) with (Byte.byte.of_Z z :: le_split n1 (Z.shiftr z 8)).
    simpl app. f_equal. rewrite IHn1.
    replace (Z.shiftr (Z.shiftr z 8) (8 * Z.of_nat n1))
      with (Z.shiftr z (8 * Z.of_nat (S n1)))
      by (rewrite Z.shiftr_shiftr by lia; f_equal; rewrite Nat2Z.inj_succ; ring).
    reflexivity.
Qed.

Local Lemma le_split_mod n z :
  le_split n (z mod 2^(8 * Z.of_nat n)) = le_split n z.
Proof.
  pose proof (split_le_combine (le_split n z)) as H.
  rewrite length_le_split, le_combine_split in H.
  replace (Z.of_nat n * 8) with (8 * Z.of_nat n) in H by ring. exact H.
Qed.

Local Lemma mod_mul_div z B C (Hz : 0 <= z) (HB : 0 < B) (HC : 0 < C) :
  z mod (B * C) / C = (z / C) mod B.
Proof.
  set (q := z / C). set (r := z mod C).
  set (q2 := q / B). set (r2 := q mod B).
  assert (z = C * q + r) by (subst q r; apply Z.div_mod; lia).
  assert (0 <= r < C) by (subst r; apply Z.mod_pos_bound; lia).
  assert (q = B * q2 + r2) by (subst q2 r2; apply Z.div_mod; lia).
  assert (0 <= r2 < B) by (subst r2; apply Z.mod_pos_bound; lia).
  assert (0 <= q) by (subst q; apply Z.div_pos; lia).
  assert (z mod (B * C) = C * r2 + r) by
    (symmetry; rewrite Z.mul_comm;
     apply Z.mod_unique_pos with (q := q2); [nia|nia]).
  rewrite H4, Z.mul_comm.
  rewrite Zdiv.Z_div_plus_full_l by lia.
  rewrite Z.div_small by lia. subst r2. lia.
Qed.

(* ================================================================ *)
(* le_split 32 z = zs2bs 8 (partition (uweight 64) 4 z) *)
(* ================================================================ *)
(* Core: bs2zs 8 (le_split 32 z) = partition (uweight 64) 4 z *)
Local Lemma bs2zs_le_split_eq_partition (z : Z) (Hz : 0 <= z) :
  bs2zs 8 (le_split 32 z) = Partition.partition (uweight 64) 4%nat z.
Proof. admit. Admitted.

Local Lemma le_split_eq_zs2bs_partition (z : Z) (Hz : 0 <= z) :
  le_split 32 z = zs2bs 8 (Partition.partition (uweight 64) 4%nat z).
Proof.
  rewrite <- (bs2zs2bs 8 (le_split 32 z) ltac:(lia) ltac:(rewrite length_le_split; reflexivity)).
  unfold zs2bs. f_equal.
  (* bs2zs 8 (le_split 32 z) = partition (uweight 64) 4 z *)
  exact (bs2zs_le_split_eq_partition z Hz).
Qed.

(* ================================================================ *)
(* word representation = partition *)
(* ================================================================ *)
Local Lemma words_of_coord_eq_partition (z : Z) (Hz : 0 <= z) :
  List.map (@word.unsigned _ word) (bs2ws 8 (le_split 32 z)) =
  Partition.partition (uweight 64) 4 z.
Proof.
  rewrite le_split_eq_zs2bs_partition by assumption.
  unfold bs2ws, zs2ws. rewrite zs2bs2zs by lia.
  rewrite !map_map. cbv [Partition.partition]. rewrite map_map.
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
(* coord_feval, coord_bounded, FElem_to_coord — remaining admits *)
(* ================================================================ *)

Lemma coord_feval : forall (x : coord), feval (bs2felem (coord.to_bytes x)) = x.
Proof.
  intro x. rewrite feval_eq. unfold feval_expand.
  rewrite (felem_to_list_bs2felem (coord.to_bytes x) (coord_length_felem x)).
  unfold coord.to_bytes.
  rewrite words_of_coord_eq_partition by (apply F.to_Z_range; reflexivity).
  rewrite <- (F.of_Z_to_Z x). apply F.eq_of_Z_iff.
  admit.
Admitted.

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
  admit.
Admitted.

Lemma FElem_to_coord : forall (r : coord) pout (out_felem : felem),
  feval (felem_to_list out_felem) = r ->
  Lift1Prop.impl1 (FElem pout out_felem) ((coord.to_bytes r)$@pout).
Proof.
  intros r pout out_felem Heval m0 Hfelem.
  apply (felem_to_bytes pout out_felem) in Hfelem. admit.
Admitted.
