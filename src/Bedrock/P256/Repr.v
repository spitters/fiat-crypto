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
Local Lemma chunk_4x8 (a b c d : list Byte.byte) :
  length a = 8%nat -> length b = 8%nat -> length c = 8%nat -> length d = 8%nat ->
  chunk 8 (a ++ b ++ c ++ d) = (a :: b :: c :: d :: nil)%list.
Proof.
  intros Ha Hb Hc Hd.
  rewrite (chunk_app 8 ltac:(lia) a _ ltac:(rewrite Ha; reflexivity)).
  rewrite (chunk_app 8 ltac:(lia) b _ ltac:(rewrite Hb; reflexivity)).
  rewrite (chunk_app 8 ltac:(lia) c _ ltac:(rewrite Hc; reflexivity)).
  rewrite (chunk_small 8 a) by (rewrite Ha; lia).
  rewrite (chunk_small 8 b) by (rewrite Hb; lia).
  rewrite (chunk_small 8 c) by (rewrite Hc; lia).
  rewrite (chunk_small 8 d) by (rewrite Hd; lia).
  reflexivity.
Qed.

Local Lemma bs2zs_le_split_eq_partition (z : Z) (Hz : 0 <= z) :
  bs2zs 8 (le_split 32 z) = Partition.partition (uweight 64) 4%nat z.
Proof.
  unfold bs2zs.
  assert (Hle : le_split 32 z =
    le_split 8 z ++ le_split 8 (Z.shiftr z 64) ++
    le_split 8 (Z.shiftr z 128) ++ le_split 8 (Z.shiftr z 192)).
  { change 32%nat with (8 + (8 + (8 + 8)))%nat.
    rewrite !le_split_app, !Z.shiftr_shiftr by lia. simpl Z.of_nat. reflexivity. }
  rewrite Hle, chunk_4x8 by (apply length_le_split).
  cbn [List.map].
  rewrite !le_combine_split, !Z.shiftr_div_pow2 by lia.
  change (8 * Z.of_nat 8) with 64.
  cbv [Partition.partition uweight ModOps.weight].
  simpl seq. simpl List.map. simpl Z.of_nat. simpl Z.mul.
  rewrite Z.div_1_r.
  apply f_equal2; [reflexivity|].
  apply f_equal2; [|apply f_equal2; [|apply f_equal2; [|reflexivity]]].
  all: rewrite <- mod_mul_div; [| assumption | apply Z.pow_pos_nonneg; lia | apply Z.pow_pos_nonneg; lia].
  all: reflexivity.
Qed.

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
(* coord_feval, coord_bounded, FElem_to_coord *)
(* ================================================================ *)

(* Helper: partition validity for Montgomery bridge proofs *)
Local Ltac assert_mont_params :=
  let r' := fresh "r'" in
  let m' := fresh "m'" in
  set (r' := @WordByWordMontgomery.r' 64 p256_field_parameters);
  set (m' := WordByWordMontgomery.m' m 64);
  assert (Hr'_correct : (2 ^ 64 * r') mod m = 1) by (subst r'; apply Z.eqb_eq; vm_compute; reflexivity);
  assert (Hm'_correct : (m * m') mod 2 ^ 64 = (-1) mod 2 ^ 64) by (subst m'; apply Z.eqb_eq; vm_compute; reflexivity);
  assert (Hm_big : m < (2 ^ 64) ^ Z.of_nat 4) by (apply Z.ltb_lt; vm_compute; reflexivity);
  assert (Hm_small : 1 < m) by (apply Z.ltb_lt; vm_compute; reflexivity);
  assert (Hr4 : (r' ^ 4 * 2^256) mod m = 1) by (subst r'; apply Z.eqb_eq; vm_compute; reflexivity).

Local Ltac prove_partition_valid z Hz :=
  pose proof (@uwprops 64 ltac:(lia)) as Huw;
  split;
  [ (* small *)
    unfold WordByWordMontgomery.WordByWordMontgomery.small;
    change (WordByWordMontgomery.WordByWordMontgomery.eval 64 _)
      with (Core.Positional.eval (uweight 64) 4 (Partition.partition (uweight 64) 4 z));
    rewrite eval_partition by exact Huw;
    rewrite Z.mod_small by (split; [lia|]; cbv [uweight ModOps.weight]; simpl; lia);
    reflexivity
  | (* 0 <= eval < m *)
    change (WordByWordMontgomery.WordByWordMontgomery.eval 64 _)
      with (Core.Positional.eval (uweight 64) 4 (Partition.partition (uweight 64) 4 z));
    rewrite eval_partition by exact Huw;
    rewrite Z.mod_small by (split; [lia|]; cbv [uweight ModOps.weight]; simpl; lia);
    exact Hz ].

Lemma coord_feval : forall (x : coord), feval (bs2felem (coord.to_bytes x)) = x.
Proof.
  intro x. rewrite feval_eq. unfold feval_expand.
  rewrite (felem_to_list_bs2felem (coord.to_bytes x) (coord_length_felem x)).
  unfold coord.to_bytes.
  rewrite words_of_coord_eq_partition by (apply F.to_Z_range; reflexivity).
  rewrite <- (F.of_Z_to_Z x). apply F.eq_of_Z_iff.
  (* Goal: Positional.eval ... (eval_trans m (partition ... (F.to_Z(x*R)))) mod M_pos
           = F.to_Z x mod M_pos *)
  assert_mont_params.
  set (z := F.to_Z (F.of_Z P256.p256 (F.to_Z x) * R)).
  set (v := Partition.partition (uweight 64) 4 z).
  assert (Hz : 0 <= z < m) by (subst z; split; apply F.to_Z_range; reflexivity).
  assert (Heval_v : Core.Positional.eval (uweight 64) 4 v = z mod uweight 64 4)
    by (subst v; apply eval_partition; apply (@uwprops 64 ltac:(lia))).
  assert (Hzmod : z mod uweight 64 4 = z)
    by (apply Z.mod_small; split; [lia|]; cbv [uweight ModOps.weight]; simpl; lia).
  assert (Hvalid : WordByWordMontgomery.WordByWordMontgomery.valid 64 4 m v)
    by (change (WordByWordMontgomery.n m 64) with 4%nat; prove_partition_valid z Hz).
  change (WordByWordMontgomery.n m 64) with 4%nat.
  pose proof (WordByWordMontgomery.WordByWordMontgomery.eval_from_montgomerymod
    64 4 m r' m' Hr'_correct Hm'_correct ltac:(lia) Hm_small ltac:(lia) Hm_big v Hvalid) as Hfrom_eval.
  replace (WordByWordMontgomery.WordByWordMontgomery.eval 64 v)
    with (Core.Positional.eval (uweight 64) 4 v) in Hfrom_eval by reflexivity.
  rewrite Heval_v, Hzmod in Hfrom_eval.
  (* Hfrom_eval : WBW.eval(from_mont v) mod m = (z * r'^4) mod m *)
  (* Show (z * r'^4) mod m = F.to_Z x mod m *)
  assert (Hz_cong : z mod m = (F.to_Z x * 2 ^ 256) mod m).
  { subst z. unfold R. rewrite F.to_Z_mul, F.to_Z_of_Z, F.to_Z_of_Z.
    change (Z.pos P256.p256) with m.
    rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r, Z.mod_mod by lia. reflexivity. }
  assert (Hrhs : (z * r' ^ Z.of_nat 4) mod m = F.to_Z x mod m).
  { change (Z.of_nat 4) with 4.
    rewrite <- Zmult_mod_idemp_l, Hz_cong, Zmult_mod_idemp_l.
    replace (F.to_Z x * 2 ^ 256 * r' ^ 4) with (F.to_Z x * (r' ^ 4 * 2 ^ 256)) by ring.
    rewrite <- Zmult_mod_idemp_r. rewrite Hr4. rewrite Z.mul_1_r. reflexivity. }
  rewrite Hrhs in Hfrom_eval.
  vm_cast_no_check Hfrom_eval.
Qed.

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
  change (WordByWordMontgomery.n m 64) with 4%nat.
  set (z := F.to_Z (x * R)).
  assert (Hz : 0 <= z < m) by (subst z; split; apply F.to_Z_range; reflexivity).
  prove_partition_valid z Hz.
Qed.

(* Reverse bridge: FElem → coord bytes in memory.
   Needs bounded_by to know the word list is in canonical Montgomery form. *)
Lemma FElem_to_coord : forall (r : coord) pout (out_felem : felem),
  feval (felem_to_list out_felem) = r ->
  bounded_by loose_bounds (felem_to_list out_felem) ->
  Lift1Prop.impl1 (FElem pout out_felem) ((coord.to_bytes r)$@pout).
Proof.
  intros r pout out_felem Heval Hbnd m0 Hfelem.
  apply (felem_to_bytes pout out_felem) in Hfelem.
  change (Z.to_nat (Memory.bytes_per_word 64)) with 8%nat in Hfelem.
  rewrite <- Heval. set (ws := felem_to_list out_felem) in *.
  enough (Heq : to_bytes (feval ws) = ws2bs 8 ws) by (rewrite Heq; exact Hfelem).
  (* Extract WBW validity from bounded_by *)
  change (@bounded_by _ _ _ _ _ p256_frep) with
    (fun (b : @bounds _ _ _ _ _ p256_frep) (ws0 : list word.rep) =>
       @list_in_bounds 64 m b (List.map (@word.unsigned _ word) ws0)) in Hbnd.
  change (@loose_bounds _ _ _ _ _ p256_frep) with wordlist in Hbnd.
  cbv beta in Hbnd. cbv [list_in_bounds] in Hbnd.
  set (zs := List.map (@word.unsigned _ word) ws) in *.
  change (WordByWordMontgomery.n m 64) with 4%nat in Hbnd.
  destruct Hbnd as [Hsmall Hrange].
  change (WordByWordMontgomery.WordByWordMontgomery.eval 64 zs)
    with (Core.Positional.eval (uweight 64) 4 zs) in Hrange.
  unfold WordByWordMontgomery.WordByWordMontgomery.small in Hsmall.
  change (WordByWordMontgomery.WordByWordMontgomery.eval 64 zs)
    with (Core.Positional.eval (uweight 64) 4 zs) in Hsmall.
  (* Hsmall : zs = partition (uweight 64) 4 (eval zs) *)
  (* Hrange : 0 <= eval zs < m *)
  (* Montgomery parameters *)
  assert_mont_params.
  unfold to_bytes. rewrite feval_eq. unfold feval_expand.
  unfold eval_trans.
  change (WordByWordMontgomery.n m 64) with 4%nat.
  change (WordByWordMontgomery.m' m 64) with m'0.
  set (from_mont_val := WordByWordMontgomery.WordByWordMontgomery.from_montgomerymod 64 4 m m'0 zs).
  (* Show F.to_Z(F.of_Z(eval(from_mont zs)) * R) = eval(zs) *)
  pose proof (WordByWordMontgomery.WordByWordMontgomery.eval_from_montgomerymod
    64 4 m r'0 m'0 Hr'_correct Hm'_correct ltac:(lia) Hm_small ltac:(lia) Hm_big
    zs (conj Hsmall Hrange)) as Hfrom_eval.
  replace (WordByWordMontgomery.WordByWordMontgomery.eval 64 zs)
    with (Core.Positional.eval (uweight 64) 4 zs) in Hfrom_eval by reflexivity.
  assert (Hkey : F.to_Z (F.of_Z M_pos (Core.Positional.eval (uweight 64) 4 from_mont_val) * R)
                = Core.Positional.eval (uweight 64) 4 zs).
  { rewrite F.to_Z_mul, F.to_Z_of_Z. unfold R. rewrite F.to_Z_of_Z.
    change (Z.pos M_pos) with m. change (Z.of_nat 4) with 4 in Hfrom_eval.
    rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
    rewrite <- Zmult_mod_idemp_l.
    assert (Hbridge : Core.Positional.eval (uweight 64) 4 from_mont_val mod m
                    = (Core.Positional.eval (uweight 64) 4 zs * r'0 ^ 4) mod m)
      by (vm_cast_no_check Hfrom_eval).
    rewrite Hbridge, Zmult_mod_idemp_l.
    replace (Core.Positional.eval (uweight 64) 4 zs * r'0 ^ 4 * 2 ^ 256)
      with (Core.Positional.eval (uweight 64) 4 zs * (r'0 ^ 4 * 2 ^ 256)) by ring.
    rewrite <- Zmult_mod_idemp_r, Hr4, Z.mul_1_r.
    rewrite Z.mod_small by exact Hrange. reflexivity. }
  (* Now: le_split 32 (F.to_Z (...)) = ws2bs 8 ws *)
  (* Use Hkey to replace F.to_Z(...) with eval(zs) *)
  assert (Hgoal2 : le_split 32 (Core.Positional.eval (uweight 64) 4 zs) = ws2bs 8 ws).
  { change (ws2bs 8 ws) with (zs2bs 8 (ws2zs ws)). unfold ws2zs. fold zs.
    rewrite Hsmall. apply le_split_eq_zs2bs_partition. lia. }
  vm_cast_no_check (eq_trans (f_equal (le_split 32) Hkey) Hgoal2).
Qed.
