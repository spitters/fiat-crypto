Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.ArrayUtil.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.ScalarsUtil.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Open Scope sep_scope.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.WordByWordMontgomeryUtil.

Section FromListF.

  Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

  Local Notation F := (F M_pos).

  Existing Instance bls12_prime_parameters.
  Existing Instance bls12_field_parameters.
  Existing Instance bls12_field_names.
  Existing Instance bls12_field_representation.

  (*curve-defining parameter b*)
  Definition b := 4.
  Definition three_b := 12.
  Definition uw := (uweight 64).
  Definition n := felem_size_in_words.
  Definition three_b_list := Partition.partition uw n three_b.
  Definition word := BasicC64Semantics.word.
  Definition three_b_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n M (@m' _ 64) three_b_list).
  Definition three_b_words := List.map (@word.of_Z 64 word) three_b_mont.
  Definition wo := @word.of_Z 64 word 0.

  (*Few lemmas about curve parameters*)
  Lemma r'_correct : (2 ^ 64 * (@WordByWordMontgomery.r' 64 _) mod M = 1).
  Proof.
      auto.
  Qed.

  Lemma m'_correct : ((M * WordByWordMontgomery.m' M 64) mod 2 ^ 64 = -1 mod 2 ^ 64).
  Proof.
      cbv [WordByWordMontgomery.m']. cbv [WordByWordMontgomery.r].
      assert (M = (-1) * (-M))%Z by auto.
      remember (ModInv.Z.modinv (- M) (2 ^ 64)) as x.
      rewrite H. subst x. rewrite <- Z.mul_assoc.
      rewrite Z.mul_mod.
      1: {
          pose proof (ModInv.Z.modinv_correct (- M) (2 ^ 64)).
          assert (0 < 2 ^ 64) by lia.
          specialize (H0 H1).
          assert (Z.gcd (Z.abs (-M)) (2 ^ 64) = 1) by auto.
          specialize (H0 H2).
          destruct H0.
          unfold M in *.
          rewrite H0. rewrite <- Z.mul_mod; try lia.
      }
      lia.
  Qed.

  Lemma M_small : (M < (2 ^ 64) ^ Z.of_nat (WordByWordMontgomery.n M 64)).
  Proof.
      cbv [M WordByWordMontgomery.n]. simpl. lia.
  Qed.

  Lemma bw_big : 0 < 64.
  Proof. lia. Qed.

  Lemma M_big : 1 < M.
  Proof.
      cbv. auto.
  Qed.

  Lemma n_nz : n <> 0%nat.
  Proof.
      cbv [n felem_size_in_words]; simpl. cbv [WordByWordMontgomery.n]; simpl; lia.
  Qed.

  (* Lemma M_small : (M < (2 ^ 64) ^ Z.of_nat (n)). *)
  (* Proof. *)
  (*     cbv [n felem_size_in_words M]. simpl. lia. *)
  (* Qed. *)

  Definition from_mont_correct := WordByWordMontgomery.from_montgomerymod_correct 64 n M r' m' r'_correct m'_correct bw_big M_big n_nz M_small.
  Definition to_mont_correct :=  WordByWordMontgomery.to_montgomerymod_correct 64 n M r' m' r'_correct m'_correct bw_big M_big n_nz M_small.

  Ltac param_hammer := cbv [M m' M M_pos r' n]; simpl; try eapply M_small; try eapply m'_correct; try eapply r'_correct; try lia; auto.

  (*Move this lemma elsewhere*)
  Lemma unsigned_of_Z_valid : forall (l : list Z), WordByWordMontgomery.valid 64 n M l -> List.map word.unsigned (List.map (@word.of_Z 64 word) l) = l.
  Proof.
      intros.
      erewrite Util.map_unsigned_of_Z. eapply MaxBounds.map_word_wrap_bounded'.
      1: eapply BasicLemmas.ZRange.is_tighter_than_bool_Reflexive.
      eapply valid_max_bounds. eapply H.
  Qed.

  Lemma three_b_mont_eq : three_b_mont = (@WordByWordMontgomery.to_montgomerymod 64 n M (@m' _ 64) three_b_list).
  Proof. vm_compute; auto. Qed.

  Lemma three_b_list_valid : WordByWordMontgomery.valid 64 n M three_b_list.
  Proof.
      split.
      1: {
          eapply WordByWordMontgomery.WordByWordMontgomery.small_m_enc; try lia; cbv [three_b]; try lia.
          cbv [n felem_size_in_words]. simpl; lia.
      }
      unfold three_b_list.
      erewrite <- WordByWordMontgomery.WordByWordMontgomery.m_enc_correct_montgomery; try lia; cbv [three_b M]; try (simpl; lia).
  Qed.

  Lemma three_b_mont_valid : WordByWordMontgomery.valid 64 n M three_b_mont.
  Proof.
      rewrite three_b_mont_eq.
      eapply to_mont_correct.
      eapply three_b_list_valid.
  Qed.

  Lemma three_b_mont_mod : (WordByWordMontgomery.from_montgomerymod 64
                                (WordByWordMontgomery.n M 64) M (WordByWordMontgomery.m' M 64)
                                (List.map Naive.unsigned three_b_words)) = three_b_list.
  Proof.
      cbv [three_b_words]. rewrite three_b_mont_eq. eapply eval_inj_list.
      2: eapply three_b_list_valid.
      1: {
          eapply from_mont_correct.
          erewrite unsigned_of_Z_valid; eapply to_mont_correct; eapply three_b_list_valid.
      }
      erewrite unsigned_of_Z_valid.
      2: eapply to_mont_correct; eapply three_b_list_valid.
      erewrite from_to_mont_inv; auto.
      1: eapply r'_correct.
      1: lia.
      1: cbv [n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; simpl; lia.
      1: cbv [M n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; lia.
      1: cbv; reflexivity.
      eapply three_b_list_valid.
  Qed.

  Definition bls12_from_list : Syntax.func := (from_list, (["out"], (nil : list string), bedrock_func_body:(
    coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_b_mont 0)));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (nth 1 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (nth 2 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (nth 3 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (nth 4 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (nth 5 three_b_mont 0))
                                             ))).

  (*Printing to C*)
  (* From bedrock2 Require Import ToCString Bytedump. *)
  (* Definition c_mod := (c_module (from_list_func :: nil)). *)
  (* Eval compute in c_mod. *)

  Instance spec_of_bls12_from_list : spec_of from_list := spec_of_from_list (ModularArithmetic.F.of_Z M_pos three_b).

  Ltac collect H1 H2 := let Hnew := (fresh "Hnew") in
  eassert (Hnew : id (fun M => (_ M) /\ (_ M)) _) by (cbv [id]; split; [eapply H1| eapply H2]); clear H1 H2.

  Local Infix "+w" := word.add (at level 80).
  Local Infix "*w" := word.mul (at level 70).

  Lemma felem_copy_ok : program_logic_goal_for_function! bls12_from_list. (*Why does this take 5 minutes???!???*)
  Proof.
      cbv [spec_of_bls12_from_list Field.spec_of_from_list]. cbv [program_logic_goal_for].
      intros.

      cbv [bls12_from_list]. simpl.
      repeat straightline.

      cbv [FElem Bignum.Bignum] in H.
      sepsimpl.

      assert (felem_size_in_words= 6)%nat by auto.
      rewrite H1 in H; clear H1.
      do 7 (destruct outold; try discriminate). clear H.
      assert (Hlist : forall {A : Type} (l : list A) a, a :: l = [a] ++ l) by auto.
      rewrite Hlist in H0.

      (*modifying H1*)
      eapply array_append_R' in H0.
      remember (word.of_Z (Memory.bytes_per_word 64)) as w1. eassert (forall l, Datatypes.length [l] = 1%nat) by auto.
      rewrite H in H0.
      remember (word.of_Z (Z.of_nat 1)) as w2.
      rewrite Hlist in H0; eapply array_append_R' in H0. rewrite H in H0. rewrite <- Heqw2 in H0.
      rewrite Hlist in H0; eapply array_append_R' in H0. rewrite H in H0. rewrite <- Heqw2 in H0.
      rewrite Hlist in H0; eapply array_append_R' in H0. rewrite H in H0. rewrite <- Heqw2 in H0.
      rewrite Hlist in H0; eapply array_append_R' in H0. rewrite H in H0. rewrite <- Heqw2 in H0.

      cbv [array] in H0. sepsimpl.

      Ltac straightline' :=
        match goal with
          | |- store Syntax.access_size.word _ _ _ _ =>
            eapply store_word_of_sep
          | _ => straightline
        end.


      do 4 straightline'.
      1: ecancel_assumption.

      do 4 straightline'.

      Lemma word_add_assoc : forall (w1 : BasicC64Semantics.word) z1 z2, ((w1 +w (word.of_Z z1)) +w (word.of_Z z2)) = (w1 +w (word.of_Z (z1 + z2))).
      Proof.
          intros. rewrite <- word.add_assoc.
          rewrite word.ring_morph_add. auto.
      Qed.

      eassert (Hword : w1 *w w2 = word.of_Z 8) by auto.
      repeat rewrite Hword in *.
      1: ecancel_assumption.
      do 4 straightline'.

      assert (Htemp : 8 + 8 = 16) by auto.
      repeat rewrite word_add_assoc in H2. rewrite Htemp in H2. clear Htemp.
      1: ecancel_assumption.

      do 4 straightline'.

      assert (Htemp : 8 + 16 = 24) by auto.
      repeat rewrite word_add_assoc in H3. rewrite Htemp in H3. clear Htemp.
      1: ecancel_assumption.

      do 4 straightline'.
      assert (Htemp : 8 + 24 = 32) by auto.
      repeat rewrite word_add_assoc in H4. rewrite Htemp in H4. clear Htemp.
      1: ecancel_assumption.

      do 4 straightline'.
      assert (Htemp : 8 + 32 = 40) by auto.
      repeat rewrite word_add_assoc in H5. rewrite Htemp in H5. clear Htemp.
      1: ecancel_assumption.

      repeat straightline. split; auto.
      exists three_b_words.
      split.
      2: split; [auto| split].

      3: {
          cbv [FElem Bignum.Bignum].
          eapply (sep_assoc _ _ Rout). sepsimpl.
          1: auto.
          eassert (three_b_words = [word.of_Z _; word.of_Z _ ;word.of_Z _ ; word.of_Z _ ; word.of_Z _ ; word.of_Z _]).
          {
              cbv [three_b_words three_b_mont]. simpl. eauto.
          }
          rewrite H7.
          rewrite Hlist.
          subst w1. subst w2.
          epose proof array_append_R'.
          eapply H8.
          remember ((word.of_Z (Memory.bytes_per_word 64))) as w1.
          remember (word.of_Z (Z.of_nat 1)) as w2.
          rewrite H. rewrite <- Heqw2.
          rewrite Hlist. eapply H8. rewrite H. rewrite <- Heqw2.
          rewrite Hlist. eapply H8. rewrite H. rewrite <- Heqw2.
          rewrite Hlist. eapply H8. rewrite H. rewrite <- Heqw2.
          rewrite Hlist. eapply H8. rewrite H. rewrite <- Heqw2.
          repeat rewrite Hword. cbv [array]. sepsimpl.
          eassert (Hword : w1 *w w2 = word.of_Z 8).
          {
              auto. subst w1. subst w2. simpl. auto.
          }
          repeat rewrite Hword.
          repeat rewrite word_add_assoc.
          assert (Htemp : 8 + 8 = 16) by auto. rewrite Htemp. clear Htemp.
          assert (Htemp : 8 + 16 = 24) by auto. rewrite Htemp. clear Htemp.
          assert (Htemp : 8 + 24 = 32) by auto. rewrite Htemp. clear Htemp.
          assert (Htemp : 8 + 32 = 40) by auto. rewrite Htemp. clear Htemp.
          subst v v1 v0 v2 v3 v4 a a0 a1 a2 a3. sepsimpl. clear H H0 H1 H2 H3 H4 H5 H7 H8.

          Fail ecancel_assumption. (*Why??*)

          clear Hword.
          remember ((pout +w word.of_Z 40)) as p5.
          remember ((pout +w word.of_Z 32)) as p4.
          remember ((pout +w word.of_Z 24)) as p3.
          remember ((pout +w word.of_Z 16)) as p2.
          remember ((pout +w word.of_Z 8)) as p1.

          remember ((word.of_Z 252692002104915169)) as v5.
          remember ((word.of_Z 7007796720291435703)) as v4.
          remember ((word.of_Z 12755092135412849606)) as v3.
          remember ((word.of_Z 8034115857496836953)) as v2.
          remember ((word.of_Z 15904462746612662304)) as v1.
          remember ((word.of_Z 4933130441833534766)) as v0.

          ecancel_assumption.
      }

      1: {
          pose proof three_b_mont_mod.
          (*Apply lemma!!!*)
          cbv [three_b]. cbv [Representation.eval_words]. cbv [eval_trans].
          eapply f_equal. rewrite H7.
          cbv [three_b_list].
          rewrite eval_partition; [| eapply uwprops; lia].
          cbv [three_b n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]. simpl.
          cbv [uw uweight ModOps.weight]. simpl. rewrite Zmod_small; lia.
      }
      cbv [three_b_words].
      rewrite unsigned_of_Z_valid.
      1: eapply three_b_mont_valid.
      1: eapply three_b_mont_valid.
  Qed.

End FromListF.




