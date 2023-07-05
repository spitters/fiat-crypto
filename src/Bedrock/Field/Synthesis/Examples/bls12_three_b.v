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
  (* Definition word := BasicC64Semantics.word. *)
  Definition three_b_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n M (@m' _ 64) three_b_list).
  Definition three_b_words := List.map (@word.of_Z 64 BasicC64Semantics.word) three_b_mont.
  Definition wo := @word.of_Z 64 BasicC64Semantics.word 0.

  (*Few lemmas about curve parameters*)
  Lemma r'_correct : (2 ^ 64 * (@WordByWordMontgomery.r' 64 _) mod M = 1).
  Proof. auto. Qed.

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
  Proof. reflexivity. Qed.

  Lemma bw_big : 0 < 64.
  Proof. reflexivity. Qed.

  Lemma M_big : 1 < M.
  Proof. reflexivity. Qed.

  Lemma n_nz : n <> 0%nat.
  Proof. cbv. congruence. Qed.

  Definition from_mont_correct := WordByWordMontgomery.from_montgomerymod_correct 64 n M r' m' r'_correct m'_correct bw_big M_big n_nz M_small.
  Definition to_mont_correct :=  WordByWordMontgomery.to_montgomerymod_correct 64 n M r' m' r'_correct m'_correct bw_big M_big n_nz M_small.

  (*Move this lemma elsewhere*)
  Lemma unsigned_of_Z_valid : forall (l : list Z), WordByWordMontgomery.valid 64 n M l -> List.map word.unsigned (List.map (@word.of_Z 64 BasicC64Semantics.word) l) = l.
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

  Lemma feval_three_b_words :
    feval three_b_words = F.of_Z M_pos three_b.
  Proof.
    Opaque M_pos three_b three_b_words.
    simpl.
    unfold eval_trans.
    Transparent three_b_words.
    rewrite three_b_mont_mod.
    reflexivity.
  Qed.

  Definition bls12_three_b : Syntax.func := ("bls12_three_b", (["out"], (nil : list string), bedrock_func_body:(
    coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_b_mont 0)));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (nth 1 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (nth 2 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (nth 3 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (nth 4 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (nth 5 three_b_mont 0))))).

  (*Printing to C*)
  (* From bedrock2 Require Import ToCString Bytedump. *)
  (* Definition c_mod := (c_module (from_list_func :: nil)). *)
  (* Eval compute in c_mod. *)

  Instance spec_of_bls12_three_b : spec_of "bls12_three_b" := spec_of_from_list (ModularArithmetic.F.of_Z M_pos three_b) "bls12_three_b".

  Ltac collect H1 H2 := let Hnew := (fresh "Hnew") in
  eassert (Hnew : id (fun M => (_ M) /\ (_ M)) _) by (cbv [id]; split; [eapply H1| eapply H2]); clear H1 H2.

  Local Infix "+w" := word.add (at level 80).
  Local Infix "*w" := word.mul (at level 70).

  Lemma bls12_three_b_ok : program_logic_goal_for_function! bls12_three_b.
  Proof.
      cbv [bls12_three_b spec_of_from_list spec_of_bls12_three_b]. cbv [program_logic_goal_for].
      intros. simpl.
      repeat straightline.

      cbv [FElem Bignum.Bignum] in *.
      sepsimpl.

      assert (size : (felem_size_in_words = 6)%nat) by auto.
      rewrite size in *.
      do 7 (destruct x; try discriminate).
      repeat seprewrite_in (array_cons (T:=@word.rep 64 BasicC64Semantics.word) (word:=BasicC64Semantics.word) (mem:=BasicC64Semantics.mem)) H2.
      repeat seprewrite_in (array_nil (T:=@word.rep 64 BasicC64Semantics.word) (word:=BasicC64Semantics.word) (mem:=BasicC64Semantics.mem)) H2.

      cbn -[scalar] in H2.

      Ltac straightline' :=
        match goal with
        | |- store Syntax.access_size.word _ _ _ _ =>
            eapply store_word_of_sep_2
        | _ => straightline
        end.

      repeat match goal with
             | H : context[ _ +w _ +w _ ] |- _ =>
                 rewrite <- word.add_assoc, <- word.ring_morph_add in H
             end.
      cbn -[scalar] in H2.

      repeat straightline'.
      all: try ecancel_assumption.

      split; auto.

      (* this needs to be done before introducing the following evars *)
      eassert ((_ ⋆ Rout) m4) by ecancel_assumption.
      destruct H15 as [mq[mr[Hsplit[Hout HRout]]]].

      eexists. split; auto.
      split.
      reflexivity.
      eexists. eexists.
      split.
      eassumption.
      eexists.
      exists three_b_words.
      sepsimpl.
      eapply feval_three_b_words.
      simpl.
      eapply three_b_mont_valid.
      eassumption.
      eassert (three_b_words = [word.of_Z _; word.of_Z _ ;word.of_Z _ ; word.of_Z _ ; word.of_Z _ ; word.of_Z _]).
      { cbv [three_b_words three_b_mont]. simpl. eauto. }
      rewrite H16.
      subst v v0 v1 v2 v3 v4.
      cbn -[scalar].
      repeat match goal with
             | |- context[ _ +w _ +w _ ] =>
                 rewrite <- word.add_assoc, <- word.ring_morph_add
             end.
      cbn -[scalar].
      subst a a0 a1 a2 a3.
      (* clear -Hout. *)
      ecancel_assumption_impl.
      ecancel_assumption_impl.
  Qed.

End FromListF.
