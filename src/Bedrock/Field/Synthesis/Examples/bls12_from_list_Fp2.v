Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_Fp2.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Specs.AbstractField.
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
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.

Section FromListFp2.

    Existing Instances Defaults64.default_parameters
    Defaults64.default_parameters_ok.

    Instance bls12_Fp2_parameters : AbstractField.FieldParameters.
    Proof.
        exact (@Fp2_parameters bls12_prime.field_parameters).
    Defined.

    Check @AbstractField.FieldRepresentation.
    Instance field_representation : (@AbstractField.FieldRepresentation bls12_Fp2_parameters _ _ _ _).
    Proof.
        exact (@Fp2_representation _ _ _ _ bls12_prime.field_parameters (@field_representation _ _ _ _ (bls12_prime.field_parameters) (@M bls12_prime.field_parameters))).
    Defined.

    (*curve-defining parameter b*)
    Definition br := 4.
    Definition bi := 4.
    Definition three_br := 12.
    Definition three_bi := 12.
    Definition uw := (uweight 64).
    Definition n := (@WordByWordMontgomery.n m 64).
    Definition three_br_list := Partition.partition uw n three_br.
    Definition three_bi_list := Partition.partition uw n three_bi.
    Definition word := BasicC64Semantics.word.
    Definition three_br_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n m (@m' bls12_prime.field_parameters 64) three_br_list).
    Definition three_bi_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n m (@m' bls12_prime.field_parameters 64) three_bi_list).
    Definition three_br_words := List.map (@word.of_Z 64 word) three_br_mont.
    Definition three_bi_words := List.map (@word.of_Z 64 word) three_bi_mont.
    Definition wo := @word.of_Z 64 word 0.

    Check WordByWordMontgomery.r'.
    Existing Instance bls12_prime.field_parameters.
    (*Few lemmas about curve parameters*)
    Lemma r'_correct : (2 ^ 64 * (@WordByWordMontgomery.r' 64 bls12_prime.field_parameters) mod M = 1).
    Proof.
        auto.
    Qed.

    Lemma m'_correct : ((M * WordByWordMontgomery.m' M 64) mod 2 ^ 64 = -1 mod 2 ^ 64).
    Proof.
        cbv [WordByWordMontgomery.m']. cbv [WordByWordMontgomery.r]. assert (m = M) by auto. rewrite <- H.
            assert (m = (-1) * (-m))%Z by auto.
            remember (ModInv.Z.modinv (- m) (2 ^ 64)) as x.
            rewrite H0. subst x. rewrite H. rewrite <- Z.mul_assoc.
            rewrite Z.mul_mod.
            1: {
                pose proof (ModInv.Z.modinv_correct (- M) (2 ^ 64)).
                assert (0 < 2 ^ 64) by lia.
                specialize (H1 H2).
                assert (Z.gcd (Z.abs (-M)) (2 ^ 64) = 1) by auto.
                specialize (H1 H3).
                destruct H1.
                rewrite H1. rewrite <- Z.mul_mod; try lia.
            }
            lia.
    Qed.

    Lemma M_small : (M < (2 ^ 64) ^ Z.of_nat (WordByWordMontgomery.n M 64)).
    Proof.
        cbv [M WordByWordMontgomery.n]. simpl. lia.
    Qed.

    Lemma bw_big : 0 < 64.
    Proof. lia. Qed.

    Lemma m_big : 1 < m.
    Proof.
        cbv. auto.
    Qed.

    Lemma n_nz : n <> 0%nat.
    Proof.
        cbv [n felem_size_in_words]; simpl. cbv [WordByWordMontgomery.n]; simpl; lia.
    Qed.

    Lemma m_small : (m < (2 ^ 64) ^ Z.of_nat (n)).
    Proof.
        cbv [n felem_size_in_words m]. simpl. lia.
    Qed.

    Check WordByWordMontgomery.to_montgomerymod_correct.

    Definition from_mont_correct := WordByWordMontgomery.from_montgomerymod_correct 64 n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small.
    Definition to_mont_correct :=  WordByWordMontgomery.to_montgomerymod_correct 64 n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small.

    Ltac param_hammer := cbv [m m' M M_pos r' n]; simpl; try eapply M_small; try eapply m'_correct; try eapply r'_correct; try lia; auto.

    (*Move this lemma elsewhere*)
    Lemma unsigned_of_Z_valid : forall (l : list Z), WordByWordMontgomery.valid 64 n m l -> List.map word.unsigned (List.map (@word.of_Z 64 word) l) = l.
    Proof.
        intros.
        erewrite Util.map_unsigned_of_Z. eapply MaxBounds.map_word_wrap_bounded'.
        1: eapply BasicLemmas.ZRange.is_tighter_than_bool_Reflexive.
        eapply valid_max_bounds. eapply H.
    Qed.

    Lemma three_br_mont_eq : three_br_mont = (@WordByWordMontgomery.to_montgomerymod 64 n m (@m' bls12_prime.field_parameters 64) three_br_list).
    Proof. vm_compute; auto. Qed.

    Lemma three_bi_mont_eq : three_bi_mont = (@WordByWordMontgomery.to_montgomerymod 64 n m (@m' bls12_prime.field_parameters 64) three_bi_list).
    Proof. vm_compute; auto. Qed.

    Lemma three_br_list_valid : WordByWordMontgomery.valid 64 n m three_br_list.
    Proof.
        split.
        1: {
            eapply WordByWordMontgomery.WordByWordMontgomery.small_m_enc; try lia; cbv [three_br]; try lia.
            cbv [n felem_size_in_words]. simpl; lia.
        }
        unfold three_br_list.
        erewrite <- WordByWordMontgomery.WordByWordMontgomery.m_enc_correct_montgomery; try lia; cbv [three_br m]; try lia.
        cbv [n felem_size_in_words]. simpl; lia.
    Qed.

    Lemma three_bi_list_valid : WordByWordMontgomery.valid 64 n m three_bi_list.
    Proof.
        split.
        1: {
            eapply WordByWordMontgomery.WordByWordMontgomery.small_m_enc; try lia; cbv [three_bi]; try lia.
            cbv [n felem_size_in_words]. simpl; lia.
        }
        unfold three_bi_list.
        erewrite <- WordByWordMontgomery.WordByWordMontgomery.m_enc_correct_montgomery; try lia; cbv [three_bi m]; try lia.
        cbv [n felem_size_in_words]. simpl; lia.
    Qed.

    Lemma three_br_mont_valid : WordByWordMontgomery.valid 64 n m three_br_mont.
    Proof.
        rewrite three_br_mont_eq.
        eapply to_mont_correct.
        eapply three_br_list_valid.
    Qed.

    Lemma three_bi_mont_valid : WordByWordMontgomery.valid 64 n m three_bi_mont.
    Proof.
        rewrite three_bi_mont_eq.
        eapply to_mont_correct.
        eapply three_bi_list_valid.
    Qed.

    Lemma three_br_mont_mod : (WordByWordMontgomery.from_montgomerymod 64
            (WordByWordMontgomery.n M 64) M (WordByWordMontgomery.m' M 64)
            (List.map word.unsigned three_br_words)) = three_br_list.
    Proof.
        cbv [three_br_words]. rewrite three_br_mont_eq. eapply eval_inj_list.
        2: eapply three_br_list_valid.
        1: {
            eapply from_mont_correct.
            erewrite unsigned_of_Z_valid; eapply to_mont_correct; eapply three_br_list_valid.
        }
        erewrite unsigned_of_Z_valid.
        2: eapply to_mont_correct; eapply three_br_list_valid.
        erewrite from_to_mont_inv; auto.
        1: eapply r'_correct.
        1: lia.
        1: cbv [n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; simpl; lia.
        1: cbv [m n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; lia.
        1: cbv [m]; lia.
        eapply three_br_list_valid.
    Qed.

    Lemma three_bi_mont_mod : (WordByWordMontgomery.from_montgomerymod 64
        (WordByWordMontgomery.n M 64) M (WordByWordMontgomery.m' M 64)
        (List.map word.unsigned three_bi_words)) = three_bi_list.
    Proof.
        cbv [three_bi_words]. rewrite three_bi_mont_eq. eapply eval_inj_list.
        2: eapply three_bi_list_valid.
        1: {
            eapply from_mont_correct.
            erewrite unsigned_of_Z_valid; eapply to_mont_correct; eapply three_bi_list_valid.
        }
        erewrite unsigned_of_Z_valid.
        2: eapply to_mont_correct; eapply three_bi_list_valid.
        erewrite from_to_mont_inv; auto.
        1: eapply r'_correct.
        1: lia.
        1: cbv [n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; simpl; lia.
        1: cbv [m n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; lia.
        1: cbv [m]; lia.
        eapply three_bi_list_valid.
    Qed.

    Definition from_list_func : Syntax.func := (from_list, (["out"], (nil : list string), bedrock_func_body:(
      coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_br_mont 0)));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (nth 1 three_br_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (nth 2 three_br_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (nth 3 three_br_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (nth 4 three_br_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (nth 5 three_br_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (48))) (nth 0 three_bi_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (56))) (nth 1 three_bi_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (64))) (nth 2 three_bi_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (72))) (nth 3 three_bi_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (80))) (nth 4 three_bi_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (88))) (nth 5 three_bi_mont 0))
    ))).

    (* From bedrock2 Require Import ToCString Bytedump.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
    Definition c_mod := (c_module (FromListFp2.from_list_func :: nil)).

    Eval compute in c_mod. *)

    Definition three_b_Fp2 : F.
    Proof.
        exact (ModularArithmetic.F.of_Z M_pos three_br,ModularArithmetic.F.of_Z M_pos three_bi).
    Defined.

    Instance spec_of_from_list : spec_of (from_list).
    Proof.
        exact (@spec_of_from_list _ _ _ _ _ _ bls12_Fp2_parameters field_representation three_b_Fp2) .
    Defined.

    Ltac collect H1 H2 := let Hnew := (fresh "Hnew") in
    eassert (Hnew : id (fun m => (_ m) /\ (_ m)) _) by (cbv [id]; split; [eapply H1| eapply H2]); clear H1 H2.

    Local Infix "+w" := word.add (at level 80).
    Local Infix "*w" := word.mul (at level 70).

    Lemma felem_copy_ok : program_logic_goal_for_function! from_list_func. (*Why does this take 5 minutes???!???*)
    Proof.
        cbv [spec_of_from_list AbstractField.spec_of_from_list]. cbv [program_logic_goal_for].
        intros.
        
        cbv [from_list_func]. simpl.
        repeat straightline.

        cbv [FElem Bignum.Bignum] in H.
        sepsimpl.

        assert (felem_size_in_words= 12)%nat by auto.
        rewrite H1 in H; clear H1.
        do 13 (destruct outold; try discriminate). clear H.
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
        rewrite Hlist in H0; eapply array_append_R' in H0. rewrite H in H0. rewrite <- Heqw2 in H0.
        rewrite Hlist in H0; eapply array_append_R' in H0. rewrite H in H0. rewrite <- Heqw2 in H0.
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

        do 4 straightline'.
        assert (Htemp : 8 + 40 = 48) by auto.
        repeat rewrite word_add_assoc in H6. rewrite Htemp in H6. clear Htemp.
        1: ecancel_assumption.

        do 4 straightline'.
        assert (Htemp : 8 + 48 = 56) by auto.
        repeat rewrite word_add_assoc in H7. rewrite Htemp in H7. clear Htemp.
        1: ecancel_assumption.

        do 4 straightline'.
        assert (Htemp : 8 + 56 = 64) by auto.
        repeat rewrite word_add_assoc in H8. rewrite Htemp in H8. clear Htemp.
        1: ecancel_assumption.

        do 4 straightline'.
        assert (Htemp : 8 + 64 = 72) by auto.
        repeat rewrite word_add_assoc in H9. rewrite Htemp in H9. clear Htemp.
        1: ecancel_assumption.

        do 4 straightline'.
        assert (Htemp : 8 + 72 = 80) by auto.
        repeat rewrite word_add_assoc in H10. rewrite Htemp in H10. clear Htemp.
        1: ecancel_assumption.

        do 4 straightline'.
        assert (Htemp : 8 + 80 = 88) by auto.
        repeat rewrite word_add_assoc in H11. rewrite Htemp in H11. clear Htemp.
        1: ecancel_assumption.

        repeat straightline. split; auto.
        exists (three_br_words ++ three_bi_words).
        split.
        2: split; [auto| split].

        3: {
            cbv [FElem Bignum.Bignum].
            eapply (sep_assoc _ _ Rout). sepsimpl.
            1: auto.
            eassert (three_br_words = [word.of_Z _; word.of_Z _ ;word.of_Z _ ; word.of_Z _ ; word.of_Z _ ; word.of_Z _]).
            {
                cbv [three_br_words three_br_mont]. simpl. eauto.
            }
            eassert (H7i : three_bi_words = [word.of_Z _; word.of_Z _ ;word.of_Z _ ; word.of_Z _ ; word.of_Z _ ; word.of_Z _]).
            {
                cbv [three_bi_words three_bi_mont]. simpl. eauto.
            }
            eassert (three_br_words ++ three_bi_words = _).
            {
                rewrite H13. rewrite H7i. simpl. reflexivity.
            }
            rewrite H14. clear H14 H13 H7i.
            rewrite Hlist.
            subst w1. subst w2.
            epose proof array_append_R'.
            eapply H13.

            remember ((word.of_Z (Memory.bytes_per_word 64))) as w1.
            remember (word.of_Z (Z.of_nat 1)) as w2.
            rewrite H. rewrite <- Heqw2.
            rewrite Hlist. eapply H13. rewrite H. rewrite <- Heqw2.
            rewrite Hlist. eapply H13. rewrite H. rewrite <- Heqw2.
            rewrite Hlist. eapply H13. rewrite H. rewrite <- Heqw2.
            rewrite Hlist. eapply H13. rewrite H. rewrite <- Heqw2.
            rewrite Hlist. eapply H13. rewrite H. rewrite <- Heqw2.
            rewrite Hlist. eapply H13. rewrite H. rewrite <- Heqw2.
            rewrite Hlist. eapply H13. rewrite H. rewrite <- Heqw2.
            rewrite Hlist. eapply H13. rewrite H. rewrite <- Heqw2.
            rewrite Hlist. eapply H13. rewrite H. rewrite <- Heqw2.
            rewrite Hlist. eapply H13. rewrite H. rewrite <- Heqw2.
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
            assert (Htemp : 8 + 40 = 48) by auto. rewrite Htemp. clear Htemp.
            assert (Htemp : 8 + 48 = 56) by auto. rewrite Htemp. clear Htemp.
            assert (Htemp : 8 + 56 = 64) by auto. rewrite Htemp. clear Htemp.
            assert (Htemp : 8 + 64 = 72) by auto. rewrite Htemp. clear Htemp.
            assert (Htemp : 8 + 72 = 80) by auto. rewrite Htemp. clear Htemp.
            assert (Htemp : 8 + 80 = 88) by auto. rewrite Htemp. clear Htemp.
            subst v v1 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9. sepsimpl. clear H H0 H1 H2 H3 H4 H6 H5 H7 H8 H9 H10 H11.

            Fail ecancel_assumption. (*Why??*)

            clear Hword.
            remember ((pout +w word.of_Z 88)) as p10.
            remember ((pout +w word.of_Z 80)) as p9.
            remember ((pout +w word.of_Z 72)) as p8.
            remember ((pout +w word.of_Z 64)) as p7.
            remember ((pout +w word.of_Z 56)) as p6.
            remember ((pout +w word.of_Z 48)) as p11.
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

            
            eassert (Htemp : Naive.wrap _ = v5).
            {
                subst v5; simpl; eauto.
            }
            rewrite Htemp; clear Htemp.

            eassert (Htemp : Naive.wrap _ = v4).
            {
                subst v4; simpl; eauto.
            }
            rewrite Htemp; clear Htemp.

            eassert (Htemp : Naive.wrap _ = v3).
            {
                subst v3; simpl; eauto.
            }
            rewrite Htemp; clear Htemp.

            eassert (Htemp : Naive.wrap _ = v2).
            {
                subst v2; simpl; eauto.
            }
            rewrite Htemp; clear Htemp.

            eassert (Htemp : Naive.wrap _ = v1).
            {
                subst v1; simpl; eauto.
            }
            rewrite Htemp; clear Htemp.

            eassert (Htemp : Naive.wrap _ = v0).
            {
                subst v0; simpl; eauto.
            }
            rewrite Htemp; clear Htemp.
            
            ecancel_assumption.
        }

        1: {
            eapply Prod.path_pair.
            1:{
            pose proof three_br_mont_mod.
            (*Apply lemma!!!*)
            cbv [three_br]. cbv [Representation.eval_words]. cbv [eval_trans].
            eapply f_equal. unfold word in H13.
            assert (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bls12_prime.field_parameters (@WordByWordMontgomery.field_representation _ _ _ _ (bls12_prime.field_parameters) (@M bls12_prime.field_parameters)) (three_br_words ++ three_bi_words) = three_br_words).
            {
                simpl. cbv [QuadraticFieldExtensionsSpecs.fst_felem firstn]. simpl.
                cbv [three_br_words three_br_mont]. simpl. auto.
            }
            Set Printing All.
            cbv [word] in H14.
            Set Printing All.
            cbv [word].
            rewrite H14.
            rewrite H13.
            cbv [three_br_list].
            rewrite eval_partition; [| eapply uwprops; lia].
            cbv [three_br n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]. simpl.
            cbv [uw uweight ModOps.weight]. simpl. rewrite Zmod_small; lia.
            }
            pose proof three_bi_mont_mod.
            (*Apply lemma!!!*)
            cbv [three_bi]. cbv [Representation.eval_words]. cbv [eval_trans].
            eapply f_equal. unfold word in H13.
            assert (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bls12_prime.field_parameters (@WordByWordMontgomery.field_representation _ _ _ _ (bls12_prime.field_parameters) (@M bls12_prime.field_parameters)) (three_br_words ++ three_bi_words) = three_bi_words).
            {
                simpl. cbv [QuadraticFieldExtensionsSpecs.fst_felem firstn]. simpl.
                cbv [three_br_words three_br_mont]. simpl. auto.
            }
            unfold word in H14. 
            unfold word.
            rewrite H14.
            rewrite H13.
            cbv [three_bi_list].
            rewrite eval_partition; [| eapply uwprops; lia].
            cbv [three_bi n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]. simpl.
            cbv [uw uweight ModOps.weight]. simpl. rewrite Zmod_small; lia.
        }

        split.
            - assert (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bls12_prime.field_parameters (@WordByWordMontgomery.field_representation _ _ _ _ (bls12_prime.field_parameters) (@M bls12_prime.field_parameters)) (three_br_words ++ three_bi_words) = three_br_words).
            {
                simpl. cbv [QuadraticFieldExtensionsSpecs.fst_felem firstn]. simpl.
                cbv [three_br_words three_br_mont]. simpl. auto.
            }
            unfold word in *.
            rewrite H13.
            cbv [three_br_words]. rewrite unsigned_of_Z_valid; eapply three_br_mont_valid.
            - assert (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bls12_prime.field_parameters (@WordByWordMontgomery.field_representation _ _ _ _ (bls12_prime.field_parameters) (@M bls12_prime.field_parameters)) (three_br_words ++ three_bi_words) = three_bi_words).
            {
                simpl. cbv [QuadraticFieldExtensionsSpecs.snd_felem firstn]. simpl. auto.
            }
            unfold word in *.
            rewrite H13.
            cbv [three_bi_words]. rewrite unsigned_of_Z_valid; eapply three_bi_mont_valid.
    Qed.
    
    (*Proof finished!! Compile this file and use in implementation of G2!*)

End FromListFp2.




