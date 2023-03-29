Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAdd.
Require Import Coq.Strings.String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.


Section bls12_Fp2.

    Existing Instances Defaults64.default_parameters Defaults64.default_parameters_ok.

    Local Notation F := (F M_pos).

    Instance prime_parameters : PrimeParameters := prime_parameters.
    Instance field_names : FieldNames := field_names.

    Instance field_parameters : Field.FieldParameters F.
    Proof.
        exact bls12_prime.field_parameters.
    Defined.

    (* Instance field_parameters : Field.FieldParameters. *)
    (* Proof. *)
    (*     exact (@Field.prime_field_parameters prime_field_parameters). *)
    (* Defined. *)

    Instance field_representation : @Field.FieldRepresentation F field_parameters _ _ _ _.
    Proof.
        exact (WordByWordMontgomery.field_representation m).
    Defined.

    Check @ladderstep_body. (*Give Proper Name!!!!!!!!*)

    Definition bls12_G1_add := ladderstep_body.
    (*make Field.field_representation from rep in WordByWordMontgomery.*)

    Definition mpos : positive.
    Proof.
        destruct bls12_Fp2.prime_parameters. eapply M_pos.
    Defined.

    (*hard-code curve-defining parameter b*)
    Definition b := 4.
    Definition three_b := 12.
    Definition uw := (uweight 64).
    Definition n := felem_size_in_words.
    Definition three_b_list := Partition.partition uw n three_b.
    Definition word := BasicC64Semantics.word.
    Definition three_b_mont := @WordByWordMontgomery.to_montgomerymod 64 n m (@m' _ 64) three_b_list.
    Definition three_b_words := List.map (@word.of_Z 64 word) three_b_mont.

    Instance spec_of_bls12_add : spec_of (fst bls12_add).
    Proof. exact spec_of_add. Defined.
        (* exact (@spec_of_add _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    Instance spec_of_bls12_sub : spec_of (fst bls12_sub).
    Proof. exact spec_of_sub. Defined.
        (* exact (@spec_of_sub _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    Instance spec_of_bls12_mul : spec_of (fst bls12_mul).
    Proof. exact spec_of_mul. Defined.
        (* exact (@spec_of_mul _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    (* Instance spec_of_bls12_square : spec_of (fst bls12_square).
    Proof. exact spec_of_square. Defined. *)

    Instance spec_of_G1_add : spec_of "ladderstep".
    Proof.
        exact (spec_of_ladderstep three_b_words).
    Defined.

    Definition three_b_F : F.
    Proof.
        exact (ModularArithmetic.F.of_Z M_pos three_b).
    Defined.

    Instance spec_of_from_list : spec_of from_list.
    Proof.
        exact (spec_of_from_list three_b_F).
    Defined.

    Lemma bls12_G1_ok : program_logic_goal_for_function! bls12_G1_add. (*Why does this take 7 minutes??!?!?*)
    pose proof ladderstep_correct. cbv [spec_of_G1_add].
    cbv [bls12_G1_add].
    cbv [program_logic_goal_for]. intros.
    eapply H.
        1: simpl; auto.
        3: cbv [spec_of_bls12_mul] in H1; apply H1.
        3: cbv [spec_of_bls12_add] in H4; apply H4.
        3: cbv [spec_of_bls12_sub] in H13; apply H13.
        2: {
            cbv [__rupicola_program_marker]. auto.
        }
        2: {
            cbv [CurveAdd.spec_of_from_list]. cbv [spec_of_from_list] in H0.
            assert (three_b_F = feval three_b_words).
            {
                cbv [Representation.eval_words eval_trans three_b_F].
                Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
                pose proof (three_b_mont_mod).
                assert (three_b_words = bls12_Fp2.three_b_words).
                {
                    cbv [bls12_Fp2.three_b_words three_b_words]. eapply f_equal.
                    cbv [bls12_Fp2.three_b_mont three_b_mont bls12_Fp2.three_b_list].
                    cbv. reflexivity.
                }
                rewrite <- H35.
                (* unfold feval. *)
                cbv [feval].
                (* rewrite H34. *)
                unfold eval_trans.
                simpl.
                apply f_equal.
                (* cbv [word] in H34. *)
                assert (@M bls12_prime.prime_parameters = m).
                {
                    simpl. cbv [M]. cbv [m]. cbv [M_pos]. simpl. reflexivity.
                }
                rewrite H36 in H34.
                unfold bls12_Fp2.three_b.
                unfold eval_trans.
                simpl in H34.
                rewrite H34.
                cbv [three_b_list]. rewrite eval_partition; [| eapply uwprops].
                2 : {
                    clear H H1 H2 H4 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33.
                    clear H34 H35 H36. lia.
                }
                clear H H1 H2 H4 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33.
                cbv [three_b bls12_Fp2.three_b]. rewrite Zmod_small. 1: reflexivity. cbv. intuition subst. easy.
            }
            rewrite H34 in H0.
            eapply H0.
        }
        clear H H1 H2 H4 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33.
        cbv [CompilationAbstract.maybe_bounded bounded_by loose_bounds bls12_Fp2.three_b_words].
        (* eassert (my_field_representation = _). *)
        (* { *)
        (*     cbv [my_field_representation]. eauto.  *)
        (* } *)
        (* rewrite H. *)
        eassert (bls12_Fp2.field_representation = _).
        {
            cbv [bls12_Fp2.field_representation]. auto.
        }
        cbv [bls12_Fp2.field_representation]. remember (List.map word.of_Z bls12_Fp2.three_b_mont) as eyy.
        simpl. subst eyy.


        assert (three_b_mont = bls12_Fp2.three_b_mont).
        {
            pose proof (three_b_mont_eq). rewrite H1.
            cbv [bls12_Fp2.three_b_mont bls12_Fp2.three_b_list bls12_Fp2.three_b].
            cbv [three_b_list three_b].
            assert (n = bls12_Fp2.n).
            {
                cbv [bls12_Fp2.n]. cbv [n]. reflexivity.
            }
            rewrite <- H2.
            assert (bls12_Fp2.uw = uw).
            {
                cbv [bls12_Fp2.uw]. cbv [uw]. reflexivity.
            }
            rewrite H4. reflexivity.
        }
        rewrite <- H1.
        rewrite unsigned_of_Z_valid.

        2: cbv [n felem_size_in_words]; simpl.
        all: eapply three_b_mont_valid.
Qed.

End bls12_Fp2.
    (* From bedrock2 Require Import ToCString Bytedump.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
    Definition c_mod := (c_module (bls12_mul :: nil)).

    Redirect "blstest.c" Eval compute in c_mod. *)
