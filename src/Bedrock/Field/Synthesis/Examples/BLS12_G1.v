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
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.

Section bls12_Fp2.

    (* Existing Instances Defaults64.default_parameters Defaults64.default_parameters_ok. *)

    Local Notation F := (F M_pos).

    Existing Instance bls12_prime_parameters.
    Existing Instance bls12_field_names.
    Existing Instance bls12_field_parameters.
    (* Instance prime_parameters : PrimeParameters := bls12_prime_parameters. *)
    (* Instance field_names : FieldNames F := bls12_field_names. *)


    (* Instance field_parameters : FieldParameters F := bls12_field_parameters. *)

    (* Instance field_parameters : Field.FieldParameters. *)
    (* Proof. *)
    (*     exact (@Field.prime_field_parameters prime_field_parameters). *)
    (* Defined. *)

    Existing Instance WordByWordMontgomery.field_representation.

    (* Instance field_representation : @Field.FieldRepresentation F field_parameters _ _ _ _. *)
    (* Proof. *)
    (*     exact (WordByWordMontgomery.field_representation). *)
    (* Defined. *)

    Check @ladderstep_body. (*Give Proper Name!!!!!!!!*)

    Definition bls12_G1_add := ladderstep_body "bls12_three_b".
    (*make Field.field_representation from rep in WordByWordMontgomery.*)

    (* Definition mpos : positive.  *)
    (* Proof. *)
    (*     destruct bls12_Fp2.prime_parameters. eapply M_pos. *)
    (* Defined. *)

    (*hard-code curve-defining parameter b*)
    (* Definition b := 4. *)
    (* Definition three_b := 12. *)
    (* Definition uw := (uweight 64). *)
    (* Definition n := felem_size_in_words. *)
    (* Definition three_b_list := Partition.partition uw n three_b. *)
    (* Definition word := BasicC64Semantics.word. *)
    (* Definition three_b_mont := @WordByWordMontgomery.to_montgomerymod 64 n M (@m' _ 64) three_b_list. *)
    (* Definition three_b_words := List.map (@word.of_Z 64 word) three_b_mont. *)

    Instance spec_of_bls12_add : spec_of (fst bls12_add) := spec_of_add.
    (* Proof. exact spec_of_add. Defined. *)
        (* exact (@spec_of_add _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    Instance spec_of_bls12_sub : spec_of (fst bls12_sub) := spec_of_sub.
    (* Proof. exact spec_of_sub. Defined. *)
        (* exact (@spec_of_sub _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    Instance spec_of_bls12_mul : spec_of (fst bls12_mul) := spec_of_mul.
    (* Proof. exact spec_of_mul. Defined. *)
        (* exact (@spec_of_mul _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    (* Instance spec_of_bls12_square : spec_of (fst bls12_square).
    Proof. exact spec_of_square. Defined. *)

    Instance spec_of_G1_add : spec_of "curve_add".
    Proof.
        exact (spec_of_ladderstep three_b_words).
    Defined.

    Definition three_b_F : F.
    Proof.
        exact (ModularArithmetic.F.of_Z M_pos three_b).
    Defined.

    Instance spec_of_three_b : spec_of "bls12_three_b" := spec_of_from_list three_b_F "bls12_three_b".

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
            cbv [CurveAdd.spec_of_three_b spec_of_from_list]. cbv [spec_of_three_b spec_of_from_list] in H0.
            assert (three_b_F = feval three_b_words).
            {
                cbv [Representation.eval_words eval_trans three_b_F].
                pose proof (three_b_mont_mod).
                cbv [feval].
                unfold eval_trans.
                simpl.
                apply f_equal.
                unfold three_b.
                unfold eval_trans.
                simpl in H34.
                rewrite H34.
                cbv [three_b_list]. rewrite eval_partition; [| eapply uwprops].
                2: reflexivity.
                cbv [three_b]. rewrite Zmod_small. 1: reflexivity. cbv. intuition subst. easy.
            }
            rewrite <- H34.
            apply H0.
        }
        cbv [maybe_bounded bounded_by loose_bounds three_b_words].
        remember (List.map word.of_Z three_b_mont) as eyy.
        simpl. subst eyy.


        rewrite unsigned_of_Z_valid.

        2: cbv [n felem_size_in_words]; simpl.
        all: eapply three_b_mont_valid.
Qed.

End bls12_Fp2.
    (* From bedrock2 Require Import ToCString Bytedump.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
    Definition c_mod := (c_module (bls12_mul :: nil)).

    Redirect "blstest.c" Eval compute in c_mod. *)
