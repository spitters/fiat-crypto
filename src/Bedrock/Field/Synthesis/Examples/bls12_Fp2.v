Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.felem_copy_p224.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Coq.Strings.String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section bls12_Fp2.

    Existing Instances Defaults64.default_parameters Defaults64.default_parameters_ok.

    Existing Instance field_parameters.

    Definition bls12_Fp2_add := (@Fp2_add _ _ _ _ bls12_prime.field_parameters (field_representation ) (snd bls12_add) (snd felem_copy_func)).
    Definition bls12_Fp2_mul := (@Fp2_mul _ _ _ _ bls12_prime.field_parameters (field_representation ) (snd bls12_add) (snd felem_copy_func) (snd bls12_sub) (snd bls12_mul)).
    Definition bls12_Fp2_sub := (@Fp2_sub _ _ _ _ bls12_prime.field_parameters (field_representation ) (snd bls12_sub) (snd felem_copy_func)).

    (*Print rest of functions to C*)
    (* From bedrock2 Require Import ToCString Bytedump.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
    Definition c_mod := (c_module (bls12_Fp2_mul :: nil)).

    Eval compute in c_mod. *)


    Require Import bedrock2.NotationsCustomEntry.
    Require Import bedrock2.WeakestPrecondition.
    Import Syntax BinInt String List.ListNotations.
    Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
    Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
    Require Import Rupicola.Lib.Api.
    Require Import Crypto.Bedrock.Specs.AbstractField.
    Require Import Crypto.Bedrock.Specs.PrimeField.
    Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
    Require Import Crypto.Bedrock.Field.Interface.Compilation2.

    Instance spec_of_bls12_add : spec_of (fst bls12_add).
    Proof.
        exact (@spec_of_add _ _ _ _ _ _ bls12_prime.field_parameters (field_representation)).
    Defined.

    Instance spec_of_bls12_Fp2_add : spec_of (fst bls12_Fp2_add).
    Proof.
        exact (@spec_of_Fp2_add _ _ _ _ _ _ bls12_prime.field_parameters (field_representation)).
    Defined.

    Instance spec_of_bls12_mul : spec_of (fst bls12_mul).
    Proof.
        exact (@spec_of_F_mul _ _ _ _ _ _ bls12_prime.field_parameters (field_representation )).
    Defined.

    Instance spec_of_bls12_Fp2_mul : spec_of (fst bls12_Fp2_mul).
    Proof.
        exact (@spec_of_Fp2_mul _ _ _ _ _ _ bls12_prime.field_parameters (field_representation )).
    Defined.

    Instance spec_of_bls12_sub : spec_of (fst bls12_sub).
    Proof.
        exact (@spec_of_F_sub _ _ _ _ _ _ bls12_prime.field_parameters (field_representation )).
    Defined.

    Instance spec_of_bls12_Fp2_sub : spec_of (fst bls12_Fp2_sub).
    Proof.
        exact (@spec_of_Fp2_sub _ _ _ _ _ _ bls12_prime.field_parameters (field_representation )).
    Defined.

    Instance spec_of_bls12_felem_copy : spec_of ((@felem_copy bls12_prime.field_parameters)).
    Proof.
        exact (@spec_of_felem_copy _ _ _ _ _ _ field_parameters (field_representation )).
    Defined.
(* 
    Lemma bls12_Fp2_add_ok : program_logic_goal_for_function! bls12_Fp2_add.
    Proof.
        epose proof (Fp2_add_ok). eapply H.
        Unshelve. all: try eapply Defaults64.default_parameters_ok; auto.
    Qed.

    Lemma bls12_Fp2_sub_ok : program_logic_goal_for_function! bls12_Fp2_sub.
    Proof.
        epose proof (Fp2_sub_ok). cbv [bls12_Fp2_sub]. eapply (H (snd felem_copy_func) (snd bls12_sub)).
        Unshelve. all: try eapply Defaults64.default_parameters_ok; auto.
    Qed.

    Lemma bls12_Fp2_mul_ok : program_logic_goal_for_function! bls12_Fp2_mul.
    Proof.
        epose proof (Fp2_mul_ok). eapply H.
        Unshelve. all: try eapply Defaults64.default_parameters_ok; auto.
        Set Printing All. econstructor. admit.
    Admitted.  *)

End bls12_Fp2.
(* 
    From bedrock2 Require Import ToCString Bytedump.
    Definition c_mod := (c_module (bls12_Fp2_mul :: nil)).

    Eval cbv in c_mod. *)
