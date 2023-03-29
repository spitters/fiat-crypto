Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.felem_copy_p224.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Coq.Strings.String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.

Import Syntax BinInt String List.ListNotations.

Section bls12_Fp2.

    Existing Instances Defaults64.default_parameters Defaults64.default_parameters_ok.

    Existing Instance prime_parameters.
    Let prefix := "bls12_Fp2".

    Instance F_names : FieldNames := field_names.
    Instance Fp2_names : FieldNames := field_names_prefixed prefix.
    (* Check Fp2_representation. *)

    Definition bls12_Fp2_add := (@Fp2_add _ _ _ _ bls12_prime.prime_parameters F_names (field_representation ) (snd bls12_add) (snd felem_copy_func) Fp2_names).
    Definition bls12_Fp2_mul := (@Fp2_mul _ _ _ _ bls12_prime.prime_parameters F_names (field_representation ) (snd bls12_add) (snd felem_copy_func) (snd bls12_sub) (snd bls12_mul) Fp2_names).
    Definition bls12_Fp2_sub := (@Fp2_sub _ _ _ _ bls12_prime.prime_parameters F_names (field_representation ) (snd bls12_sub) (snd felem_copy_func) Fp2_names).

    (*Print rest of functions to C*)
    (* From bedrock2 Require Import ToCString Bytedump.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
    Definition c_mod := (c_module (bls12_Fp2_mul :: nil)).

    Eval compute in c_mod. *)

    Instance spec_of_bls12_add : spec_of (fst bls12_add).
    Proof.
        exact (@spec_of_add _ _ _ _ _ _ bls12_prime.prime_parameters F_names (field_representation)).
    Defined.

    Instance spec_of_bls12_Fp2_add : spec_of (fst bls12_Fp2_add).
    Proof.
        exact (@spec_of_Fp2_add _ _ _ _ _ _ bls12_prime.prime_parameters (field_representation) Fp2_names).
    Defined.

    Instance spec_of_bls12_mul : spec_of (fst bls12_mul).
    Proof.
        exact (@spec_of_F_mul _ _ _ _ _ _ bls12_prime.prime_parameters F_names (field_representation )).
    Defined.

    Instance spec_of_bls12_Fp2_mul : spec_of (fst bls12_Fp2_mul).
    Proof.
        exact (@spec_of_Fp2_mul _ _ _ _ _ _ bls12_prime.prime_parameters (field_representation ) Fp2_names).
    Defined.

    Instance spec_of_bls12_sub : spec_of (fst bls12_sub).
    Proof.
        exact (@spec_of_F_sub _ _ _ _ _ _ bls12_prime.prime_parameters F_names (field_representation )).
    Defined.

    Instance spec_of_bls12_Fp2_sub : spec_of (fst bls12_Fp2_sub).
    Proof.
        exact (@spec_of_Fp2_sub _ _ _ _ _ _ bls12_prime.prime_parameters (field_representation ) Fp2_names).
    Defined.

    Instance spec_of_bls12_felem_copy : spec_of ((@felem_copy F_names)).
    Proof.
        exact spec_of_felem_copy. (* (@Field.spec_of_felem_copy _ _ _ _ _ _ (F M_pos) field_parameters F_names (field_representation )). *)
    Defined.

    Lemma bls12_Fp2_add_ok : program_logic_goal_for_function! bls12_Fp2_add.
    Proof.
        eapply Fp2_add_ok.
        Unshelve. all: try eapply Defaults64.default_parameters_ok; auto.
    Qed.

    Lemma bls12_Fp2_sub_ok : program_logic_goal_for_function! bls12_Fp2_sub.
    Proof.
        eapply Fp2_sub_ok.
        (* epose proof (Fp2_sub_ok). cbv [bls12_Fp2_sub]. eapply (H (snd felem_copy_func) (snd bls12_sub)). *)
        Unshelve. all: try eapply Defaults64.default_parameters_ok; auto.
    Qed.

    Lemma bls12_Fp2_mul_ok : program_logic_goal_for_function! bls12_Fp2_mul.
    Proof.
        eapply Fp2_mul_ok.
        (* epose proof (Fp2_mul_ok). eapply H. *)
        Unshelve. all: try eapply Defaults64.default_parameters_ok; auto.
        econstructor.
        (* Do we have a proof that bls12 modulus is prime? *)
        Admitted.

End bls12_Fp2.
(* 
    From bedrock2 Require Import ToCString Bytedump.
    Definition c_mod := (c_module (bls12_Fp2_mul :: nil)).

    Eval cbv in c_mod. *)
