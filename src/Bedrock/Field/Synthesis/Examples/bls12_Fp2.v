Require Import Coq.Strings.String.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section bls12_Fp2.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok
      bls12_prime_parameters
      (* bls12_field_parameters *)
      bls12_field_names
      bls12_field_representation.

    Local Notation Fp2 := ((F M_pos) * (F M_pos))%type.

    Instance bls12_Fp2_field_parameters : FieldParameters Fp2 := Fp2_field_parameters.
    Instance bls12_Fp2_field_representation : FieldRepresentation Fp2 := Fp2_field_representation.

    Instance spec_of_bls12_add : spec_of add := spec_of_F_add.
    Instance spec_of_bls12_mul : spec_of mul := spec_of_F_mul.
    Instance spec_of_bls12_sub : spec_of sub := spec_of_F_sub.
    Instance spec_of_bls12_felem_copy : spec_of felem_copy := spec_of_F_felem_copy.
    Instance spec_of_bls12_select_znz : spec_of select_znz := spec_of_F_select_znz.

    Let prefix := "bls12_Fp2".
    Instance bls12_Fp2_field_names : FieldNames Fp2 := field_names_prefixed Fp2 prefix.

    Instance spec_of_bls12_Fp2_add : spec_of (add (F:=Fp2)) := spec_of_Fp2_add.
    Instance spec_of_bls12_Fp2_mul : spec_of (mul (F:=Fp2)) := spec_of_Fp2_mul.
    Instance spec_of_bls12_Fp2_sub : spec_of (sub (F:=Fp2)) := spec_of_Fp2_sub.

    (*Print rest of functions to C*)
    (* From bedrock2 Require Import ToCString Bytedump.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
    Definition c_mod := (c_module (bls12_Fp2_mul :: nil)).

    Eval compute in c_mod. *)

    Lemma bls12_Fp2_add_ok : program_logic_goal_for_function! Fp2_add.
    Proof.
        eapply Fp2_add_ok.
        Unshelve. all: try eapply Defaults64.default_parameters_ok; auto.
    Qed.

    Lemma bls12_Fp2_sub_ok : program_logic_goal_for_function! Fp2_sub.
    Proof.
        eapply Fp2_sub_ok.
        (* epose proof (Fp2_sub_ok). cbv [bls12_Fp2_sub]. eapply (H (snd felem_copy_func) (snd bls12_sub)). *)
        Unshelve. all: try eapply Defaults64.default_parameters_ok; auto.
    Qed.

    Lemma bls12_Fp2_mul_ok : program_logic_goal_for_function! Fp2_mul.
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
