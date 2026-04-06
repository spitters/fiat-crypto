(** * BN446 Pairing Helper WP Proofs
    Standalone WP correctness proofs for pairing helper functions
    defined in BN446_Pairing.v:
    - C1: bn446_Fp2_mul_fp (multiply Fp2 by Fp scalar)
    - C3: bn446_load_gamma1_p2
    - C4: bn446_load_gamma2_p2
    - C5: bn446_load_w_frob_p2_c1
    - C2: bn446_make_line
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn446_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn446_prime_certif.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn446_felem_copy.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN446_Pairing.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BN446_PairingHelpers.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bn446_M_pos : positive := Eval vm_compute in (Z.to_pos bn446_prime.m).

    Instance bn446_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn446_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn446_mul";
      PrimeField.add := "bn446_add";
      PrimeField.sub := "bn446_sub";
      PrimeField.opp := "bn446_opp";
      PrimeField.square := "bn446_square";
      PrimeField.scmula24 := "bn446_scmula24";
      PrimeField.inv := "bn446_inv";
      PrimeField.from_bytes := "bn446_from_bytes";
      PrimeField.to_bytes := "bn446_to_bytes";
      PrimeField.select_znz := "bn446_select_znz";
      PrimeField.felem_copy := "bn446_felem_copy";
      PrimeField.from_word := "bn446_from_word";
      PrimeField.from_list := "bn446_from_list";
    |}.

    Instance bn446_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn446. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Instance bn446_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn446_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn446_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn446_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn446_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn446_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn446_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn446_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn446_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn446_frep |}.

    Instance bn446_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn446_Fp_rep] in *.
      cbv [Field.bounded_by bn446_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let bn446_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
    Let bn446_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 2.
    Let bn446_xi_im : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 3.

    Let fp2_prefix := "bn446_Fp2_".
    Let fp6_prefix := "bn446_Fp6_".
    Let fp12_prefix := "bn446_Fp12_".

    Instance bn446_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bn446_beta "bn446_") in exact v).
    Instance bn446_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bn446_beta "bn446_") in exact v).
    Instance bn446_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bn446_beta bn446_xi_re bn446_xi_im "bn446_") in exact v).
    Instance bn446_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bn446_beta bn446_xi_re bn446_xi_im "bn446_") in exact v).
    Instance bn446_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bn446_beta bn446_xi_re bn446_xi_im "bn446_") in exact v).
    Instance bn446_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bn446_beta bn446_xi_re bn446_xi_im "bn446_") in exact v).

    (* Placeholder: WP proofs for helper functions will follow the same pattern
       as BN254_PairingHelpers.v, adapted for 7-limb Fp elements. *)

End BN446_PairingHelpers.
