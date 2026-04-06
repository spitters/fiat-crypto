(** * BN446 Power-by-u -- thin instantiation of BLS12_PowGeneric.
    Computes f^{u} where u = 0x4000000000000000001000000001 (111 bits, 2 words).
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
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
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_PowGeneric.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BN446_PowU.

    (* === BN446 Fp-level setup === *)
    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bn446_M_pos : positive := Eval vm_compute in (Z.to_pos bn446_prime.m).

    Instance bn446_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn446_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn446_mul"; PrimeField.add := "bn446_add";
      PrimeField.sub := "bn446_sub"; PrimeField.opp := "bn446_opp";
      PrimeField.square := "bn446_square"; PrimeField.scmula24 := "bn446_scmula24";
      PrimeField.inv := "bn446_inv"; PrimeField.from_bytes := "bn446_from_bytes";
      PrimeField.to_bytes := "bn446_to_bytes"; PrimeField.select_znz := "bn446_select_znz";
      PrimeField.felem_copy := "bn446_felem_copy"; PrimeField.from_word := "bn446_from_word";
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

    (* === Extension field constants === *)
    Let bn446_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
    Let bn446_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 2.
    Let bn446_xi_im : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 3.

    (* Extension field instances matching BLS12_PowGeneric *)
    Instance bn446_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ext_Fp12_params bn446_beta bn446_xi_re bn446_xi_im "bn446_".
    Instance bn446_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ext_Fp12_rep bn446_beta bn446_xi_re bn446_xi_im "bn446_".

    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').

    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn446_Fp12_rep') AbstractField.un_square.
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bn446_Fp12_rep') AbstractField.bin_mul.
    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bn446_Fp12_rep').

    (* Spec for bn446_Fp12_pow_u: computes base^{u} *)
    Instance spec_of_pow_u : spec_of "bn446_Fp12_pow_u" :=
      fnspec! "bn446_Fp12_pow_u" (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆
           (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    (* NOTE: BN446 uses a 2-word u parameter (111 bits), unlike BN254's single-word u.
       The generic pow_ok lemma from BLS12_PowGeneric may need adaptation for 2-word
       parameters. For now we state the correctness theorem; the proof requires
       either extending pow_ok or writing a custom loop invariant. *)
    Lemma bn446_Fp12_pow_u_ok :
      forall functions
        (EnvContains : map.get functions "bn446_Fp12_pow_u" =
          Some (snd BN446_Pairing.bn446_Fp12_pow_u))
        (HFsqr : spec_of_Fp12_sqr functions)
        (HFmul : spec_of_Fp12_mul functions)
        (HFcopy : spec_of_Fp12_felem_copy functions),
      spec_of_pow_u functions.
    Proof.
      intros.
      (* BN446 pow_u uses a 2-word parameter (111 bits). The generic pow_ok
         from BLS12_PowGeneric uses expr.literal (single-word) so it cannot
         be applied directly. The function body uses a 2-word stack storage
         approach defined in BN446_Pairing.v. A dedicated 2-word pow_ok
         variant would be needed for the full WP proof. *)
      Admitted.

End BN446_PowU.
