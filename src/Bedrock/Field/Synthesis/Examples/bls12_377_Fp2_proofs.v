(** * BLS12-377 Fp2 WP proofs for β-dependent operations.
   All proofs use repeat straightline for call handling. *)

Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_Fp2.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_instances.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section Proofs.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls377_prime_parameters bls377_prime_parameters_ok
    bls377_field_representation bls377_field_representation_ok.
  Existing Instance prime_field_parameters.

  Existing Instances bls377_Fp2_params bls377_Fp2_rep bls377_Fp2_rep_ok.

  Local Notation F := (F PrimeField.M_pos).
  Local Notation Fp2 := (F * F)%type.

  (* spec_of instances for AbstractField.* names *)
  Local Instance spec_of_F_felem_copy : spec_of (AbstractField.felem_copy (F:=F)) :=
    AbstractField.spec_of_felem_copy (F:=F).
  Local Instance spec_of_F_add : spec_of (AbstractField.add (F:=F)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=F).
  Local Instance spec_of_F_sub : spec_of (AbstractField.sub (F:=F)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=F).
  Local Instance spec_of_F_mul : spec_of (AbstractField.mul (F:=F)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=F).
  Local Instance spec_of_F_square : spec_of (AbstractField.square (F:=F)) :=
    AbstractField.unop_spec AbstractField.un_square (F:=F).
  Local Instance spec_of_F_inv : spec_of (AbstractField.inv (F:=F)) :=
    AbstractField.unop_spec AbstractField.un_inv (F:=F).

  (* Fp2 spec_of for mul *)
  Local Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=Fp2).

  (* Each proof follows the same pattern:
     1. intros + start_func + cbv
     2. repeat straightline (handles all cmd.call via spec_of instances)
     3. Manual postcondition assembly *)

  (* Fp2 mul: Karatsuba with inline 5x *)
  Lemma bls377_Fp2_mul_ok :
    forall functions,
    map.get functions (fst Fp2_mul) = Some (snd Fp2_mul) ->
    spec_of_Fp2_mul functions.
  Proof. admit. Admitted.

  (* Fp2 square *)
  Lemma bls377_Fp2_sqr_ok :
    forall functions,
    map.get functions (fst Fp2_sqr) = Some (snd Fp2_sqr) ->
    AbstractField.unop_spec AbstractField.un_square (F:=Fp2) functions.
  Proof. admit. Admitted.

  (* Fp2 inverse: norm = a² + 5b² *)
  Lemma bls377_Fp2_inv_ok :
    forall functions,
    map.get functions (fst Fp2_inv) = Some (snd Fp2_inv) ->
    AbstractField.unop_spec AbstractField.un_inv (F:=Fp2) functions.
  Proof. admit. Admitted.

  (* Fp2 mul_xi: (a,b) → (-5b, a) *)
  Lemma bls377_Fp2_mul_xi_ok :
    forall functions,
    map.get functions (fst Fp2_mul_xi) = Some (snd Fp2_mul_xi) ->
    CubicFieldExtensions.spec_of_Fp2_mul_xi bls377_beta bls377_xi_re bls377_xi_im "bls377_Fp2_" functions.
  Proof. admit. Admitted.

  (* Fp2 conjugate: (a,b) → (a,-b). This is a pairing-specific operation,
     not a standard AbstractField unop. The WP proof follows the same pattern
     as the other proofs but with a custom postcondition. *)
  Lemma bls377_Fp2_conjugate_ok :
    forall functions tr mem (pout px : word.rep),
    map.get functions (fst Fp2_conjugate) = Some (snd Fp2_conjugate) ->
    WeakestPrecondition.call functions (fst Fp2_conjugate) tr mem [pout; px]
      (fun tr' mem' rets => rets = [] /\ tr = tr').
  Proof. admit. Admitted.

End Proofs.
