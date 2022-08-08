Require Import Rupicola.Lib.Api.
(* Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.FLia. *)
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.FieldsUtil.
Require Import Crypto.Algebra.Hierarchy.
Require Import Numbers.DecimalString.

Local Open Scope Z_scope.

Section QuadraticExtension.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}. 
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {prime_field_parameters : PrimeFieldParameters}
          {prime_field_parameters_ok : PrimeFieldParameters_ok}
          {M_mod : M_pos mod 4 =? 3 = true}.

  Lemma M_big : 2 < M_pos.
  Proof.
    lia.
  Qed.

  Local Instance F_parameters : FieldParameters.
  Proof.
    exact (PrimeField.prime_field_parameters).
  Defined.

  Local Instance F_parameters_ok : FieldParameters_ok.
  Proof.
    constructor. destruct prime_field_parameters_ok.
    apply (@F.field_modulo M_pos M_prime).
  Qed.
    

  Context {F_representation : @FieldRepresentation F_parameters _ _ _ _}
          {field_representation_ok : FieldRepresentation_ok}.

  Definition prefix : string := "Fp2_".

  Instance Fp2_parameters : FieldParameters.
  Proof.
      econstructor.
        - exact (zerop2 M_pos).
        - exact (onep2 M_pos).
        - exact (oppp2 M_pos).
        - exact (invp2 M_pos).
        - exact (addp2 M_pos).
        - exact (subp2 M_pos).
        - exact (mulp2 M_pos).
        - exact (divp2 M_pos).
        - eapply eq_dec_Fp2.
        - exact (zerop2 M_pos). (*value of a_24, not relevant for BLS curves*)
        - exact "Fp2_mul".
        - exact "Fp2_add".
        - exact "Fp2_sub".
        - exact "Fp2_opp".
        - exact "Fp2_square".
        - exact "Fp2_scmula_24".
        - exact "Fp2_inv".
        - exact "Fp2_from_bytes".
        - exact "Fp2_to_bytes".
        - exact "Fp2_select".
        - exact "Fp2_felem_copy".
        - exact "Fp2_from_word".
        - exact "Fp2_from_list".
  Defined.

  Instance Fp2_parameters_ok : @FieldParameters_ok Fp2_parameters.
  Proof.
    econstructor;
    exact (@std_to_fiatCrypto_field _ _ _ _ _ _ _ _ _ (FFp2 M_pos M_prime M_big M_mod)).
  Defined.

  Definition fst_felem (Fp2_list : list word) : list word := firstn felem_size_in_words Fp2_list.
  Definition snd_felem (Fp2_list : list word) : list word := skipn felem_size_in_words Fp2_list.

  Definition fst_felem_bytes (Fp2_list : list byte) : list byte := firstn (Z.to_nat felem_size_in_bytes) Fp2_list.
  Definition snd_felem_bytes (Fp2_list : list byte) : list byte := skipn (Z.to_nat felem_size_in_bytes) Fp2_list.

  Instance Fp2_representation : @FieldRepresentation Fp2_parameters _ _ _ _.
  Proof.
    econstructor.
      - exact (fun y => (feval (fst_felem y), feval (snd_felem y))).
      - exact (fun y => (feval_bytes (fst_felem_bytes y), feval_bytes (snd_felem_bytes y))).
      - exact (2 * felem_size_in_words)%nat.
      - exact (2 * encoded_felem_size_in_bytes)%nat.
      - exact (fun y => bytes_in_bounds (fst_felem_bytes y) /\ bytes_in_bounds (snd_felem_bytes y)).
      - exact (fun (y : bounds) felem => (bounded_by y (fst_felem felem)) /\ (bounded_by y (snd_felem felem))).
      - exact loose_bounds.
      - exact tight_bounds.
  Defined.

  Instance Fp2_representation_ok : @FieldRepresentation_ok Fp2_parameters _ _ _ _ Fp2_representation.
  Proof.
    econstructor; destruct field_representation_ok; intros.
    split; eapply relax_bounds; apply H.
  Defined.

End QuadraticExtension.


