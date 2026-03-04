Require Import Rupicola.Lib.Api.
(* Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.FLia. *)
Require Import Crypto.Bedrock.Specs.Field.
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

  Context {prime_parameters : PrimeParameters}
          {prime_parameters_ok : PrimeParameters_ok}
          {M_mod : M_pos mod 4 =? 3 = true}.
  Existing Instance prime_field_parameters.
  Context {field_representation : FieldRepresentation (F M_pos)}
          {field_representation_ok : FieldRepresentation_ok (F M_pos)}.

  Lemma M_big : 2 < M_pos.
  Proof.
    lia.
  Qed.

  Local Notation Fp2 := ((F M_pos) * (F M_pos))%type.

  Instance Fp2_field_parameters : FieldParameters Fp2.
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
        - exact (of_Zp2 M_pos).
        - eapply eq_dec_Fp2.
  Defined.

  Instance Fp2_field_parameters_ok : FieldParameters_ok Fp2.
  Proof.
    econstructor;
    exact (@std_to_fiatCrypto_field _ _ _ _ _ _ _ _ _ (FFp2 M_pos M_prime M_big M_mod)).
  Defined.

  Definition fst_felem (Fp2_list : list word) : list word := firstn felem_size_in_words Fp2_list.
  Definition snd_felem (Fp2_list : list word) : list word := skipn felem_size_in_words Fp2_list.

  Definition fst_felem_bytes (Fp2_list : list byte) : list byte := firstn (Z.to_nat felem_size_in_bytes) Fp2_list.
  Definition snd_felem_bytes (Fp2_list : list byte) : list byte := skipn (Z.to_nat felem_size_in_bytes) Fp2_list.

  Instance Fp2_field_representation : FieldRepresentation Fp2.
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

  Instance Fp2_field_representation_ok : FieldRepresentation_ok Fp2.
  Proof.
    econstructor; destruct field_representation_ok; intros.
    split; eapply relax_bounds; apply H.
  Defined.

End QuadraticExtension.


