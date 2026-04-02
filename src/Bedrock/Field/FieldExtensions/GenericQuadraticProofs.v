(** * WP correctness proofs for generic quadratic extension functions. *)

Require Import Crypto.Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.FieldExtensions.SepFromPutmany.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.

Import Separation SeparationLogic.

Section GenericQuadProofs.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {BaseField : Type}.
  Context {base_fp : FieldParameters BaseField}.
  Context {base_repr : @FieldRepresentation BaseField base_fp width BW word mem}.
  Context {base_repr_ok : @FieldRepresentation_ok BaseField base_fp width BW word mem base_repr}.

  Variable nonresidue : BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Instance QE_fp := QE_field_parameters nonresidue prefix eq_dec_base (base_fp := base_fp).
  Local Instance QE_repr := QE_field_representation nonresidue (base_fp := base_fp) (base_repr := base_repr).

  Local Notation QE := (BaseField * BaseField)%type.
  Local Notation base_size := (@felem_size_in_words _ base_fp _ _ _ _ base_repr).
  Local Notation base_offset := (Memory.bytes_per_word width * Z.of_nat base_size).

  Context {QE_names : FieldNames (F := QE)}.
  Context {base_names : FieldNames (F := BaseField)}.

  Variable mul_by_nr_name : string.
  Variable Mul_by_nr_func : string * (list String.string * list String.string * Syntax.cmd.cmd).
  Hypothesis Mul_by_nr_name_eq : fst Mul_by_nr_func = mul_by_nr_name.

  (* ================================================================ *)
  (* QE_zero_ok                                                        *)
  (* ================================================================ *)

  (* Test 1: simplest possible *)
  Goal True.
  Proof. exact I. Qed.

  (* Test 2: does QE_zero_func typecheck? *)
  Check QE_zero_func nonresidue prefix eq_dec_base
    mul_by_nr_name Mul_by_nr_func Mul_by_nr_name_eq.

End GenericQuadProofs.
