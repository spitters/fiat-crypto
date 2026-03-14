Require Import Rupicola.Lib.Api.
Require Export Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Local Open Scope Z_scope.

(* This file re-exports Compilation2 and provides backward-compatible
   qualified names for downstream BLS12 files. *)

Section CompilationAbstractCompat.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  (* Qualified-name aliases for backward compat *)
  Definition maybe_bounded := @Compilation2.maybe_bounded
    width BW word mem field_parameters field_representation.
  Definition FElem := @Compilation2.FElem
    width BW word mem field_parameters field_representation.

  (* FofZ: convert Z to F M_pos *)
  Definition FofZ (x : Z) : F M_pos := F.of_Z M_pos x.

  (* spec_of_from_list: needed by downstream from_list files *)
  Definition spec_of_from_list (v : F M_pos) (name : string) :=
    fun functions =>
      forall tr m out_ptr (out : felem) R,
        (Field.FElem out_ptr out * R)%sep m ->
        WeakestPrecondition.call functions name tr m [out_ptr]
          (fun tr' m' rets =>
             tr = tr' /\
             rets = nil /\
             exists X : felem,
               feval X = v
               /\ bounded_by loose_bounds X
               /\ (Field.FElem out_ptr X * R)%sep m').

End CompilationAbstractCompat.
