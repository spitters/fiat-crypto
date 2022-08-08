Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.ArrayUtil.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.ScalarsUtil.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Open Scope sep_scope.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.WordByWordMontgomeryUtil.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.

Section __.

      Context {width : Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
      Context {locals: map.map String.string word}.
      Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
      Context {ext_spec: bedrock2.Semantics.ExtSpec}.
      Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
      Context {locals_ok : map.ok locals}.
      Context {env_ok : map.ok env}.
      Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
      Context {field_parameters : AbstractField.FieldParameters}
            {field_parameters_ok : AbstractField.FieldParameters_ok}.

      Context {field_representation : FieldRepresentation}
            {field_representation_ok : FieldRepresentation_ok}
            {group_cmov : string}
            {store_zero : string}.

    (*curve-defining parameter b*)
    (* Definition three_b := 0.
    Definition uw := (uweight 64).
    Definition n := felem_size_in_words.
    Definition three_b_list := Partition.partition uw n three_b.
    Definition word := BasicC64Semantics.word.
    Definition three_b_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n m (@m' bls12_prime.field_parameters 64) three_b_list).
    Definition three_b_words := List.map (@word.of_Z 64 word) three_b_mont. *)

      Instance spec_of_store_zero : spec_of "store_zero_G" :=
      fnspec! "store_zero_G"
            (pX pY pZ: word)
            / (X Y Z : F) R,
      { requires tr mem :=
            (FElem (Some tight_bounds) pX X
            * FElem (Some tight_bounds) pY Y
            * FElem (Some tight_bounds) pZ Z * R)%sep mem;
            ensures tr' mem' :=
                  (FElem (Some tight_bounds) pX Fzero
            * FElem (Some tight_bounds) pY Fone
            * FElem (Some tight_bounds) pZ Fzero * R)%sep mem'}.

          (* Definition from_list_func : Syntax.func := ("store_zero_F", (["out"], (nil : list string), bedrock_func_body:(
                coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_b_mont 0)));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (nth 1 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (nth 2 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (nth 3 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (nth 4 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (nth 5 three_b_mont 0))
              ))).

        Definition store_zero_func : bedrock2.Syntax.func :=
        ("store_zero", (["outx"; "outy"; "outz"], []:list String.string, bedrock_func_body:(
                coq:(cmd.call [] "store_zero_F" [expr.var ("outx")]);
                coq:(cmd.call [] "store_one_F" [expr.var ("outy")]);
                coq:(cmd.call [] "store_zero_F" [expr.var ("outz")])
        ))).

        From bedrock2 Require Import ToCString Bytedump.
        Definition c_mod := (c_module (store_zero_func:: nil)).
    
        Eval native_compute in c_mod. *)

End __.