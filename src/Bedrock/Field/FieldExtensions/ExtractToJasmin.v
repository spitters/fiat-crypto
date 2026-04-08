(** * OCaml extraction of the ToJasmin translator + FlattenStackalloc. *)

From Coq Require Export Extraction.
From Coq Require Export ExtrOcamlBasic.
From Coq Require Export ExtrOcamlString.
From Coq Require Export ExtrOcamlZInt.
From Stdlib Require Import ZArith String Ascii.
Require Import Crypto.Bedrock.Field.FieldExtensions.ToJasmin.
Require Import Crypto.Bedrock.Field.FieldExtensions.FlattenStackalloc.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

(* Use ExtrOcamlZInt for native Z/positive/nat *)
(* Use ExtrOcamlString for native string/ascii *)
(* These are the standard Rocq extraction remappings *)

Extraction "src/Bedrock/Field/FieldExtensions/to_jasmin_extracted"
  tr_func tr_func_sized pp_func pp_module to_jasmin to_jasmin_sized
  flatten_stackallocs flatten_func flatten_selected.
