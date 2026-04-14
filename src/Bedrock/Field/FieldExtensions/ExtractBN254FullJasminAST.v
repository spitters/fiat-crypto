(** * AST-to-AST Jasmin extraction for BN254 (full pairing).
 *
 * Uses [to_jasmin_cmd] from [JasminBridgeReal.v] to translate our
 * [jasmin_cmd] AST directly to Jasmin's [cmd] type (= [seq instr]),
 * bypassing the pretty-printer entirely. The resulting translated
 * bodies are extracted to OCaml and fed to Jasmin's verified
 * [compile_prog_to_asm] by the OCaml driver.
 *
 * Verification chain:
 *   bedrock2 cmd → tr_cmd (Qed) → jasmin_cmd → polish_func (6 passes, Qed)
 *   → to_jasmin_cmd (Qed) → Jasmin cmd → compile_prog_to_asm → x86-64
 *
 * No pretty-printer. No parser. The entire chain is AST-to-AST.
 *
 * Parallel to [ExtractBLS12JasminAST.v] but pulls in the full BN254
 * pairing function list from [BN254_Pairing] plus the optimized ops
 * from [BN254_OptimizedOps], matching the surface of the deprecated
 * [ExtractBN254FullJasmin.v] text-based driver.
 *)

From Stdlib Require Import ZArith String List.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString.
Import ListNotations.

Require Import bedrock2.Syntax.
Require Import Crypto.Bedrock.Field.FieldExtensions.ToJasmin.
Require Import Crypto.Bedrock.Field.FieldExtensions.JasminBridgeReal.

Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_Fp2.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN254_Pairing.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN254_OptimizedOps.

Import bedrock2.Syntax.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Same function list as [ExtractBN254FullJasmin.bn254_full_funcs_raw]. *)
Definition bn254_fp_base_funcs : list function_t :=
  [ bn254_add; bn254_sub; bn254_mul; bn254_square;
    bn254_select_znz;
    ("bn254_felem_copy", bn254_felem_copy) ].

(** [Fp2_zero]/[Fp2_one] omitted — they depend on [bn254_from_word],
    which is never synthesized in [bn254_prime.v].  See the note in
    [ExtractBN254FullJasmin.v]. *)
Definition bn254_fp2_base_funcs : list function_t :=
  [ Fp2_felem_copy; Fp2_add; Fp2_sub;
    Fp2_mul; Fp2_sqr; Fp2_inv ].

Definition bn254_full_funcs_raw : list function_t :=
  bn254_fp_base_funcs ++
  bn254_fp2_base_funcs ++
  BN254_Pairing.bn254_all_pairing_funcs ++
  bn254_opt_funcs.

(** [vm_compute] forces the typeclass projections for
    [felem_size_in_bytes] to real byte sizes so [stackalloc] arguments
    become literal integers.  Same reasoning as
    [ExtractBN254FullJasmin.bn254_full_funcs]. *)
Definition bn254_full_funcs : list function_t :=
  Eval vm_compute in bn254_full_funcs_raw.

Definition bn254_full_field_size : Z := 4.

(** Step 1: bedrock2 → our [jasmin_cmd] AST (via [tr_func_sized] +
    6 polish passes). *)
Definition bn254_full_jasmin_ast : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized bn254_full_field_size f))
             bn254_full_funcs.

(** Step 2: our [jasmin_cmd] AST → Jasmin's [cmd] AST (via
    [to_jasmin_cmd] from [JasminBridgeReal]).  The translated function
    bodies are extracted as quadruples (name, params, returns, body).
    The OCaml driver packages each with Jasmin's [f_extra] / [fn_info]
    to build a full [prog] and feeds it to [compile_prog_to_asm]. *)
Definition bn254_full_translated_bodies
  : list (string * list string * list string * jasmin_cmd) :=
  List.map (fun f => (jf_name f,
                      List.map fst (jf_params f),
                      nil,  (* pure side-effect functions *)
                      jf_body f)) bn254_full_jasmin_ast.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

(** Extract the translated bodies plus the [to_jasmin_cmd] translator
    (the OCaml driver calls it per-function to get a Jasmin [cmd]). *)
Extraction "bn254_full_ast_extracted"
  bn254_full_translated_bodies
  bn254_full_field_size
  to_jasmin_cmd
  to_pexpr
  string_to_ident.
