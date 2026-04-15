# bridge_simple_v2.ml — Coq-extracted JasminBridgeReal

## What this is

`bridge_simple_v2.ml` is the OCaml extraction of
`src/Bedrock/Field/FieldExtensions/JasminBridgeReal.v`, produced in
isolation (no fiat-crypto imports) to side-step the universe
inconsistency that triggers when `JasminBridgeReal` and `bn254_prime` /
`bls12_prime` are imported into the same file (see
`project_unipoly_rebuild.md` in Claude memory).

## How it is consumed

Two parallel OCaml drivers use this file via `Obj.magic` casts on the
structurally-identical `jasmin_cmd` type (the ASTs are defined once in
`ToJasmin.v` and flow through both extractions):

- `src/Bedrock/Field/FieldExtensions/ast2ast_main.ml`           (BLS12-381)
- `src/Bedrock/Field/FieldExtensions/bn254_ast2ast_main.ml`      (BN254)
- `src/Bedrock/Field/FieldExtensions/bls377_ast2ast_main.ml`     (BLS12-377)

Build scripts: `src/Bedrock/Field/FieldExtensions/build_*_ast2ast.sh`.

## Runtime status (2026-04-15)

**Runtime WORKS** — the file has been patched to realize the 8 Coq
axioms via OCaml primitives (`jasmin.uint63-native` for `Uint63.t`,
`Obj.magic` identity casts for the sealed `Cident.t`-style ones).  See
the `PATCH (2026-04-15)` comment blocks in the file.  Sample output:

```
$ ./bn254_ast2ast_main
[bn254-ast2ast] 56 functions
  bn254_mul                      -> 813 Jasmin instrs
  bn254_miller_loop              -> 19 Jasmin instrs
  bn254_pairing_dsd              -> 5 Jasmin instrs
  ...
$ ./bls377_ast2ast_main
[bls377-ast2ast] 6 functions
  bls377_mul                     -> 1913 Jasmin instrs
  ...
```

The patch is a stop-gap over the original Coq extraction: the cleaner
fix is to re-extract `bridge_simple_v2.ml` with the directives below.

## How it was produced

The extraction driver (a small `.v` file that imported
`JasminBridgeReal` alone and ran `Extraction "bridge_simple_v2" ...`)
was a throwaway during the 2026-04-10 bring-up and is not checked in.
When regenerating, the driver should include:

```coq
Extract Inductive PrimInt63.int => "int" [ "0" ].
Extract Inlined Constant PrimInt63.lsl      => "(lsl)".
Extract Inlined Constant PrimInt63.lor      => "(lor)".
Extract Inlined Constant PrimInt63.sub      => "(-)".
Extract Inlined Constant PrimInt63.eqb      => "(=)".
Extract Inlined Constant PrimInt63.compares => "Stdlib.compare".
Extract Inlined Constant JasminBridgeReal.int_to_ident
  => "(fun x -> Obj.magic x)".
Extract Inlined Constant JasminBridgeReal.int_to_funname
  => "(fun x -> Obj.magic x)".
```

Feeding the resulting file to jasminc's `compile_prog_to_asm` (via
additional OCaml wrapping — see `COMPILE_PROG_TO_ASM.md`) closes the
verified bedrock2 → x86-64 chain.
