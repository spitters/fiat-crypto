# Deprecated text-path extraction files

**STATUS: DEPRECATED 2026-04-14. Do not use for new development.**

These files extract via `Core.pp_module` / `Core.to_jasmin_sized` to `.jazz`
text. The output is unverified (`pp_*` has no soundness proof) and requires
manual post-processing (MULHUU → #MULX fixups, function reordering, etc.)
before jasminc accepts it.

## Replaced by

The verified AST-to-AST path: `../extractions/<curve>.v` + `../BridgeReal.to_jasmin_cmd`,
glued by the ~30-line OCaml shim `ast2ast_main.ml`.

## Why kept

- Differential testing against the AST path (catches divergence)
- Reproducing benchmarks cited in older paper drafts
- Debugging by visualising the AST as `.jazz` text

## Files

| File | Was | Curve |
|---|---|---|
| `ExtractText.v` | `ExtractToJasmin.v` | (generic) |
| `ExtractBLS12Text.v` | `ExtractBLS12Jasmin.v` | BLS12-381 |
| `ExtractBN254Text.v` | `ExtractBN254Jasmin.v` | BN254 |
| `ExtractBN254FullText.v` | `ExtractBN254FullJasmin.v` | BN254 (full pairing) |
| `ExtractBLS377Text.v` | `ExtractBLS377Jasmin.v` | BLS12-377 |

## Removal plan

These will be deleted after:
1. The AST path produces matching `.s` files for BLS12-381 (verified).
2. AST-path extractions for BN254, BLS12-377 are written.
3. The paper benchmarks are locked.
