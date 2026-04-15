# Bedrock2 → Jasmin verified pipeline

End-to-end translation: bedrock2 `cmd` AST → polished local AST → real Jasmin
`expr.cmd` → x86-64 assembly via jasminc's Rocq-verified compiler.

## Verified core (this directory)

| File | Lines | Role | Status |
|---|---:|---|---|
| `Core.v` | 1790 | Local `jasmin_cmd` AST + `tr_cmd` (structural) + `polish_func` composition + DEPRECATED text pretty-printer | Qed |
| `PolishProofs.v` | 1120 | Soundness for all 6 polish passes | 30 Qed, 0 Admitted |
| `BridgeAbstract.v` | 244 | Parametric `JasminSemantics` module type + functor | Qed |
| `BridgeReal.v` | 455 | `to_jasmin_cmd : jasmin_cmd → Jasmin.expr.cmd` (real Jasmin AST) | 17 Qed, 2 trivial axioms |
| `BridgeRealInstance.v` | 167 | Wires parametric bridge to Jasmin's real `psem.sem` | Qed |
| `BridgeConcrete.v` | 235 | Concrete `StubJasminSem` instance (proves the abstract type is inhabited) | Qed |
| `ExprBridge.v` | 214 | Expression-level semantic bridge | Qed |
| `FlattenStackalloc.v` | — | Verified stackalloc flattening | Qed |

**Total:** ~4400 lines of Rocq, ~50 Qed lemmas, **2 trivial identity-cast axioms**
(`int_to_ident`, `int_to_funname` in `BridgeReal.v` — both runtime identity).

## Verified extractions (`extractions/`)

One file per curve, each producing an OCaml-extracted `jasmin_func list` for
consumption by the OCaml driver.

| File | Curve | Output |
|---|---|---|
| `BLS12_381.v` | BLS12-381 pairing | `bls12_jasmin_extracted.ml` |

X25519-64 lives in AUCurves (per repo separation policy):
`AUCurves/src/Bedrock/End2End/X25519_64/ExtractJasminAST.v` produces
`x25519_64_jasmin_extracted.ml`.

## DEPRECATED text-path extractions (`deprecated/`)

These use `Core.v`'s pretty-printer (`pp_module` / `to_jasmin_sized`) which
emits `.jazz` text. The output requires manual post-processing (MULHUU →
#MULX fixups, function reordering, pointer-vs-array convention patches) and
the pretty-printer itself is unverified.

| File | Replacement |
|---|---|
| `ExtractText.v` | use the per-curve files in `extractions/` |
| `ExtractBLS12Text.v` | `extractions/BLS12_381.v` |
| `ExtractBN254Text.v` | (TODO: write `extractions/BN254.v`) |
| `ExtractBN254FullText.v` | (TODO: write `extractions/BN254.v`) |
| `ExtractBLS377Text.v` | (TODO: write `extractions/BLS12_377.v`) |

These files are kept for differential testing and historical reproducibility
of paper benchmarks; new code must not import them.

## OCaml drivers

The drivers live alongside the verified core in fiat-crypto's
`Field/FieldExtensions/` (legacy location, will move when refactor finishes):

- `compile_direct.ml` (893 LoC) — partially deprecated:
  - `translate_cmd` / `translate_expr` (~200 LoC) RE-IMPLEMENT `BridgeReal.to_jasmin_cmd` in OCaml. **DEPRECATED** — use the extracted version via the universe shim.
  - The remaining ~700 LoC (`Conv.cuprog_of_prog`, `Compile.compile`, variable tables, register-pressure partitioning, `Pp_x86.print_prog`) is legitimate jasminc API plumbing and **retained**.
- `ast2ast_main.ml` (23 LoC) + `ast2ast_driver.ml` (90 LoC) — the **~30-line universe shim**: bridges two separate Coq extractions (the bedrock2 data extraction and the `to_jasmin_cmd` translator extraction) using `Obj.magic` for the architecture typeclass arguments and a `Z`/`positive` int conversion. Required because combining fiat-crypto and Jasmin in one Rocq extraction triggers a coqutil/mathcomp universe inconsistency (see `project_unipoly_rebuild.md`).

## Verification chain

```
bedrock2.cmd
    ↓ tr_cmd (Qed in Core.v)
jasmin_cmd
    ↓ polish_func (30 Qed in PolishProofs.v)
jasmin_cmd (polished)
    │
    │ ≡≡≡ universe inconsistency boundary ≡≡≡
    │   bridged in OCaml by ast_bridge.ml (~30 lines, Obj.magic + Z/int)
    │
    ↓ to_jasmin_cmd (17 Qed in BridgeReal.v) — extracted to OCaml
Jasmin.expr.cmd
    ↓ Conv.cuprog_of_prog + Compile.compile (Jasmin's own Rocq proof)
x86-64 .s
```

## TCB summary

1. **2 identity-cast axioms** in `BridgeReal.v` — eliminable by upstreaming `of_int : int → t` to Jasmin's `Ident` module.
2. **~30-line OCaml shim** (`ast2ast_*.ml`) — eliminable by closing the coqutil/mathcomp universe gap (see `project_unipoly_rebuild.md`).
3. **~700 lines of jasminc API plumbing** in `compile_direct.ml` — wraps Conv/Compile/Pp_x86; mechanical glue with no Rocq counterpart.
4. **jasminc back-end** (5 of 30 passes) — Jasmin project's own remaining work, not our scope.

## See also

- `writeup/docs/ast2ast-pipeline.md` — full architectural narrative
- `~/.claude/projects/.../memory/feedback_tojasmin_ast_path.md` — why the AST path is canonical
- `~/.claude/projects/.../memory/project_unipoly_rebuild.md` — universe inconsistency origin
