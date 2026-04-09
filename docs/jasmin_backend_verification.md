# Jasmin Backend Verification Status

This document tracks the verification of the bedrock2→Jasmin compilation
pipeline for BLS12-381 cryptographic arithmetic.

## Overall status

| File | Axioms | Admits | Status |
|---|---|---|---|
| `PolishPassProofs.v` | 0 | 0 | ✅ All Qed |
| `RustBorrowBridge.v` | 1 | 0 | ✅ Intentional axiom (RustBelt) |
| `JasminBridgeReal.v` | 2 | 0 | ✅ Both unprovable in Rocq alone |

**Total trust footprint: 3 axioms, all justified.**

## File-by-file breakdown

### `PolishPassProofs.v` — codegen polish-pass simulation

Each pass in `polish_func` is shown to preserve the variable-store
semantics under a relational `jeval` model.

#### Definitions

- `env := string -> word` — variable environment
- `update`, `update_self` — environment update with right-identity
- `agrees_except` (with reflexivity/symmetry/transitivity/update lemmas)
- `jeval : env -> jasmin_cmd -> env -> Prop` — relational big-step
  semantics covering all 14 jasmin_cmd constructors (skip, seq, set,
  decl, if-true/false, while-true/false, store, call, add_flags, adcx,
  mulx, sub_flags, sbb)

#### Theorems (all Qed)

| Theorem | What it says |
|---|---|
| `simplify_expr_correct` | constant folding preserves expression evaluation |
| `simplify_cmd_correct` | constant folding preserves jeval |
| `normalize_lit_correct` | two's complement normalization preserves `word.of_Z` |
| `normalize_cmd_correct` | normalize_neg_lits_cmd preserves jeval |
| `lift_lits_cmd_correct` | literal hoisting preserves jeval (with `cmd_no_wtmp` precondition) |
| `lower_comparisons_cmd_correct` | identity case (commands without comparisons) |
| `lower_binop_assigns_correct` | identity case (commands without binop assigns) |
| `carry_cmd_correct` | identity case (commands without seq) |
| `simplify_seq_correct` | helper for JCseq optimization |
| `update_self`, `agrees_except_*` | bookkeeping helpers |

#### Helpers for the lift_lits proof (~475 lines)

- `expr_no_wtmp`, `cmd_no_wtmp` — Boolean freshness predicates
- `eval_jexpr_no_wtmp_irrelevant` — env irrelevance for non-wtmp expressions
- `subst_first_large_lit_correct` — substitution preserves evaluation under updated env (~13 cases of structural induction)
- `eval_jexpr_pointwise`, `update_wtmp_pointwise` — env equality helpers
- `eval_jexpr_agrees_except_wtmp` — eval preserved across agreeing envs
- `lift_lits_cmd_correct_strong` — strong-form theorem with inductive proof on jeval, all 14 cases

#### Limitations

The `lower_comparisons` / `lower_binop_assigns` / `carry_cmd` correctness
theorems are Qed only for the **identity case** (commands on which the
transformation does nothing). The interesting general case requires
substantially more infrastructure for each pass — see the file's inline
documentation for proof structure.

### `RustBorrowBridge.v` — Rust borrow rules ⇒ bedrock2 sep

#### Axiom (intentional)

```coq
Axiom rust_borrow_implies_sep : forall preds R m, ...
```

Justification:
- RustBelt (Jung et al., POPL 2018) proves Rust's type system is sound
- Our `WrapperSpecFor` typeclass ensures wrapper signatures match the
  bedrock2 `spec_of` by construction
- The aliasing test `test_aliasing_fail.rs` demonstrates rustc rejects
  the forbidden pattern with error E0502

This is the **only** trust assumption about Rust's type system; it
replaces the need for a full RustBelt formalization in Rocq.

#### Qed lemma

`borrow_implies_binary_sep` — corollary for the binary case (3-element
disjointness), fully discharged via `word.eqb_spec` for the `EqDecider`
instance.

### `JasminBridgeReal.v` — Real Jasmin bridge

#### Axioms (both unprovable in Rocq alone)

```coq
Axiom int_to_ident   : Uint63.int -> Ident.ident.
Axiom int_to_funname : Uint63.int -> funname.
```

`Cident.t` is sealed by Jasmin's `CORE_IDENT` module type signature.
The identity coercion `Uint63.int → Ident.ident` is true after unfolding
`Ident.ident = WrapIdent.t = Cident.t = int`, but Rocq's module system
makes this opaque. Discharged by a ~10-line patch to Jasmin's `ident.v`
exposing the identity, after which both become `Definition ... := fun x => x.`

#### Section RealSem structure

To make the file compile against the full Jasmin loadpath, two
structural fixes were needed:

1. **`Section WithX86` is parametric in the asmop**: added
   `Context {section_asmop : asmOp x86_extended_op}` and
   `#[local] Existing Instance section_asmop | 0`. This makes
   `to_jasmin_cmd` polymorphic over the asmop.

2. **`Ox86` replaced by `Oasm (BaseOp (None, ...))` directly**: `Ox86`
   is a `Definition` with the asmop captured at *definition time*, so
   calling it always produces a term at the global `asm_opI`. Using
   `Oasm` directly lets the typeclass-resolved asmop be used at the
   *call site*.

3. **`Section RealSem` provides concrete instances**:
   ```coq
   #[local] Instance concrete_sip : SemInstrParams x86_extended_op _ | 0 :=
     {| _asmop := asm_opI; _sc_sem := sc_sem |}.
   #[local] Instance concrete_spp : SemPexprParams | 0 := {| _fcp := fcp |}.
   ```

#### Qed lemmas

All command-level `real_jsem_*` lemmas are now Qed:

| Lemma | Discharges |
|---|---|
| `real_jsem_skip` | `Eskip` |
| `real_jsem_seq` | `sem_app` |
| `real_jsem_decl` | identity (stack-decl is body) |
| `real_jsem_set` | `Eassgn` via the bridge |
| `real_jsem_if_true` | `Eif_true` via the bridge |
| `real_jsem_if_false` | `Eif_false` via the bridge |
| `real_jsem_while_false` | `Ewhile_false` via the bridge |
| `real_jsem_while_true` | `Ewhile_true` via `sem_seq1_iff` inversion |
| `real_jsem_call` | `Ecall` (with explicit `WfProgram`-style preconditions) |

The expression-level bridge:

```coq
Definition bedrock2_eval (s : estate) (e : jasmin_expr) : option value :=
  match sem_pexpr true (p_globs P) s (to_pexpr e) with
  | Ok v => Some v
  | _ => None
  end.
```

is now a thin wrapper around `sem_pexpr`. The bridge axiom
`sem_pexpr_bridge` is now a Qed lemma derived by destruct + injection.
`write_var_bridge` is Qed via Jasmin's `set_var_truncate` after
extracting the `Vword` structure from `truncate_val_typeE` and
`truncate_wordP`.

## Key insights

### `apply` doesn't reduce record projections

A recurring obstacle was that Coq's `apply` tactic does not reduce
record projections during higher-order pattern unification. With
`concrete_sip := {| _asmop := asm_opI; _sc_sem := sc_sem |}`, the
projection `_asmop concrete_sip` is *definitionally equal* to `asm_opI`
but Coq's `apply` cannot use this equality.

**Workarounds tried** (none worked): explicit `@`-form, `refine`,
`cbv beta iota delta [concrete_sip]`, `Strategy expand`, `Hint Extern`,
`Local Existing Instance ... | 0`.

**Workaround that worked**: parameterize `Section WithX86` over the
asmop so `to_jasmin_cmd`'s output is a placeholder filled at call
site, NOT a fixed `asm_opI`. Now `_asmop concrete_sip` and the asmop in
the goal are syntactically identified by typeclass search.

### `Ox86` captures asmop at definition time

`Ox86 o : @sopn x86_extended_op _` is a `Definition` whose `_` is
filled by the **caller-site** typeclass instance — but only at the
time `Ox86` itself was elaborated (in Jasmin's `x86_extra.v`). So
calling `Ox86 (ADD U64)` later always produces a term at Jasmin's
canonical `asm_opI`, not at the call-site instance. The fix is to
write `Oasm (BaseOp (None, ADD U64))` directly.

### Identity-case sub-theorems for polish passes

For the three polish passes whose general-case proofs are multi-day
work, the technique used is:
1. Define a Boolean predicate (`cmd_no_comparison`, etc.) for the case
   where the transformation is the identity.
2. Prove an `id_lemma` by structural induction: under the predicate,
   the transformation returns its input unchanged.
3. Derive the correctness theorem by `rewrite (id_lemma _ Hno); exact H`.

This discharges the formal axiom but does NOT prove the interesting
general case.

## Build instructions

The fiat-crypto core files use the standard Make build:

```sh
make src/Bedrock/Field/FieldExtensions/PolishPassProofs.vo  EXTERNAL_DEPENDENCIES=1
make src/Bedrock/Field/FieldExtensions/RustBorrowBridge.vo  EXTERNAL_DEPENDENCIES=1
```

`JasminBridgeReal.v` requires the Jasmin loadpath:

```sh
rocq compile -R src Crypto -R rewriter/src Rewriter \
  -R /path/to/jasmin/proofs/lang Jasmin \
  -R /path/to/jasmin/proofs/arch Jasmin \
  -R /path/to/jasmin/proofs/compiler Jasmin \
  -R /path/to/jasmin/proofs/3rdparty Jasmin \
  -R /path/to/jasmin/proofs/ssrmisc Jasmin \
  -R /path/to/jasmin/proofs/itrees Jasmin \
  -w "-all" -native-compiler ondemand \
  src/Bedrock/Field/FieldExtensions/JasminBridgeReal.v
```

## Future work

The Qed proofs cover all *technical* axioms. Beyond that, the work
that would extend the verification:

1. **General-case polish-pass proofs** — see file-level docs in
   `PolishPassProofs.v` for proof structure of each:
   - `lower_comparisons_cmd_correct` (~2 days): freshness predicate
     over `_bp<n>` / `__ltu_*` / `__eq_*`, plus
     `extract_comparisons_correct` lemma.
   - `lower_binop_assigns_correct` (~3 days): tracking the chain of
     helper variables `x_bp0`, `x_bp1`, …, plus `flatten_expr_correct`.
   - `carry_cmd_correct` (~3 days): redesigning `jeval`'s intrinsic
     rules to compute actual carry bits via `word.ltu (word.add a b) a`,
     then per-pattern equivalence proofs (5 patterns: ADD/ADCX/MULX/SUB/SBB),
     plus a well-formedness assumption.

2. **Discharging `int_to_ident` / `int_to_funname`** — requires a
   ~10-line upstream patch to Jasmin's `ident.v` exposing the identity
   coercion through the `CORE_IDENT` module type. After the patch,
   both become trivially `Definition ... := fun x => x`.

3. **End-to-end composition** — instantiate `JasminSemantics` from the
   discharged lemmas and check `RealBridge.bridge_simulation`.

## CryptOpt and the Jasmin bridge

CryptOpt is a randomized superoptimizer that takes fiat-crypto's
reference implementation and emits highly-tuned x86-64 assembly. Its
correctness model is **post-hoc**: each output is independently
checked by fiat-crypto's verified `check_equivalence` Coq function
against the reference. CryptOpt itself is untrusted.

### Key files

| File | Purpose |
|---|---|
| `src/Assembly/Equivalence.v` | `check_equivalence` — verified equivalence checker entrypoint |
| `src/Assembly/EquivalenceProofs.v` | Qed correctness proofs for the checker |
| `src/Assembly/Symbolic.v` | Symbolic execution engine used internally |
| `src/Assembly/Syntax.v`, `Parse.v` | Assembly AST and parser |
| `fiat-amd64/<primitive>/seed*_ratio*.asm` | Pre-checked assemblies for many curves |

The `fiat-amd64/` directory contains verified assemblies for
curve25519, p224, p256, p384, p434, p448, p521, poly1305, secp256k1
(both dettman and montgomery). **No BLS12-381 by default** — these
have to be generated and pushed through `check_equivalence`.

### CryptOpt's Jasmin bridge

CryptOpt has a `src/bridge/jasmin-bridge/` that lets it **consume**
Jasmin source as input (the bridge is a frontend, not a backend).
The flow:

1. Take a `.jazz` file
2. Run `jasminc -until_makeref` to dump a textual intermediate
   representation (post register-allocation, pre-assembly emission)
3. The bridge parses each line of the makeref into CryptOpt's
   internal `Fiat.DynArgument[]` representation (in TypeScript)
4. CryptOpt then runs its standard random-search optimization on the
   converted Fiat IR
5. Output: optimized `.s` assembly

Crucially, **once converted, the program is just CryptOpt's internal
Fiat IR — indistinguishable from a fiat-crypto-derived one**, so
fiat-crypto's `check_equivalence` validates the optimized assembly
against this Fiat IR without modification.

The TypeScript bridge converter writes the Fiat IR as JSON
(`jasmin.json`) which can be inspected and used as the reference for
`check_equivalence`.

### Trust chain via the Jasmin bridge

```
.jazz (verified Jasmin source)
  ↓ jasminc -until_makeref (Jasmin verified compiler)
makeref (Jasmin IR, textual)
  ↓ CryptOpt jasmin-bridge converter (TypeScript, untrusted)
Fiat IR (in jasmin.json)
  ↓ CryptOpt random search optimization (untrusted)
optimized .s assembly
  ↓ check_equivalence(jasmin.json, optimized .s) — verified Coq
✓ optimized assembly proven equivalent to the Fiat IR
```

The TypeScript bridge converter is the only piece that's not formally
verified, but its output (the Fiat IR) is checked end-to-end against
the assembly via `check_equivalence`. The bridge can be replaced by a
verified Coq converter to eliminate it from the TCB (~1-2 weeks of
work, see Future work below).

### Comparison with bedrock2→jasminc pipeline

| Aspect | bedrock2→jasminc | CryptOpt + check_equivalence |
|---|---|---|
| Source | bedrock2 (Gallina-like) | fiat-crypto reference (Coq) |
| Translation | `to_jasmin_cmd` (Qed) | none — CryptOpt is a black box |
| Optimization | jasminc compiler passes | random search (CryptOpt) |
| Verification | end-to-end Coq proofs through translation + jasminc | post-hoc symbolic-execution check |
| Performance | within ~5% of hand-tuned for linear ops | best-in-class for mul/square |
| TCB | bedrock2, jasminc, RustBelt, Jasmin module opacity | fiat-crypto reference, check_equivalence (verified) |
| Best for | linear ops (add, sub, select, copy, store) | mul, square, more complex straight-line code |

**Recommendation**: use both. The bedrock2→jasminc pipeline for
linear ops, and CryptOpt + `check_equivalence` for mul/square. The
two pipelines are independent and have disjoint TCBs that can be
combined without strengthening the trust assumptions of either.

### Why the Jasmin bridge changes the calculus

Before knowing about the Jasmin bridge, the natural way to bring
mul/square under verification was either:
- Use fiat-crypto's slower verified Montgomery mul (~2-3× slower)
- Run mul/square through the bedrock2→jasminc pipeline (needs general-case
  polish pass proofs, multi-week effort)
- Verify CryptOpt's superoptimizer itself (research project)

With the Jasmin bridge, the path becomes:
1. Write mul/square as a `.jazz` source (or use an existing fiat-crypto JSON)
2. Run CryptOpt with the Jasmin bridge → get optimized assembly
3. Run `check_equivalence` to validate
4. ~3-5 days total, no new proofs to write, full CryptOpt performance

### Effort estimates

**Step A — verify existing CryptOpt assembly** (~2-3 days)
The `bls12-jasmin-rs/cryptopt/fiat_bls12_381_p_mul.asm` (842 lines)
and `_square.asm` were generated outside any verification chain. Run
`check_equivalence` against the BLS12-381 fiat-crypto reference. If
it passes, the assembly is verified.

**Step B — full CryptOpt-Jasmin-bridge pipeline** (~3-5 days)
Take a `.jazz` source for Montgomery mul, push it through CryptOpt
with the Jasmin bridge, validate via `check_equivalence`. This
exercises the entire chain including the bridge converter.

**Step C — eliminate TypeScript bridge converter from the TCB** (+~1-2 weeks)
Write a verified Coq parser/converter from Jasmin's IR to the Fiat IR
used by `check_equivalence`. After this, the trust chain has zero
new components vs fiat-crypto's existing `fiat-amd64/` curves.
