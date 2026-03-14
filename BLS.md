# BLS12-381 Rocq 9 Port — Status & Continuation Guide

## Project Overview

Formal verification of BLS12-381 elliptic curve operations in bedrock2/Rupicola, targeting Rocq 9.0.0. The code lives in a fork of fiat-crypto. A companion hax/SSProve-Lean implementation at `/home/au528660/Claude/SSProve-lean/bls-hax/` provides the full BLS stack including pairing, serving as a reference specification.

**Branch**: `bls12-rocq9`
**Working dir**: `/home/au528660/Claude/BLS/AUCurves/fiat-crypto`

## Build System

```bash
eval $(opam env --switch=rocq-9)

# Build via Makefile.bls12:
make -f Makefile.bls12 quad three_b felem_copy fp2 curve_add g1 g1_alt g2 bignum_shift

# Direct coqc:
ROCQPATH=/home/au528660/.opam/rocq-9/lib/coq/user-contrib \
  /home/au528660/.opam/rocq-9/bin/coqc -Q src Crypto <file>
```

**Build notes**:
- Do NOT kill loogle — it is shared by other Claude instances
- CurveAdd.v compilation uses ~2GB RAM, completes in <1 minute
- Use `-j1` on 14GB systems

### Memory Optimization (for large Fp12 proofs)

The Fp12 mul/sqr/inv proofs use ~2-3GB each. To avoid OOM:

```bash
# 1. Use .vos to skip opaque proof bodies when building dependencies (much less RAM):
make -f Makefile.bls12 dodecic-all-vos

# 2. Or build each proof file individually:
make -f Makefile.bls12 dodecic-mul   # Fp12_mul_ok
make -f Makefile.bls12 dodecic-sqr   # Fp12_sqr_ok
make -f Makefile.bls12 dodecic-inv   # Fp12_inv_ok

# 3. Increase OCaml heap/stack limits:
OCAMLRUNPARAM="l=8G,s=4M" make -f Makefile.bls12 dodecic-sqr

# 4. Use -vos for dependencies, -vok for the file under test:
coqc -vos <dependency>.v   # fast, skips proofs
coqc -vok <file>.v         # checks proofs, loads .vos for deps
```

### File Structure (Fp12 proofs)

The Fp12 WP proofs are split into separate compilation units to avoid OOM:

```
DodecicFieldExtensions.v       # base: infrastructure + simple proofs + definitions
DodecicFieldExtensionsMul.v    # Fp12_mul_ok proof (~1000 lines)
DodecicFieldExtensionsSqr.v    # Fp12_sqr_ok proof (~850 lines)
DodecicFieldExtensionsInv.v    # Fp12_inv_ok proof (~850 lines)
```

Each proof file duplicates the Section context (Rocq Sections can't span files).
Zero `Admitted` across all files.

---

## Current Status (2026-03-12, updated)

### Zero Admitted Statements in Group Operations

All previously Admitted statements have been **proved**:

| Statement | File | Status |
|-----------|------|--------|
| `cmov_ok` | BignumShift.v | **PROVED** ✓ (2025-03-09) |
| `compile_ladderstep` | CurveAdd.v | **PROVED** ✓ (2026-03-09) |
| `ladderstep_correct` | CurveAdd.v | **PROVED** ✓ (2026-03-10) |
| `felem_copy_ok` | bls12_felem_copy.v | **PROVED** ✓ (2026-03-09) |
| `FFp6` field inverse | CubicExtensions.v | **PROVED** ✓ (2026-03-09) |

The `ladderstep_correct` was the last Admitted — closed using Rupicola's `Derive ... SuchThat` pipeline with two key fixes:
1. **`tighten_bounds_FElem`**: Local ecancel hint converting `loose_bounds → tight_bounds` (valid because `Hbounds_eq : loose_bounds = tight_bounds`)
2. **`compile_load_three_b`**: Custom compiler hint for loading the `three_b_val` constant via a function call

### WP Proofs Progress (Real Separation Logic Proofs)

**Fp2 layer — ALL PROVED** (QuadraticFieldExtensions.v + QuadraticFieldExtensionsMul.v):
- Fp2_zero_ok, Fp2_one_ok, Fp2_felem_copy_ok, Fp2_add_ok, Fp2_sub_ok, Fp2_opp_ok, Fp2_select_znz_ok, Fp2_mul_ok

**Fp6 layer — 3/8 PROVED** (CubicFieldExtensions.v):
- PROVED: Fp6_felem_copy_ok, Fp6_add_ok, Fp6_sub_ok
- Admitted: Fp6_opp_ok, Fp6_select_znz_ok, Fp6_zero_ok, Fp6_one_ok
- cmd.skip: Fp6_mul, Fp6_sqr, Fp6_inv (no bodies yet)

**Remaining `exact I` stubs** (~35):
- Fp6 opp/select_znz/zero/one
- Fp12 layer: all ops (add/sub/mul/sqr/inv/conjugate/copy/opp/zero/one/select_znz)
- Pairing ops: Frobenius, mul_fp2, mul_by_v, make_line, miller_loop, final_exp, pairing
- Top-level: BLS12_G1.v, BLS12_G1_alt.v, BLS12_G2.v instantiation lemmas

### `cmd.skip` Placeholders (Missing Bedrock2 Bodies)

**None remaining.** All `cmd.skip` stubs have been replaced with real bedrock2 bodies.

### New Functions (2026-03-10)

| Function | Description | Stack Usage |
|----------|-------------|-------------|
| `curve_add_G2` | G2 point addition over Fp2 (34 Fp2 ops) | 7 × Fp2 (672 bytes) |
| `bls12_Fp2_mul_fp` | Fp2 × Fp scalar (2 Fp muls) | none |
| `bls12_make_line` | Line evaluation construction | 1 × Fp2 (96 bytes) |
| `fp12_set_one` | Set Fp12 to identity (12 from_word calls) | none |
| `bls12_miller_loop` | Full Miller loop (63-bit iteration) | 7 field temps (f, t_x, t_y, λ, tmp1, tmp2, line) |
| `bls12_final_exp` | Easy part + h3 square-and-multiply | 3 Fp12 temps + 160 bytes for h3 limbs |
| `bls12_pairing` | Chains miller_loop + final_exp | 1 Fp12 temp |

---

## Completeness Assessment: Do We Have Full BLS12 Pairing?

**Yes, at the body level.** We have bedrock2 bodies for the **complete pairing pipeline** (Fp→Fp2→Fp6→Fp12→G1→G2→Miller loop→final exponentiation→pairing). No `cmd.skip` placeholders remain. WP correctness proofs remain as stubs (`exact I`) — 38 total.

### Component Status Matrix

| Component | Gallina Spec | Bedrock2 Body | WP Proof | Notes |
|-----------|-------------|--------------|----------|-------|
| **Fp arithmetic** | ✓ | ✓ | ✓ | Fully verified via fiat-crypto synthesis |
| **Fp2 zero/one** | ✓ | ✓ | **✓** | QuadraticFieldExtensions.v |
| **Fp2 add/sub/opp/copy** | ✓ | ✓ | **✓** | QuadraticFieldExtensions.v |
| **Fp2 select_znz** | ✓ | ✓ | **✓** | QuadraticFieldExtensions.v |
| **Fp2 mul** | ✓ | ✓ | **✓** | Karatsuba, QuadraticFieldExtensionsMul.v |
| **Fp2 conjugate** | ✓ | ✓ | stub | PairingFieldOps.v |
| **Fp6 add/sub** | ✓ | ✓ | **✓** | CubicFieldExtensions.v |
| **Fp6 copy** | ✓ | ✓ | **✓** | CubicFieldExtensions.v |
| **Fp6 opp/zero/one/sel** | ✓ | ✓ | stub | CubicFieldExtensions.v |
| **Fp6 mul** | ✓ | ✓ | stub | Karatsuba body (6 Fp2 muls + adds/subs + 3 mul_xi) |
| **Fp6 sqr** | ✓ | ✓ | stub | Chung-Hasan SQR3 body (3 Fp2 sqrs + 2 muls + mul_xi) |
| **Fp6 inv** | ✓ | ✓ | stub | Cubic inverse (3 sqrs + 6 muls + inv + 3 mul_xi) |
| **Fp6 mul_by_v** | ✓ | ✓ | stub | Shift + mul_xi (DodecicFieldExtensions.v) |
| **Fp6 mul_fp2** | ✓ | ✓ | stub | Scalar mul by Fp2 (PairingFieldOps.v) |
| **Fp6 Frobenius** | ✓ | ✓ | stub | Conjugate + gamma muls (PairingFieldOps.v) |
| **Fp6 Frobenius p²** | ✓ | ✓ | stub | Gamma_p2 muls (PairingFieldOps.v) |
| **Fp12 add/sub/opp/copy** | ✓ | ✓ | stub | DodecicFieldExtensions.v |
| **Fp12 mul** | ✓ | ✓ | stub | Karatsuba (2 Fp6 muls + mul_by_v + adds/subs) |
| **Fp12 sqr** | ✓ | ✓ | stub | 2 Fp6 sqrs + 1 mul + mul_by_v + adds |
| **Fp12 conjugate** | ✓ | ✓ | stub | (c0, -c1) — cheap cyclotomic inverse |
| **Fp12 inv** | ✓ | ✓ | stub | Quadratic norm + Fp6 inv |
| **Fp12 Frobenius** | ✓ | ✓ | stub | PairingFieldOps.v |
| **Fp12 Frobenius p²** | ✓ | ✓ | stub | PairingFieldOps.v |
| **G1 point addition** | ✓ | ✓ | **✓** | **Fully derived via Rupicola** |
| **G1 scalar mult** | ✓ | ✓ (LadderStep) | **✓** | Montgomery ladder |
| **G2 point addition** | ✓ | ✓ | stub | BLS12_G2.v (34 Fp2 ops, 7 Fp2 temps) |
| **Fp2 × Fp mul** | ✓ | ✓ | stub | BLS12_Pairing.v (2 Fp muls) |
| **Line evaluation** | ✓ | ✓ | stub | BLS12_Pairing.v (sparse Fp12 construction) |
| **Fp12 set_one** | ✓ | ✓ | stub | BLS12_Pairing.v (12 from_word calls) |
| **Miller loop** | ✓ | ✓ | stub | BLS12_Pairing.v (63-bit while loop) |
| **Final exponentiation** | ✓ | ✓ | stub | BLS12_Pairing.v (easy + h3 exp loop) |
| **Pairing** | ✓ | ✓ | stub | BLS12_Pairing.v (chains Miller + final exp) |
| **Bilinearity proof** | ✗ | — | — | Open mathematical question |

### What's Proved End-to-End

Real bedrock2 body + WP correctness proof:
- **Fp field operations**: Verified by fiat-crypto's word-by-word Montgomery synthesis
- **felem_copy**: Manual WP proof (bls12_felem_copy.v)
- **Fp2 all 8 ops**: zero, one, add, sub, opp, copy, select_znz, mul (Karatsuba) — manual WP proofs
- **Fp6 add, sub, copy**: manual WP proofs (same pattern as Fp2, with `change` for instance bridging)
- **G1 point addition** (`ladderstep_correct`): Rupicola derives the bedrock2 `cmd` tree and simultaneously proves it implements `ladderstep_gallina`
- **G1 ladder step** (`LadderStep.v`): Same Rupicola pattern for Montgomery ladder step

Everything else has real bedrock2 bodies but `exact I` WP proof stubs (~35 total).

---

## Next Steps: WP Proof Infrastructure

### The `function_t` Shim Problem

All 38 `exact I` stubs use a compatibility shim that overrides bedrock2's goal generator:

```coq
(* This makes ALL WP goals trivially True *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).
```

The shim exists because bedrock2 ≥0.0.9 removed the name from `func`, but our code needs function names for the environment table. The shim bundles `(name, body)` into `function_t` but makes the WP goal generator ignore the body and produce `True`.

### Approaches to Fix

**Approach A: Refactor to `Syntax.func`** — High effort, cleanest result
- Change all function definitions to use `Syntax.func` (body only)
- Store names separately in the function list
- Use bedrock2's real `program_logic_goal_for_function!`
- The Ltac2 goal generator then works correctly

**Approach B: Custom Ltac2 for `function_t`** — Medium effort
- Write a custom `program_logic_goal_for_function_t!` Ltac2 notation
- Extract body and name from the `(string * func)` pair
- Generate real WP goals using bedrock2's machinery

**Approach C: Standalone WP lemmas** — Per-function effort
- Write correctness lemmas directly as `WeakestPrecondition.call` goals
- Bypass `program_logic_goal_for_function!` entirely
- Template from `felem_copy_ok` proof pattern

### Proof Priority

| Tier | Count | Functions | Effort per function |
|------|-------|-----------|-------------------|
| Simple (2-3 ops) | 20 | Fp6/Fp12 add/sub/opp/copy, conjugate, select_znz, cmov | Low |
| Medium (4-9 ops) | 10 | Frobenius, mul_fp2, loop_body, make_line | Medium |
| Hard (loops/10+) | 8 | Fp6/Fp12 mul/sqr/inv, miller_loop, final_exp | High |

### Other Curves/Primitives in Scope

The fiat-crypto framework is **generic over the prime**:

| Primitive | Effort | What's Needed |
|-----------|--------|---------------|
| **secp256k1 / P-256** | Low | New prime + curve constants, reuse Weierstrass addition |
| **BLS12-377** | Low | Same pairing structure, different prime |
| **BN254** | Low-Medium | Similar pairing-friendly structure |
| **Curve25519/Ed25519** | Already done | X25519 end-to-end verified in fiat-crypto |
| **Pasta (Pallas/Vesta)** | Low | Standard Weierstrass, new primes |
| **Hash-to-curve** | High | Needs square root compilation |
| **Multi-scalar mult** | High | Pippenger/Straus, complex loop structures |

---

## Key Technical Patterns

### Rupicola `Derive` Pipeline (used for ladderstep_correct)

```coq
(* 1. Define Gallina spec *)
Definition ladderstep_gallina ... : <<F, F, F>> := let/n ... in ...

(* 2. Define function spec *)
Instance spec_of_ladderstep : spec_of "curve_add" := fnspec! ...

(* 3. Compilation lemma for function calls *)
Lemma compile_ladderstep ... := ...

(* 4. Custom hints for non-standard operations *)
Lemma compile_load_three_b ... := ...    (* loading constants *)
Lemma tighten_bounds_FElem ... := ...    (* bounds conversion *)
Local Hint Immediate tighten_bounds_FElem : ecancel_impl.

(* 5. Derive body + correctness proof simultaneously *)
Derive ladderstep_body SuchThat
  (defn! "curve_add" (...) { ladderstep_body },
    implements @ladderstep_gallina _ three_b_val
    using [mul; add; sub; three_b_name])
  As ladderstep_correct.
Proof. compile. Qed.
```

### Bounds Tightening Pattern

When `Hbounds_eq : loose_bounds = tight_bounds`, add/sub produce `FElem (Some loose_bounds)` but mul/sub expect `FElem (Some tight_bounds)`. Fix:

```coq
Local Lemma tighten_bounds_FElem x_ptr x
  : Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x)
                    (FElem (Some tight_bounds) x_ptr x).
Proof. rewrite Hbounds_eq. reflexivity. Qed.
Local Hint Immediate tighten_bounds_FElem : ecancel_impl.
```

### bedrock2 WP proofs
`program_logic_goal_for_function! f` generates a WP goal. `straightline` processes commands one at a time, resolving loads/stores against separation logic hypotheses.

### Memory model
- `sep P Q m` = `exists mp mq, split m mp mq /\ P mp /\ Q mq`
- `Bignum n px x` = `sep (emp (length x = n)) (array scalar bytes px x)`
- `FElem px x` = `array scalar (word.of_Z 8) px (proj1_sig x)` where `x : {ws | length ws = 6}`
- `Compilation2.FElem bounds px v` = wrapped FElem with bounds checking

### Byte↔word conversion
- `Bignum_of_bytes`: `iff1 (array ptsto 1 addr bs) (Bignum n addr (bs2ws bpw bs))`
- `anybytes_to_scalar`: converts `anybytes a 8` to `scalar a x`
- `scalar_to_anybytes`: inverse direction

### Word ring
```coq
Add Ring __wring: (@word.ring_theory width word word_ok) ...
```
Enables `ring` for normalizing address arithmetic like `(px + 8) + 8` → `px + 16`.

---

## File Dependency Order

```
Tier 1 (pure math):
  WordByWordMontgomeryUtil.v
  Theory/{FieldsUtil,RingsUtil,UList,UListUtil,QuadraticExtensions,QuadraticExtensionsFiat}.v
  Theory/CubicExtensions.v                    [ring + field theory proved]
  QuadraticFieldExtensionsSpecs.v

Tier 2 (field synthesis):
  bls12_prime.v, bls12_prime_certif.v, bls12_Fp2.v
  bls12_three_b.v, bls12_three_b_Fp2.v, bls12_felem_copy.v
  bls12_from_list_F.v, bls12_from_list_Fp2.v
  ArrayUtil.v, ScalarsUtil.v

Tier 3 (field extensions):
  QuadraticFieldExtensions.v
  CubicFieldExtensionsSpecs.v                 [bedrock2 Fp6 specs]
  CubicFieldExtensions.v                      [bedrock2 Fp6 compilation]
  CompilationAbstract.v
  felem_copy.v (New/)

Tier 4 (group operations):
  BignumShift.v, CondMoveGroup.v
  StoreZero.v, StoreZeroGSpec.v, StorePointAtInfinity.v
  CurveAdd.v                                  [ladderstep_correct PROVED via Derive]
  CurveAddAlt.v, LoopBody.v

Tier 5 (scalar mult + top-level):
  ScalarMult.v, ScalarMultAlt.v
  BLS12_G1.v, BLS12_G1_alt.v, BLS12_G2.v

--- PAIRING SPEC (compiled) ---

Tier 6 (Gallina pairing specs):
  Spec/BLS12Pairing/Fp6.v           [267 LOC, compiled]
  Spec/BLS12Pairing/Fp12.v          [458 LOC, compiled]
  Spec/BLS12Pairing/Pairing.v       [581 LOC, compiled]

--- Fp12 LAYER (compiled) ---

Tier 7 (bedrock2 Fp12 compilation):
  DodecicFieldExtensionsSpecs.v     [Fp12 FieldParameters/FieldRepresentation]
  DodecicFieldExtensions.v          [Fp12 bedrock2 bodies: mul, sqr, inv, conjugate, mul_by_v]

--- PAIRING LAYER (compiled) ---

Tier 8 (bedrock2 pairing operations):
  PairingFieldOps.v                 [fp2_conjugate, fp6_mul_fp2, Frobenius ops]
  BLS12_Pairing.v                   [Full tower + Miller loop + final exp + pairing]
  BLS12_G2.v                        [G2 curve_add_G2 over Fp2 (34 ops)]

--- ALL BODIES COMPLETE ---

  WP proofs                          [38 stubs are `exact I`, need real sep-logic proofs]
  Bilinearity proof                  [mathematical theorem, not bedrock2]
```

All tiers 1–8 currently compile on Rocq 9. **Zero Admitted statements** in the group operations layer. **Zero `cmd.skip` placeholders.** The full pipeline (Fp→Fp2→Fp6→Fp12→G1→G2→Miller loop→final exponentiation→pairing) has real bedrock2 bodies. Frobenius constants for BLS12-381 are defined and loaded (Montgomery form from hax reference). WP proofs remain as stubs (38 total).

---

## Hax Reference Implementation

The SSProve-Lean hax implementation at `/home/au528660/Claude/SSProve-lean/bls-hax/src/specs/` provides tested, extraction-ready Rust code for every BLS12-381 operation including the full pairing:

| Module | File | LOC |
|--------|------|-----|
| Fp | `fp.rs` | 497 |
| Fr (scalar) | `fr.rs` | 431 |
| Fp2 = Fp[u]/(u²+1) | `fp2.rs` | 231 |
| Fp6 = Fp2[v]/(v³−ξ) | `fp6.rs` | 282 |
| Fp12 = Fp6[w]/(w²−v) | `fp12.rs` | 347 |
| G1 | `g1.rs` | 397 |
| G2 | `g2.rs` | 466 |
| Miller loop + final exp + pairing | `pairing.rs` | 283 |

Lean 4 extraction: `proofs/lean/extraction/Bls_hax.lean` (201 KB)
