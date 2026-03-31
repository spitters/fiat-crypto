# BLS12-381 Optimization Tracking

## Measured Optimization Breakdown

| # | Optimization | Before | After | Speedup | Measured? |
|---|---|---|---|---|---|
| 1 | DSD final exp (HHT algorithm) | 7,854 μs | 1,400 μs | **5.6x** | ✅ Measured |
| 2 | + Cyclotomic squaring | 1,400 μs | 1,300 μs | **1.08x** | ✅ Measured (within DSD) |
| 3 | + Copy elimination (Phase 1: add/sub) | — | — | **22-37%** on add/sub, **5-6%** on mul/sqr | ✅ Measured |
| 4 | + No-alias mul (Phase 2) | 1,400 μs | 1,171 μs | **1.20x** | ✅ Measured |
| 5 | CryptOpt Fp mul/sqr | 73 ns | 38 ns | **1.9x** on Fp mul | ✅ Measured |
| | CryptOpt vs blst Fp mul | 38 ns | 34 ns (blst) | **1.12x** gap | ✅ Measured |

### Cumulative Effect on Final Exp Hard Part

| Configuration | Time (μs) | vs baseline | vs blst |
|---|---|---|---|
| Baseline (C, naive h3) | 7,854 | 1.0x | 26.2x |
| + DSD + cyclotomic squaring | 1,400 | 5.6x | 4.7x |
| + Copy elimination + noalias | 1,171 | 6.7x | 3.9x |
| + CryptOpt (projected) | ~706 | 11.1x | 2.4x |
| blst reference | 300 | 26.2x | 1.0x |

### Full Pairing (Projected)

| Configuration | Miller | Final Exp | Total | vs blst |
|---|---|---|---|---|
| Baseline (C, naive h3) | 600 μs | 8,000 μs | 8,600 μs | 16.8x |
| All optimizations (C) | 600 μs | 1,200 μs | 1,800 μs | 3.5x |
| All + CryptOpt | ~300 μs | ~730 μs | ~1,030 μs | 2.0x |
| blst | 217 μs | 300 μs | 513 μs | 1.0x |

## Verification Status

### Fully Verified (Qed, 0 admits)

| Item | File | Status |
|---|---|---|
| All WP proofs (Fp2 through Fp12 tower) | PairingFieldOps.v | Qed |
| bls12_Fp2_mul_xi_ok | BLS12_Pairing.v | Qed |
| Cyclotomic squaring correctness | Fp12.v | Qed (`fp12_cyclotomic_sqr_correct`) |
| DSD exponent identity: 3h3 = ... | FinalExpEquiv.v | Qed (`dsd_corrected_computes_3h3`) |
| h3 = (p^4-p^2+1)/r | FinalExpEquiv.v | Qed (`h3_is_cofactor`) |

### Verified Bedrock2 Function Bodies (WP stubs)

| Item | File | Status |
|---|---|---|
| DSD hard part (HHT algorithm) | BLS12_Pairing.v | `exact I` stub |
| exp-by-x with cyclotomic squaring | BLS12_Pairing.v | `exact I` stub |
| All other pairing functions | BLS12_Pairing.v | `exact I` stubs |

Note: `exact I` means the function body is defined but the WP proof is
a trivial stub. The body IS in the verified Rocq pipeline and will be
extracted to C by ToCString. A full WP proof requires showing the body
matches the Gallina spec — this is ~200-400 lines per function following
established patterns from PairingFieldOps.v.

### Trusted (Not Verified)

| Item | File | Trust Level |
|---|---|---|
| CopyElim.v (AST rewriting pass) | CopyElim.v | Same as ToCString.v |
| apply_copy_elim.py (C post-processor) | apply_copy_elim.py | Tested, not proved |
| bls12_optimized.c (DSD + cyc_sqr C) | bls12_optimized.c | Standalone C, not extracted |
| CryptOpt Fp mul/sqr assembly | CryptOpt generated | CryptOpt verified compiler |
| ToCString.v (C code generation) | bedrock2 | Upstream trusted component |
| bls12_Fp12_mul_noalias | bls12_optimized.c | Manual C, not in Rocq |

## What Can Be Formalized

### 1. CopyElim correctness (Medium, ~300 lines)

**What**: Prove that `elim_copies` preserves the WP postcondition for
componentwise functions.

**Approach**: Per-function WP proofs. Each optimized function (without
stackalloc+copy) is proved against the SAME spec as the original. The
proof is ~50 lines shorter than the original because it skips the
stackalloc/copy handling steps.

**Formalizable?** YES — straightforward. The proofs follow the existing
PairingFieldOps.v patterns. The only difference: the sep frame uses the
input pointer directly instead of a stack copy.

### 2. No-alias mul correctness (Medium, ~100 lines)

**What**: Prove `bls12_Fp12_mul_noalias` satisfies the same spec as
`bls12_Fp12_mul` when called with non-aliased arguments.

**Approach**: The WP proof is identical to `bls12_Fp12_mul_ok` but
without the initial stackalloc+copy steps. The precondition adds
`out ≠ inx ∧ out ≠ iny` (which is trivially true when the caller
uses distinct stackalloc'd temporaries).

**Formalizable?** YES — the proof is a strict subset of the original
mul proof. The non-aliasing condition follows from the sep frame
(different FElems occupy disjoint memory).

### 3. DSD exponent correctness (Done)

**What**: The HHT algorithm computes f^{3*h3}.

**Status**: PROVED. `dsd_corrected_computes_3h3` in FinalExpEquiv.v
verifies `3*h3 = 3 + (u^2-1+p^2)*(u+1)^2*(p-u)` by `native_compute`.

### 4. DSD WP proof (Hard, ~500 lines)

**What**: Prove the bedrock2 `final_exp_hard_dsd_body` satisfies the
spec `Fp12_final_exp_hard_dsd_spec`.

**Approach**: The function body is a sequence of calls (exp-by-x,
Frobenius, mul, conjugate). Each call has an existing `spec_of`
instance. The WP proof chains them together using `weaken_call` +
`ecancel_assumption`, same pattern as the existing pairing proofs.

**Formalizable?** YES but labor-intensive. The function has ~20 calls
with inline exp-by-x loops. The loop proofs require loop invariants
tracking the exponent value (similar to `bls12_Fp12_pow_x_ok` in
BLS12_PowX.v).

### 5. CryptOpt equivalence (External)

**What**: CryptOpt's generated assembly computes the same function as
fiat-crypto's generated C.

**Status**: Proved by CryptOpt's verified compiler (separate tool).
The trust boundary is the CryptOpt compiler itself, which has its own
Rocq formalization.

## Remaining Performance Gap Analysis

The 2.0x gap (with CryptOpt) vs blst breaks down as:

| Factor | Ratio | Source |
|---|---|---|
| Fp mul | 1.12x | CryptOpt vs blst asm |
| Copy overhead in Fp12_mul | ~1.3x | bedrock2 stackalloc+copy in Karatsuba |
| Copy overhead in Fp6_mul | ~1.2x | nested copies |
| Instruction scheduling | ~1.1x | blst hand-tunes instruction interleaving |
| **Combined** | **~2.0x** | |

The copy overhead is the dominant remaining factor. Eliminating ALL copies
(not just componentwise ones) requires either:
1. Per-call-site noalias analysis (done for 2 of 7 mul calls in DSD)
2. Bedrock2 compiler change to skip copies when non-aliasing is provable
3. Full function inlining (eliminates the copy-at-boundary pattern)
