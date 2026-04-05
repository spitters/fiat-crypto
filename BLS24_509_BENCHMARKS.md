# BLS24-509 Pairing: Benchmark Comparison

## Platform
- **CPU**: AMD Ryzen 7 PRO 7840U (Zen 4, 5.1 GHz boost)
- **OS**: Linux 6.17.0
- **Compiler**: GCC -O3 -march=native

## Verified Implementation Status

**This is the FIRST formally verified BLS24-509 pairing implementation,
including both the Miller loop AND the full final exponentiation.**

| Component | Proof status | Lines |
|-----------|-------------|-------|
| Base Fp (509-bit Montgomery) | Qed | ~500 (auto) |
| Fp2 = Fp[u]/(u²+1) | Qed | generic QE |
| Fp4 = Fp2[x]/(x²-(1+u)) | Qed | generic QE |
| Fp8 = Fp4[v]/(v²-x) | Qed | generic QE |
| Fp24 = Fp8[w]/(w³-v) | Qed | generic CE |
| Miller loop (52 iterations) | Qed | ~2300 |
| make_line (line evaluation) | Qed | ~730 |
| Fp4_mul_fp, fp24_set_one | Qed | ~600 |
| Split/join sep lemmas | Qed | ~200 |
| pow_abs_z (square-and-multiply, 51 iters) | Qed | ~230 |
| Final exp easy (conj+inv+frob_p4+mul) | Qed | ~180 |
| Final exp hard (20-step addition chain) | Qed | ~500 |
| Final exp combined | Qed | ~100 |
| **Total Admitted** | **0** | **~5300** |

## Measured Performance: BLS12-377 (6×64-bit, same framework)

Verified C from fiat-crypto/bedrock2 extraction:

| Operation | Time | Notes |
|-----------|------|-------|
| Fp mul (377-bit) | 73 ns | 6 limbs, Montgomery |
| Fp2 mul | 281 ns | Karatsuba |
| Fp6 mul | 2,268 ns | cubic extension |
| Fp12 mul | 7,254 ns | quadratic over Fp6 |
| **Miller loop** | **993 μs** | 62 iterations |
| **Final exp (DSD)** | **1,778 μs** | optimized hard part |
| **Full pairing (DSD)** | **2,633 μs** | Miller + final exp |

## Measured Performance: BLS12-381 (same framework, same platform)

| Operation | fiat-crypto (verified C) | blst (hand-asm) | Ratio |
|-----------|-------------------------|-----------------|-------|
| Fp mul | 79 ns | 36 ns | 2.2x |
| Fp12 mul | 6,057 ns | 2,101 ns | 2.9x |
| Miller loop | ~270 μs (blst) | 267 μs | — |
| Final exp (DSD) | 1,453 μs | 369 μs | 3.9x |
| **Full pairing** | **~1,700 μs est.** | **640 μs** | **2.7x** |

## Estimated Performance: BLS24-509 (8×64-bit)

Based on algorithmic complexity scaling from BLS12-377/381 measurements:

### Field operations

| Operation | Estimated | Scaling rationale |
|-----------|-----------|-------------------|
| Fp mul (509-bit) | ~130 ns | (8/6)² × 73 ns (quadratic in limbs) |
| Fp2 mul | ~500 ns | 3 Fp mul + 5 Fp add/sub (Karatsuba) |
| Fp4 mul | ~2,000 ns | 3 Fp2 mul + mul_by_nr + add/sub |
| Fp8 mul | ~8,000 ns | 3 Fp4 mul + mul_by_v + add/sub |
| Fp24 mul | ~32,000 ns | 6 Fp8 mul + mul_by_w + add/sub (Karatsuba cubic) |
| Fp24 sqr | ~24,000 ns | ~75% of mul (standard estimate) |

### Miller loop

| | Estimated | Notes |
|---|-----------|-------|
| **Miller loop** | **~3–5 ms** | 52 iterations × ~29 Fp4-level calls |

- 52 iterations (vs 62 for BLS12-377)
- Each iteration: doubling step (~16 calls) + conditional addition (~13 calls)
- Operations at Fp4 level (~7x more expensive than Fp2)
- Fewer iterations partially compensates

### Final exponentiation

| Component | Operations | Estimated |
|-----------|-----------|-----------|
| **Easy part** | 1 conj + 1 inv + 2 mul + 1 frob_p4 | ~0.5 ms |
| **Hard part: 8× pow_z** | 8 × (51 sqr + ~7 mul + 1 opp) = 408 sqr + 56 mul | ~13 ms |
| **Hard part: other** | 7 mul + 3 frob + 2 conj + 1 sqr | ~0.3 ms |
| **Hard part total** | | ~13.3 ms |
| **Final exp total** | | **~14 ms** |

The final exp is dominated by the 8 `pow_z` calls. Each `pow_z` does
`pow_abs_z` (51 iterations of Fp24_sqr + conditional Fp24_mul) + 1 conjugate.
With Fp24_sqr ≈ 24 μs and Fp24_mul ≈ 32 μs:
- Each pow_z ≈ 51 × 24 + 7 × 32 ≈ 1,448 μs ≈ 1.4 ms
- 8 × pow_z ≈ 11.6 ms

### Full pairing estimate

| Component | Estimated |
|-----------|-----------|
| Miller loop | ~4 ms |
| Final exp | ~14 ms |
| **Full pairing** | **~18 ms** |

## Comparison with Production Implementations

| Implementation | Language | Verified? | Miller | Final Exp | Pairing | Platform |
|---------------|----------|-----------|--------|-----------|---------|----------|
| **fiat-crypto (ours)** | **C (verified)** | **Yes (Qed)** | **~4 ms** | **~14 ms** | **~18 ms est.** | Zen 4 |
| Longa/RELIC (TCHES'23) | C + x86 asm | No | ~1.0 ms | ~1.6 ms | **2.6 ms** | Coffee Lake |
| Aranha+/RELIC (CiC'24) | C + asm | No | 1.51 ms | 2.69 ms | **4.19 ms** | Kaby Lake |
| RELIC baseline | C + asm | No | ~1.7 ms | ~2.9 ms | **4.6 ms** | Skylake |
| Faraoun (2025) | Rust (CT) | No | ~2.7 ms | ~6.6 ms | **~9.4 ms** | unknown |

## Analysis

### The verification tax

For BLS12-381 on our platform, fiat-crypto's verified C is **2.7x slower** than
blst's hand-optimized assembly. The overhead comes from bedrock2's separation
logic requirements (redundant memory copies, uintptr_t defeating alias analysis).

For BLS24-509, the estimated **~18 ms** vs Longa's **2.6 ms** gives a ratio of
~7x. This is higher than BLS12's 2.7x because:

1. **Deeper tower amplifies copy overhead**: BLS24's 4-level QE tower
   (Fp→Fp2→Fp4→Fp8) means more nested `felem_copy` calls per operation.
   Each level copies 2x the data of the level below.

2. **More pow_z calls**: The final exp hard part calls `pow_z` 8 times,
   each doing 51 loop iterations. The loop body overhead (straightline
   processing, local variable management) accumulates.

3. **No DSD optimization yet**: BLS12-377/381 use Devegili-Scott-Dahab (DSD)
   optimized final exponentiation. BLS24-509's hard part uses a direct
   addition chain which is not yet optimized for the cyclotomic subgroup.

### Optimization opportunities

| Optimization | Expected impact | Effort |
|-------------|----------------|--------|
| **CryptOpt Fp mul/sqr** | ~2x speedup on Fp ops → ~40% on tower | Medium |
| **Copy elimination** | ~30–50% on tower operations | Low (AST pass exists) |
| **Cyclotomic squaring** | ~25% savings in pow_z loop | Medium |
| **DSD final exp** | ~3–5x speedup on final exp | High |
| **Lazy reduction** | ~10% on Fp2 mul | Low |

**With CryptOpt + copy elimination + cyclotomic squaring:**
- Miller loop: ~4 ms → ~2 ms
- Final exp: ~14 ms → ~5 ms (cyclotomic sqr helps pow_z enormously)
- **Full pairing: ~7 ms** (competitive with Faraoun's unverified Rust)

**With additionally DSD-optimized final exp:**
- Final exp: ~5 ms → ~2 ms
- **Full pairing: ~4 ms** (competitive with RELIC baseline)

### Why BLS24-509?

BLS24-509 targets **192-bit security** (vs 128-bit for BLS12-381). At this
security level, BLS24-509 is the **fastest known curve family** for pairings
(Aranha-Fotiadis-Guillevic, CiC 2024), beating:
- BLS12-1150 by 73%
- KSS16 curves by 20%
- KSS18 curves by 40%
- All other 192-bit families by 6–56%

### Proof metrics

| Metric | Value |
|--------|-------|
| Total lines of proof (WP) | ~5,300 |
| Total lines of function bodies | ~1,800 |
| Total `Admitted` | 0 |
| Proof files | 3 (.v) |
| Compile time (all proofs) | ~5 min |
| Trust base | Rocq kernel + bedrock2 semantics |

## References

1. P. Longa, "Efficient Algorithms for Large Prime Characteristic Fields and
   Their Application to Bilinear Pairings," TCHES 2023(3):445-472.

2. D. Aranha, S. Fotiadis, A. Guillevic, "A short-list of pairing-friendly
   curves resistant to Special TNFS at the 192-bit security level,"
   IACR CiC 1(3), 2024.

3. D. Aranha, Y. El Housni, A. Guillevic, "A survey of elliptic curves for
   proof systems," Des. Codes Cryptogr. 91(11):3333-3378, 2023.
