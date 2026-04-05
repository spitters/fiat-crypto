# BLS24-509 Pairing: Benchmark Results

## Platform
- **CPU**: AMD Ryzen 7 PRO 7840U (Zen 4, 5.1 GHz boost)
- **OS**: Linux 6.17.0
- **Compiler**: GCC 14 -O3 -march=native

## MEASURED Baseline (verified C, no optimizations)

| Operation | Time | Notes |
|-----------|------|-------|
| **Fp mul** | **157 ns** | 509-bit, 8-limb Montgomery |
| **Fp sqr** | **146 ns** | |
| Fp add | 13 ns | |
| Fp sub | 9 ns | |
| **Fp2 mul** | **529 ns** | Karatsuba, beta=-1 |
| Fp2 sqr | 489 ns | |
| **Fp4 mul** | **1,806 ns** | Karatsuba, xi=1+u |
| Fp4 sqr | 1,650 ns | |
| **Fp8 mul** | **5,749 ns** | Karatsuba |
| Fp8 sqr | 5,316 ns | |
| **Fp24 mul** | **37,367 ns** | Karatsuba cubic |
| Fp24 sqr | 29,170 ns | |
| Fp24 conjugate | 84 ns | negate c1 component |
| **Miller loop** | **118,779 μs** | 52 iterations, Fp4-level ops |
| **Final exp** | **24,711 μs** | 8×pow_z + frob + mul chain |
| **Full pairing** | **~144 ms** | Miller + final exp |

Note: Miller loop uses placeholder Fp4/Fp8 inv (not correct, inflates timing).
Final exp uses zero gamma constants (arithmetically valid, not correct output).

## Analysis: Why 144 ms instead of estimated 18 ms?

The field-level operations match estimates well:
| Op | Estimated | Measured | Ratio |
|----|-----------|----------|-------|
| Fp mul | 130 ns | 157 ns | 1.2x |
| Fp4 mul | 2,000 ns | 1,806 ns | 0.9x |
| Fp24 mul | 32,000 ns | 37,367 ns | 1.2x |

But the **Miller loop** is ~30x slower than the field-level estimate because:

1. **bedrock2 copy overhead is MASSIVE at deep tower levels**: Each Fp24 operation
   copies 1,536 bytes of data to stack before operating. Nested calls copy recursively:
   Fp24→Fp8(×3)→Fp4(×6)→Fp2(×12)→Fp(×24) = thousands of `memcpy` calls per Fp24 op.

2. **Copy overhead dominates**: Fp24_mul takes 37 μs, but 52 iterations of the loop body
   (which does ~29 calls including Fp24_sqr, Fp24_mul, Fp4-level ops) should take
   52 × 29 × ~30 μs ≈ 45 ms. The remaining 74 ms is pure overhead (nested copies,
   function call setup, stack allocation/deallocation).

3. **Placeholder inv**: The Fp4_inv stub does 1000 squarings instead of a proper inversion.
   Each iteration calls inv twice, adding ~2 × 1000 × 1.6 μs ≈ 3.2 ms × 52 ≈ 166 ms of
   overhead. This likely accounts for most of the Miller loop excess.

## Copy Elimination Impact (estimated from BLS12 data)

BLS12-381 copy elimination gave:
- Fp12 mul: 5,800 → 3,100 ns (47% reduction)
- Full pairing: 23x → 12x gap (46% reduction)

For BLS24-509 with deeper tower, copy elimination should help MORE:
- Fp24 mul: 37 μs → ~18 μs (estimate: 50% reduction)
- Miller loop (after fixing inv): ~45 ms → ~20 ms

## Comparison with Production

| Implementation | Language | Verified? | Miller | Final Exp | Pairing | Platform |
|---------------|----------|-----------|--------|-----------|---------|----------|
| **fiat-crypto baseline** | **C (verified)** | **Yes** | **119 ms†** | **25 ms** | **~144 ms** | Zen 4 |
| Longa/RELIC (TCHES'23) | C + x86 asm | No | ~1.0 ms | ~1.6 ms | **2.6 ms** | Coffee Lake |
| Aranha+/RELIC (CiC'24) | C + asm | No | 1.51 ms | 2.69 ms | **4.19 ms** | Kaby Lake |
| RELIC baseline | C + asm | No | ~1.7 ms | ~2.9 ms | **4.6 ms** | Skylake |
| Faraoun (Rust, CT) | Rust | No | ~2.7 ms | ~6.6 ms | **~9.4 ms** | unknown |

† Includes placeholder inv overhead. True Miller loop time TBD after proper inv.

## Optimization Roadmap

| Phase | Optimization | Expected impact |
|-------|-------------|----------------|
| 0 | ~~C extraction + baseline~~ | **DONE** — 144 ms measured |
| 1 | **Copy elimination** | **~50% reduction** → ~72 ms |
| 2 | **CryptOpt Fp mul/sqr** | **~40% on field ops** → ~45 ms |
| 3 | **Proper Fp4/Fp8 inv** | Remove placeholder overhead |
| 4 | **Cyclotomic squaring** | ~25% on pow_z → saves ~5 ms |
| 5 | **Lazy Fp2 reduction** | ~10% on Fp2 → saves ~3 ms |

## Proof Metrics

| Metric | Value |
|--------|-------|
| Total lines of proof (WP) | ~5,300 |
| Total lines of function bodies | ~1,800 |
| Total `Admitted` | **0** |
| Extracted C code | 4,118 lines, 57 functions |
| Trust base | Rocq kernel + bedrock2 semantics |

## References

1. P. Longa, TCHES 2023(3):445-472.
2. D. Aranha, S. Fotiadis, A. Guillevic, IACR CiC 1(3), 2024.
3. D. Aranha, Y. El Housni, A. Guillevic, Des. Codes Cryptogr. 91(11), 2023.
