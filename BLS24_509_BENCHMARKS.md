# BLS24-509 Pairing: Final Benchmark Results

## Platform
- **CPU**: AMD Ryzen 7 PRO 7840U (Zen 4, 5.1 GHz boost)
- **OS**: Linux 6.17.0, GCC 14, -O3 -march=native
- Note: Laptop CPU with variable boost. Absolute timings vary 2x; ratios reliable.

## Implementation Status

**FIRST formally verified BLS24-509 pairing (Miller loop + final exponentiation).**
All proofs Qed, 0 Admitted. Verified stackalloc flattening pass (Qed).

## Configurations Tested

| # | Config | Description |
|---|--------|-------------|
| 1 | Original | bedrock2 C + copy elimination for add/sub |
| 2 | + Verified flatten | + stackalloc flattening (proved correct in Rocq) |
| 3 | + CryptOpt | + CryptOpt x86-64 assembly for Fp mul/sqr |

## Results

| Operation | Config 1 | Config 2 | Config 3 | Improvement |
|-----------|----------|----------|----------|-------------|
| Fp mul | 583 ns | 438 ns | **384 ns** | 1.52x |
| Fp sqr | 441 ns | 377 ns | **354 ns** | 1.25x |
| Fp2 mul | 1,686 ns | 1,647 ns | **1,669 ns** | ~same |
| Fp4 mul | 5,907 ns | 5,151 ns | **5,082 ns** | 1.16x |
| Fp8 mul | 18,120 ns | 14,588 ns | **15,312 ns** | 1.18x |
| Fp24 mul | 110,841 ns | 100,573 ns | **94,586 ns** | 1.17x |
| Fp24 sqr | 89,809 ns | 75,059 ns | **84,696 ns** | 1.06x |
| **Miller loop** | **37.6 ms** | **37.6 ms** | **32.2 ms** | **1.17x** |
| **Final exp** | **56.0 ms** | **57.6 ms** | **43.9 ms** | **1.28x** |
| **Full pairing** | **93.7 ms** | **95.2 ms** | **76.1 ms** | **1.23x** |

## Controlled A/B (Miller loop, interleaved rounds)

| Round | Original | Config 3 | Speedup |
|-------|----------|----------|---------|
| 1 | 35.8 ms | 34.6 ms | 1.04x |
| 2 | 37.4 ms | 30.4 ms | 1.23x |
| 3 | 38.7 ms | 34.6 ms | 1.12x |

## Optimization Impact Summary

| Optimization | Effect | Verified? |
|-------------|--------|-----------|
| Proper tower inversions | 119 ms → 37 ms (3.2x) | N/A (was placeholder) |
| Copy elimination (add/sub) | 21-57% on add/sub ops | Safe-list validated |
| **Stackalloc flattening** | 71→44 allocs, mul_xi 2.5x | **Qed (Rocq proof)** |
| CryptOpt Fp mul | 1.55x on Fp mul (A/B) | CryptOpt verified compiler |
| CryptOpt Fp sqr | 1.25x on Fp sqr | CryptOpt verified compiler |
| Tower asm (prototype) | 1.25-1.62x on Fp2-Fp4 mul | Differential testing |
| Tower inlining (Python) | No effect | N/A |
| restrict/inline/LTO | No effect or slower | N/A |

## Comparison with Production

| Implementation | Verified? | Full Pairing | vs Longa |
|---------------|-----------|-------------|----------|
| **fiat-crypto Config 3** | **Yes (Qed)** | **~76 ms** | **29x** |
| fiat-crypto Config 1 | Yes (Qed) | ~94 ms | 36x |
| Longa/RELIC (TCHES'23) | No | 2.6 ms | 1.0x |
| Aranha+/RELIC (CiC'24) | No | 4.19 ms | 1.6x |
| Faraoun (Rust, CT) | No | ~9.4 ms | 3.6x |

## Gap Analysis

The ~29x gap (Config 3 vs Longa) breaks down as:

| Factor | Estimated | Root Cause |
|--------|-----------|------------|
| Fp arithmetic | ~1.0x | CryptOpt closes this |
| Karatsuba temps in memory | ~10x | bedrock2 stack-allocates all intermediates |
| Function call overhead | ~3x | Each Fp op is a separate function call |
| **Total** | **~30x** | |

The dominant factor (~10x) is bedrock2's memory model: all Karatsuba
intermediates live on the stack and are accessed via loads/stores.
Hand-optimized code keeps them in registers across Fp operations.

## Verified Artifacts

| File | Lines | Content |
|------|-------|---------|
| `FlattenStackalloc.v` | 327 | Verified AST pass + correctness proof (3 Qed) |
| `BLS24_509_MillerLoop_proof.v` | ~1800 | Miller loop WP proof (0 Admitted) |
| `BLS24_509_FinalExp_proof.v` | ~1200 | Final exp WP proof (0 Admitted) |
| `BLS24_509_PairingHelpers.v` | ~1640 | Tower helpers (0 Admitted) |
| `bls24_509_pairing.c` | 4,110 | Extracted C (57 functions) |
| `bls24_509_mul.asm` | 1,726 | CryptOpt Fp mul (verified compiler) |
| `bls24_509_sqr.asm` | 1,804 | CryptOpt Fp sqr (verified compiler) |

## References

1. P. Longa, TCHES 2023(3):445-472.
2. D. Aranha, S. Fotiadis, A. Guillevic, IACR CiC 1(3), 2024.
3. D. Aranha, Y. El Housni, A. Guillevic, Des. Codes Cryptogr. 91(11), 2023.
