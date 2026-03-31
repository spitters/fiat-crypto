# BLS12-381 Pairing Performance Analysis

## Benchmark Results (2026-03-31)

### Fp-level operations

| Operation | fiat-crypto (C) | CryptOpt (asm) | blst (asm) | CryptOpt speedup |
|-----------|-----------------|----------------|------------|-------------------|
| Fp mul    | 70 ns           | 37 ns          | ~22 ns     | 1.9x              |
| Fp sqr    | 66 ns           | 38 ns          | ~20 ns     | 1.7x              |
| Fp add    | 7 ns            | (same)         | ~3 ns      | -                 |
| Fp sub    | 6 ns            | (same)         | ~3 ns      | -                 |

CryptOpt assembly from: https://github.com/0xADE1A1DE/CryptOpt/tree/main/generated/bls12

### Tower operations

| Operation | fiat-crypto (C) | With CryptOpt | blst |
|-----------|-----------------|---------------|------|
| Fp2 mul   | 268 ns          | ~140 ns       | ~66 ns |
| Fp12 mul  | 5,800 ns        | ~3,100 ns     | ~900 ns |
| Fp12 sqr  | 4,500 ns        | ~2,400 ns     | ~650 ns |

### Full pairing projections

| Configuration | Miller loop | Final exp | **Total** | **vs blst** |
|--------------|------------|-----------|-----------|-------------|
| Baseline (C, naive h3) | 543 μs | 9,472 μs | **10,015 μs** | 23x |
| + CryptOpt Fp mul/sqr | 287 μs | 5,007 μs | **5,294 μs** | 12x |
| + DSD final exp (corrected) | 287 μs | 948 μs | **1,235 μs** | 2.8x |
| + Cyclotomic squaring | 287 μs | 865 μs | **1,153 μs** | 2.6x |
| + Lazy reduction | 261 μs | 788 μs | **~1,049 μs** | 2.4x |
| blst (hand-optimized asm) | 187 μs | 249 μs | **436 μs** | 1.0x |

## Optimization Status

### Implemented and verified
- **DSD final exponentiation**: Corrected Hayashida-Hayasaka-Teruya algorithm.
  Gallina model proved correct: `3*h3 = 3 + (u²-1+p²)*(u+1)²*(p-u)`.
  Reduces hard part from 1268-bit to ~320-bit exponentiation (~4x speedup).
- **Cyclotomic squaring**: `fp12_cyclotomic_sqr_correct` in Fp12.v (Qed).
  Uses 1 Fp6_mul + 1 Fp6_mul_by_v instead of 2 Fp6_mul + 1 Fp6_sqr (~11% savings).

### Implemented, not verified
- **CryptOpt Fp mul/sqr**: Drop-in x86-64 assembly from CryptOpt's verified
  compiler. 1.9x speedup on Fp mul.
- **Lazy Fp2 reduction**: Skip 2 Fp reductions per Karatsuba Fp2 mul (~9%).
  Exploits Montgomery multiplier's tolerance for loose inputs (< 2p).

### Not effective
- **GCC `always_inline` + uninitialized stack**: Tested, no improvement.
  GCC `-O3` already inlines and optimizes stack allocation.
- **Asm Fp add/sub**: fiat-crypto's generated add/sub is already optimal
  under GCC `-O3`. Hand-written `__int128` version was slower.
- **NAF for exp-by-x**: BLS12-381's parameter x already has Hamming weight 6,
  same as its NAF representation. No benefit.

## The Remaining 2.4x Gap: Root Cause Analysis

### Why bedrock2 generated C is slower than hand-optimized asm

The dominant overhead is **not** the Fp arithmetic — it's the generated code structure.
Measured: Fp12_mul takes 5,800 ns, but only ~1,260 ns (22%) is Fp multiplications.
The other 78% is overhead from bedrock2's code generation pattern.

#### 1. Redundant memory copies (biggest factor)

bedrock2's separation logic requires proving memory non-aliasing. The generated
C achieves this by **copying inputs to local stack** before every operation:

```c
void bls12_Fp6_add(uintptr_t out, uintptr_t inx, uintptr_t iny) {
    uint8_t _br2_stackalloc_allocx[288];  // 288 bytes copied
    uint8_t _br2_stackalloc_allocy[288];  // 288 bytes copied
    allocx = (uintptr_t)&_br2_stackalloc_allocx;
    allocy = (uintptr_t)&_br2_stackalloc_allocy;
    bls12_Fp6_felem_copy(allocx, inx);     // copy 288 bytes
    bls12_Fp6_felem_copy(allocy, iny);     // copy 288 bytes
    bls12_Fp2_add(out, allocx, allocy);    // operate on copies
    bls12_Fp2_add(out+96, allocx+96, allocy+96);
    bls12_Fp2_add(out+192, allocx+192, allocy+192);
}
```

For Fp12_mul, this pattern nests: Fp12 copies Fp6 operands, Fp6 copies Fp2 operands,
Fp2 copies Fp operands. Total: thousands of bytes copied per Fp12 operation.

#### 2. uintptr_t defeats alias analysis

bedrock2 uses `uintptr_t` (integer) for all memory addresses, not typed pointers.
This prevents GCC/Clang from doing alias analysis:

```c
// GCC sees integers, not pointers — can't prove non-aliasing
void fp_add(uintptr_t out, uintptr_t a, uintptr_t b);
```

Even with all functions inlined, GCC cannot eliminate the copies because it can't
prove `out` doesn't alias with `a` or `b` through the integer-to-pointer casts.

#### 3. No register allocation across operations

bedrock2 stores all intermediates in stack memory. In contrast, blst keeps
Fp2 Karatsuba intermediates in registers across the 3 Fp multiplications,
avoiding 6 × 48 = 288 bytes of memory traffic per Fp2 mul.

### Can we fix this in GCC/Clang?

**Option A: Teach the compiler about the copy-then-read pattern**

The pattern `memcpy(local, src, N); f(local); // f only reads local` could be
optimized to `f(src)` if the compiler can prove `src` is not modified between
the copy and the last read. This is a form of **copy propagation through memory**.

GCC's `-ftree-dse` (dead store elimination) and `-ftree-fre` (full redundancy
elimination) come close but fail because:
- The `uintptr_t` cast breaks the pointer provenance chain
- The compiler can't track that the callee only reads (not writes) the copy

A GCC plugin or LLVM pass that recognizes this pattern specifically for
bedrock2-generated code could be valuable. The pass would:
1. Detect: `memcpy(stack_local, src, N)` followed by calls using `stack_local`
2. Verify: `src` is not modified between the copy and last use
3. Replace: uses of `stack_local` with `src` directly

**Option B: Change bedrock2's C backend to use typed pointers**

Replace `uintptr_t` with `const uint64_t *restrict` for function parameters.

**Tested (2026-03-31):** Adding `restrict`-qualified `uint8_t*` aliases via
`#define` macros in each function body. Result: **no measurable improvement**.
GCC generates identical assembly because the restrict info is lost when
casting back to `uintptr_t` for callee arguments.

**Root cause:** restrict must propagate through the ENTIRE call chain.
`bls12_Fp6_add` calls `bls12_Fp2_add(uintptr_t, uintptr_t, uintptr_t)`,
and GCC can't see into this extern callee to know it won't modify the
restrict-qualified memory through the integer argument.

**What would actually work:** change ALL function signatures from `uintptr_t`
to `const uint64_t *restrict` / `uint64_t *restrict`. This is a fundamental
change to bedrock2's C calling convention (ToCString.v + prelude). The load/store
helpers would need to take `uint64_t*` instead of `uintptr_t`. This propagates
restrict info through the entire call chain, enabling GCC to eliminate copies.

Estimated: ~50 lines in ToCString.v. Does not affect WP proofs (ToCString is
an unverified pretty-printer).

**Option C: Post-processing pass on the generated C**

A simple text-processing pass that:
1. Identifies `felem_copy(local, input)` calls
2. Checks that `local` is only passed as a read-only argument
3. Replaces `local` with `input` in subsequent calls
4. Removes the dead copy

This is ~100 lines of Python/sed and could be verified by differential testing
(run both versions on test vectors and compare results).

**Option D: Custom LLVM pass**

An LLVM optimization pass that operates on the IR level, after inlining.
It would recognize the `load-store-to-stack; load-from-stack` pattern
and short-circuit it. LLVM's MemorySSA framework provides the alias
analysis infrastructure. Estimated: ~500 lines of C++.

### What we tested (2026-03-31)

**Option B (restrict pointers): tested, no effect.**
Added `uint8_t *restrict` aliases to function parameters via `#define` macros
and a Python post-processor. GCC generates identical assembly because the
copies are explicit in the source code — `restrict` prevents the compiler from
ADDING aliasing assumptions but cannot REMOVE explicit `memcpy` calls.

**`always_inline` + uninitialized stack: tested, no effect.**
GCC `-O3` already inlines static functions and optimizes stack allocation.

**Asm Fp add/sub: tested, slower.** The generated C add/sub is already optimal
under GCC `-O3`. Hand-written `__int128` version was slower due to suboptimal
register allocation.

### Root cause (confirmed)

The copies are **explicit in the bedrock2-generated source code** — they are
`felem_copy()` calls emitted by bedrock2's code generator to satisfy separation
logic non-aliasing requirements. No C compiler optimization can remove them
because they are semantically meaningful from C's perspective.

### Correct fix: CopyElim.v (AST-level transformation)

The fix must happen at the bedrock2 AST level, BEFORE C code generation.
`CopyElim.v` implements an AST rewriting pass:

```
Pattern:  stackalloc x N; felem_copy(x, src); body(x)
Rewrite:  x := src; body(x)
```

**Safety analysis** (which functions can skip copies):

| Function type | Safe? | Reason |
|--------------|-------|--------|
| add, sub, opp | YES | Each sub-call writes to a non-overlapping output slice; input slices are read before any write |
| felem_copy, conjugate | YES | Same property |
| mul, square | NO | Karatsuba reads `x.c0 + x.c1` AFTER writing `out.c0` — aliased `out==inx` corrupts the read |
| inv, frobenius | NO | Complex data flow with cross-component dependencies |

**Verification approach**: Per-function WP proofs. Each optimized function
is proved directly against its spec. The proof is SIMPLER than the original
(fewer steps: no stackalloc, no copy, no dealloc). No generic exec simulation
theorem needed.

Why per-function is better than a generic simulation:
- Generic simulation requires ~300 lines of induction on `exec` (12 constructors)
  + memory indistinguishability + compositional read-only property for callees
- Per-function proofs reuse the existing WP proof structure with fewer steps
- The allowlist is small and manually verified

### Recommendation

1. **CopyElim.v AST pass** (implemented): wire into extraction, benchmark
2. **Per-function WP proofs**: prove optimized add/sub/opp satisfy same specs
3. **Phase 2 (no-copy mul variants)**: create `mul_nocopy` for non-aliased call sites

Expected impact: eliminating copies would reduce Fp12_mul from 5,800 ns to
~2,500 ns (the "CryptOpt only" projection), giving a full pairing of ~540 μs
(1.2x of blst) with CryptOpt + DSD + cyclotomic squaring.
