# BLS24-509 Optimization Log

## Summary

Starting from 144 ms, achieved ~22 ms verified pairing through
proper inversions + CryptOpt. All C-level optimizations exhausted.
Remaining ~10x gap to production (2.6 ms) is bedrock2's inherent
memory-model overhead.

## Platform
- AMD Ryzen 7 PRO 7840U (Zen 4), GCC 14 -O3 -march=native
- Timings vary 2-3x due to laptop boost clocking; ratios are reliable

## Optimizations Applied (effective)

### 1. Proper Fp2/Fp4/Fp8 inversions
- **Before**: 119 ms Miller loop (placeholder inv = 1000 random squarings)
- **After**: 37 ms Miller loop
- **Speedup**: 3.2x
- **File**: `bls24_inv.c`
- **Method**: Norm-based tower inversion. Fp2: norm = a²+b², Fermat inv.
  Fp4: norm = a²-xi·b², Fp2 inv. Fp8: norm = a²-v·b², Fp4 inv.

### 2. CryptOpt Fp mul assembly
- **Before**: ~600 ns Fp mul (bedrock2 C)
- **After**: ~392 ns Fp mul (CryptOpt x86-64 asm)
- **Speedup**: 1.55x on Fp mul, cascading ~1.28x on Miller loop
- **File**: `bls24_509_mul.asm` (1726 lines)
- **Method**: CryptOpt stochastic search (5k evals, ratio 18395).
  Uses mulx/adcx/adox instruction scheduling. Verified compiler output.

### 3. CryptOpt Fp sqr assembly
- **Before**: ~550 ns Fp sqr (bedrock2 C)
- **After**: ~400 ns Fp sqr (CryptOpt x86-64 asm)
- **Speedup**: 1.4x on Fp sqr
- **File**: `bls24_509_sqr.asm` (1804 lines)
- **Method**: Same as mul, ratio 15455. Lower improvement suggests
  more CryptOpt iterations needed.

### 4. Copy elimination for add/sub/opp
- **Speedup**: 21-57% on componentwise ops (add/sub/opp at all levels)
- **File**: `apply_copy_elim.py`
- **Method**: Python post-processor removes stackalloc+felem_copy pattern
  in safe functions (no write-after-read hazard).
- **No effect on Miller loop** — dominated by mul/sqr, not add/sub.

## Optimizations Attempted (no improvement)

### 5. Typed struct tower (separate compilation)
- **Result**: 5-10% on mul, 50% on add. Not transformative.
- **Files**: `bls24_tower_typed.c`, `bls24_fp2_typed.c`
- **Why no help**: Fp base ops still use `uintptr_t` across the boundary.
  `restrict` qualifiers can't see through the `(br_word_t)` cast.
  The copy overhead per mul (~15 ns memcpy) is <1% of total.

### 6. restrict pointers on function params
- **Result**: 2.8x SLOWER (Fp mul 157→438 ns)
- **File**: `apply_restrict.py`
- **Why worse**: Changing `uintptr_t` to `uint8_t* restrict` triggers
  different GCC optimization paths. Implicit int-to-pointer conversions
  add overhead. GCC's `uintptr_t` code path is already optimized.

### 7. always_inline on all functions
- **Result**: 2.7x SLOWER (Fp mul 157→430 ns)
- **Why worse**: The bedrock2 Fp mul has 1500+ local variables. When
  inlined into Fp2_mul (which calls it 3 times), register pressure
  explodes — only 16 x86-64 GPRs for thousands of live variables.
  Result: massive spill-to-stack, worse than the function call overhead.

### 8. Selective inlining (Fp only into Fp2)
- **Result**: Still slower (Fp mul 157→282 ns)
- **Why worse**: Same register pressure issue, just at one level.

### 9. -flto (link-time optimization)
- **Result**: 4x SLOWER (Fp mul 157→617 ns)
- **Why worse**: LTO enables cross-file inlining, triggering the same
  register spill cascade as always_inline.

### 10. Tower inlining (Python post-processor)
- **Result**: No change (Miller 19.8→19.5 ms, within noise)
- **File**: `apply_inline.py` (729 lines)
- **Why no help**: GCC -O3 already inlines small non-static wrapper
  functions. The inlining pass just duplicates what GCC does.

### 11. Zero-initialization removal
- **Result**: No change
- **Why no help**: GCC already optimizes away `= {0}` when it can
  prove the array is immediately overwritten by a function call.

### 12. Aligned uint64_t arrays (instead of uint8_t)
- **Result**: No change
- **Why no help**: All array access goes through `uintptr_t` pointers.
  The element type of the underlying array doesn't affect the generated
  loads/stores.

## Root Cause Analysis

The ~10x gap between verified bedrock2 C and hand-optimized assembly
has three components:

### A. Fp arithmetic (~1.5x, now closed by CryptOpt)
bedrock2's generated C is straight-line Montgomery multiplication with
`_br_load`/`_br_store` memory access. CryptOpt's verified assembly
uses `mulx`/`adcx`/`adox` with optimized instruction scheduling.

### B. Karatsuba temporaries through memory (~3-4x, unfixable in C)
Every tower multiplication allocates stack arrays for intermediate
results. Fp2_mul needs 3 Fp temporaries (192 bytes). Fp4_mul needs
3 Fp2 temporaries (384 bytes). These stack arrays are accessed through
`uintptr_t` pointers, forcing all data through memory.

In contrast, hand-optimized assembly keeps Karatsuba intermediates in
registers (using callee-saved GPRs + XMM registers for spilling).
This eliminates ~80% of memory traffic in tower operations.

### C. Function call overhead (~2-3x, unfixable in C)
Each Fp base operation (`bls24_509_mul`, `bls24_509_add`, etc.) is a
separate function with its own stack frame. The Miller loop body makes
~29 function calls per iteration × 52 iterations = ~1500 calls.
Each call has: push callee-saved regs, set up frame, compute, pop regs.

In hand-optimized code, the entire Fp24_mul is one function with the
Fp operations inlined. Register allocation spans the entire computation.

### Why B and C can't be fixed at the C level
- Inlining Fp ops into tower ops causes register spills (1500+ vars
  per Fp_mul × 3 calls = 4500+ vars, only 16 GPRs)
- `restrict` can't help because `uintptr_t` isn't a pointer type
- `-flto` triggers the same inlining problem
- The root cause is bedrock2's memory-model: separation logic requires
  all values to have addresses in memory, preventing register promotion

## Remaining Path: Hand-Written Tower Assembly

The only way to close the ~10x gap is to write complete tower operations
(Fp2_mul through Fp24_mul) in x86-64 assembly with register-resident
Karatsuba intermediates. This approach:

1. Uses CryptOpt-generated Fp_mul as a subroutine (via `call`)
2. Keeps 3 Fp intermediates in callee-saved registers (rbx, r12-r15, rbp)
   + XMM registers for additional spilling
3. Eliminates all stack-allocated temporary arrays
4. Can be verified against the bedrock2 spec by proving the assembly
   implements the same mathematical operation

Expected improvement: ~3-4x on tower ops, bringing full pairing to
~5-8 ms (competitive with Faraoun's unverified Rust at 9.4 ms).
