# Plan: bedrock2 Copy Elimination for Tower Arithmetic

## Problem

bedrock2-generated C copies ALL function inputs to local stack before every call:
```c
void Fp6_add(out, inx, iny) {
    allocx = stackalloc(288); allocy = stackalloc(288);
    felem_copy(allocx, inx);  // 288 bytes copied
    felem_copy(allocy, iny);  // 288 bytes copied
    Fp2_add(out, allocx, allocy);  // operates on copies
    ...
}
```
This accounts for ~78% of tower arithmetic overhead (Fp12_mul: 5800 ns actual vs
~1260 ns of Fp multiplications). Eliminating copies would close the gap from 2.4x
to ~1.2x of blst.

GCC cannot remove these copies (tested: restrict pointers, always_inline, -O3).
The copies are in the source code; the fix must be at the bedrock2 level.

## Safety Analysis

**Safe to eliminate (componentwise operations):**
- `Fp*_add`, `Fp*_sub`, `Fp*_opp`: each sub-call operates on a non-overlapping
  slice. Even with `out == inx`, slice N is read before being written.
- `Fp*_felem_copy`, `Fp*_conjugate`: same property.

**NOT safe (cross-component reads after output writes):**
- `Fp*_mul`, `Fp*_square`: Karatsuba reads `x.c0 + x.c1` AFTER writing `out.c0`.
  If `out == inx`, the read sees corrupted data. Copies required for in-place.
- `Fp*_inv`, `Fp*_frobenius`: complex data flow, copies required.

## Approach: AST-level rewriting pass

### New file: `CopyElim.v` (~100 lines)

A Rocq function that rewrites the bedrock2 cmd AST:

```
Pattern:  cmd.stackalloc x N (cmd.seq (cmd.call [] copy [x; src]) rest)
Replace:  cmd.seq (cmd.set x (expr.var src)) (elim_copies rest)
```

This substitutes the stack allocation + copy with a direct pointer assignment.
Applied selectively to functions on an allowlist.

### Allowlist (safe_fns)

```
bls12_Fp2_add, bls12_Fp2_sub, bls12_Fp2_opp,
bls12_Fp6_add, bls12_Fp6_sub, bls12_Fp6_opp,
bls12_Fp12_add, bls12_Fp12_sub, bls12_Fp12_opp,
bls12_Fp12_conjugate
```

### Wiring: modify C extraction

```coq
Definition all_funcs_optimized :=
  elim_copies_funcs copy_fn_names safe_fn_names all_funcs.
Definition all_c_optimized := Eval vm_compute in c_module all_funcs_optimized.
```

## Expected Impact

| Level | Copies eliminated | Savings per call |
|-------|------------------|-----------------|
| Fp6_add/sub | 2 × 288 bytes | ~60 ns |
| Fp12_add/sub | 2 × 576 bytes | ~120 ns |
| Per Fp12_mul | 6 inner Fp6_add/sub | ~360 ns |
| Per Fp12_sqr | 2 inner Fp6_add | ~120 ns |

Conservative estimate: **30-40% of copy overhead** eliminated (componentwise ops
are frequent but cheaper per-call than mul). Gap reduces from 2.4x to ~1.8x.

### Phase 2: No-copy variants for mul/square

Create `Fp6_mul_nocopy` that skips copies when called with non-aliased arguments.
Callers (Fp12_mul) know their temporaries are distinct from inputs. This eliminates
the remaining 60-70% of copy overhead, closing the gap to ~1.2x.

## Schedule

| Day | Task |
|-----|------|
| 1 | Implement `CopyElim.v`: AST pattern matcher + rewriter |
| 2 | Wire into extraction, generate optimized C, benchmark |
| 3 | Phase 2: no-copy mul/square variants, end-to-end testing |

## Trust / Verification Status

- `CopyElim.v` is **trusted** (same status as ToCString.v — not verified against
  bedrock2 semantics, but the transformation is simple and auditable)
- The allowlist is manually curated with documented safety invariants
- End-to-end correctness validated by running the pairing on test vectors and
  comparing byte-for-byte with the unoptimized version
- An optional verification target: prove `elim_copies` preserves the WP
  postcondition for componentwise functions (research-grade, not required
  for practical use)

## Files

| File | Status | Lines |
|------|--------|-------|
| `src/Bedrock/Field/FieldExtensions/CopyElim.v` | NEW | ~100 |
| `src/Bedrock/Field/Synthesis/Examples/BLS12_Extract.v` | MODIFY | ~10 |
| `bench_bls12_vs_blst.c` | MODIFY | ~20 |
