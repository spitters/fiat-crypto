# Plan: Prove the BLS12-381 Pairing Pipeline Correct

## Context

We have a complete BLS12-381 pairing implementation in bedrock2 (Fp -> Fp2 -> Fp6 -> Fp12 -> G1 -> G2 -> Miller loop -> final exponentiation -> pairing). All function bodies exist — zero `cmd.skip` placeholders. But ~30 WP correctness proofs remain as stubs (`exact I` or `Admitted`). The Fp layer is fully verified (fiat-crypto synthesis), and we've proved all 8 Fp2 ops + 6 Fp6 ops. The goal is to prove the remaining WP proofs bottom-up through the field extension tower to the pairing.

## Architecture

```
PROVED:  Fp (synthesis) → Fp2 (8/8) → Fp6 add/sub/copy/opp/mul_xi/mul (7/~12)
         G1 add (Rupicola) → G1 scalar mult

TODO:    Fp6 sqr/inv → Fp12 → Frobenius/helpers → Miller loop → final exp → pairing
         G2 add
```

## Current Status (2026-03-13)

### Completed Proofs

| Proof | File | Status | Date |
|-------|------|--------|------|
| All 8 Fp2 ops | QuadraticFieldExtensions.v | Qed | 2026-03-12 |
| Fp6_felem_copy_ok | CubicFieldExtensions.v | Qed | 2026-03-12 |
| Fp6_add_ok | CubicFieldExtensions.v | Qed | 2026-03-12 |
| Fp6_sub_ok | CubicFieldExtensions.v | Qed | 2026-03-12 |
| Fp6_opp_ok | CubicFieldExtensions.v | Qed | 2026-03-12 |
| Fp2_mul_xi_ok | CubicFieldExtensions.v | Qed | 2026-03-12 |
| Fp6_mul_ok | CubicFieldExtensions.v | Qed | 2026-03-13 |

### Not Yet Started

| Proof | File | Notes |
|-------|------|-------|
| Fp6_zero_ok | CubicFieldExtensions.v | Nullop pattern |
| Fp6_one_ok | CubicFieldExtensions.v | Nullop pattern |
| Fp6_select_znz_ok | CubicFieldExtensions.v | |
| Fp6_sqr_ok | CubicFieldExtensions.v | Chung-Hasan SQR3, ~15 Fp2 calls |
| Fp6_inv_ok | CubicFieldExtensions.v | Cubic inverse, ~20 Fp2 calls |
| All Fp12 ops | DodecicFieldExtensions.v | 9 proofs |
| All Frobenius ops | PairingFieldOps.v | 6 proofs |
| BLS12 helpers | BLS12_Pairing.v | 5 proofs |
| Loop proofs | BLS12_Pairing.v | 3 proofs (hardest) |
| Top-level | BLS12_G1.v etc. | 3 proofs |

## Proof Complexity Tiers

| Tier | Pattern | Ops | Est. effort each |
|------|---------|-----|-----------------|
| **A: Trivial** | 0 stackalloc, 2-3 sub-calls, componentwise | Fp12 add/sub/copy/opp/conjugate | ~30 min |
| **B: Simple** | 0-1 stackalloc, 2-6 sub-calls, direct | Fp6 opp, Fp2 conjugate, Fp2_mul_xi, Fp6_mul_by_v, Fp6_mul_fp2, Fp6/Fp12 frobenius_p2, constant loaders | ~1 hr |
| **C: Medium** | 1+ stackalloc, 6-8 sub-calls, Frobenius | Fp6 frobenius, Fp12 frobenius, Fp2_mul_fp, make_line | ~2 hr |
| **D: Hard** | 2-4 stackalloc, 7-27 sub-calls, Karatsuba | Fp6 mul/sqr, Fp12 mul/sqr | ~4 hr |
| **E: Very Hard** | Deep stackalloc, inv chain | Fp6 inv, Fp12 inv | ~6 hr |
| **F: Loop invariant** | while loops, 63-1280 iterations | Miller loop, final exp, pairing | ~1-2 days |
| **G: Top-level** | Instantiation wrappers | bls12_G1_ok, bls12_G1_alt_ok, bls12_G2_ok | ~2 hr |

## Phased Plan

### Phase 1: Complete Fp6 Remaining Ops (5 proofs)

**Files:** `CubicFieldExtensions.v`

| Proof | Pattern | Calls | Status |
|-------|---------|-------|--------|
| `Fp6_opp_ok` | unop, 1 stackalloc + 1 copy + 3 Fp2 opp | 4 | **DONE** |
| `Fp2_mul_xi_ok` | custom, 4 Fp calls (add, sub, copy) | 4 | **DONE** |
| `Fp6_mul_ok` | binop, 2 stackalloc + 2 copy + ~27 Fp2 calls | 29 | **~98%** — 3 admits in Copy preconditions |
| `Fp6_sqr_ok` | unop, 1 stackalloc + 1 copy + ~15 Fp2 calls | 17 | Chung-Hasan SQR3 |
| `Fp6_inv_ok` | unop, 1 stackalloc + 1 copy + ~20 Fp2 calls | 22 | Cubic inverse |

### Phase 2: Fp12 Simple Ops + mul_by_v (6 proofs)

**Files:** `DodecicFieldExtensions.v`

| Proof | Pattern | Calls | Notes |
|-------|---------|-------|-------|
| `Fp12_felem_copy_ok` | copy spec, 2 Fp6 copy calls | 2 | |
| `Fp12_add_ok` | binop, 0 stackalloc, 2 Fp6 add | 2 | No stackalloc! |
| `Fp12_sub_ok` | binop, 0 stackalloc, 2 Fp6 sub | 2 | |
| `Fp12_opp_ok` | unop, 0 stackalloc, 1 Fp6 copy + 1 Fp6 opp | 2 | |
| `Fp12_conjugate_ok` | custom, 0 stackalloc, 1 Fp6 copy + 1 Fp6 opp | 2 | |
| `Fp6_mul_by_v_ok` | custom, 1 stackalloc, 6 calls | 6 | |

### Phase 3: Fp12 Complex Ops (3 proofs)

**Files:** `DodecicFieldExtensions.v`

| Proof | Stackallocs | Calls |
|-------|-------------|-------|
| `Fp12_mul_ok` | 4 | 8 Fp6 ops |
| `Fp12_sqr_ok` | 3 | 7 Fp6 ops |
| `Fp12_inv_ok` | 2 | 10 Fp6 ops |

### Phase 4: Frobenius + Cross-Cutting Ops (6 proofs)

**Files:** `PairingFieldOps.v`

| Proof | Calls |
|-------|-------|
| `Fp2_conjugate_ok` | 2 |
| `Fp6_mul_fp2_ok` | 4 |
| `Fp6_frobenius_ok` | 8 |
| `Fp6_frobenius_p2_ok` | 3 |
| `Fp12_frobenius_ok` | 3 |
| `Fp12_frobenius_p2_ok` | 3 |

### Phase 5: BLS12-Specific Helpers (5 proofs)

### Phase 6: Loop Proofs (3 proofs) — HARDEST

### Phase 7: Top-Level Instantiation (3 proofs)

## Key Infrastructure & Bridge Lemmas

### mulp2/fp2_mul Bridge (CRITICAL)

The Fp2 AbstractField instance uses `QuadraticExtensions.mulp2` (generic β), while Fp6/Fp12 specs use `BLS12Fp6Spec.fp2_mul` (hardcoded u²=-1). Bridge lemma proved:

```coq
Lemma mulp2_eq_fp2_mul : forall a b,
  QuadraticExtensions.mulp2 M_pos a b = BLS12Fp6Spec.fp2_mul M_pos a b.
```

**Also needed**: `change` commands for `addp2`/`subp2` (definitionally equal but kernel can't verify in huge terms).

Pattern for feval postcondition in all mul-containing proofs:
```coq
rewrite !mulp2_eq_fp2_mul.
change (QuadraticExtensions.addp2 M_pos) with (BLS12Fp6Spec.fp2_add M_pos).
change (QuadraticExtensions.subp2 M_pos) with (BLS12Fp6Spec.fp2_sub M_pos).
reflexivity.
```

### Fp2_bounds_tight_of_loose

Fp6 `bin_mul` has `bin_outbounds := tight_bounds`, but Fp2 `bin_add` produces `loose_bounds`. Bridge lemma:
```coq
Lemma Fp2_bounds_tight_of_loose : forall x,
  Fp2_bounded_by loose_bounds x -> Fp2_bounded_by tight_bounds x.
```
Uses existing `bounds_equiv` from the Fp level.

### solve_putmany_eq / Stack Deallocation

- `solve_putmany_eq` works for single-map stack temps
- Fp6-sized allocations (3 Fp2 sub-maps) need manual `putmany_assoc`/`putmany_comm` chains
- sep section map equality needs MCP-verified rewrite chains (goal structure varies per proof)

## Spec Changes Made

### Fp6.v: fp6_mul uses double subtraction

Changed from `sub X (add B C)` to `sub (sub X B) C` for all three Karatsuba intermediates. This matches the bedrock2 body (which uses two successive sub calls) and the Fp12-level spec pattern.

## Lessons Learned

### L1: Always Test feval Section First (CRITICAL)

Before writing a long WP proof (N > 5 sub-calls):
1. Save MCP session at the feval postcondition goal
2. Try the full rewrite chain + reflexivity
3. If it fails, identify mismatches BEFORE writing mechanical sub-call steps
4. The mulp2/fp2_mul mismatch was discovered after ~800 lines of proof — wasted effort

### L2: Never Use `simpl` in Extension Proofs

`simpl` after `unfold AbstractField.Fmul` reduces through ALL field levels, breaking Fp2-level `rewrite Hfeval_*`. Always use targeted `change`:
```coq
(* BAD *)  unfold AbstractField.Fmul. simpl.
(* GOOD *) change (@AbstractField.Fmul _ Fp6_fp_inst) with (BLS12Fp6Spec.fp6_mul M_pos).
```

### L3: cbv [...] in * Can Destroy Hypotheses

Using `cbv [...] in *` modifies all hypotheses including those needed by later proof sections. Target specific hypotheses:
```coq
(* BAD *)  cbv [...] in *.
(* GOOD *) cbv [...] in Hbound_out0, Hbound_out1, Hbound_out2.
```

### L4: Gallina Spec Must Match Bedrock2 Structure

When bedrock2 uses `sub(sub(X,B),C)`, the Gallina spec must also use double subtraction, not `sub(X, add(B,C))`. These are propositionally but not definitionally equal — and the feval section expects exact structural match.

### L5: MCP Session Approach for sep Sections

sep section map equalities have goal structures that depend on the exact call sequence and stack allocation pattern. The only reliable approach:
1. Save MCP session at the goal
2. Use `reflexivity` to see `Unable to unify "LHS" with "RHS"`
3. Work out the rewrite chain from the concrete LHS→RHS
4. Test each step interactively

### L6: Context Size is a Real Constraint

After 25+ weaken_call steps, the Rocq proof state is enormous (50K+ characters). MCP output files are needed rather than direct display. Use `python3 -c` to extract specific parts (e.g., "Unable to unify" messages) from saved tool results.

## Estimated Remaining Effort

| Phase | Proofs | Status | Estimated |
|-------|--------|--------|-----------|
| 1: Fp6 remaining | 5 | 3 done, 1 at 98%, 2 todo | 1-2 days |
| 2: Fp12 simple | 6 | todo | 1-2 days |
| 3: Fp12 complex | 3 | todo | 2-3 days |
| 4: Frobenius | 6 | todo | 2-3 days |
| 5: BLS12 helpers | 5 | todo | 1-2 days |
| 6: Loop proofs | 3 | todo | 3-5 days |
| 7: Top-level | 3 | todo | 1-2 days |
| **Total remaining** | **~28** | | **11-19 days** |

## Methodology Reflections

### What Worked Well

1. **MCP interactive proving**: Saves enormous time vs. edit-compile cycles (5 min build per attempt). Essential for sep section rewrite chains where the goal structure is unpredictable.

2. **Bottom-up approach**: Proving Fp2 ops first gave a template (weaken_call, sep decomposition, instance bridging) that scaled to Fp6 with manageable new challenges.

3. **Memory files**: Tracking proof patterns, blockers, and infrastructure across sessions prevented re-discovering the same issues.

4. **Bridge lemma identification**: Once mulp2/fp2_mul was identified as THE blocker, fixing it unblocked the entire feval section cleanly.

### What Could Be Improved

1. **Test feval FIRST, always**: The biggest time sink was writing 800 lines of mechanical proof before discovering the feval section couldn't close. A 5-minute MCP test would have caught this. Future protocol: for any proof with N > 5 sub-calls, the FIRST thing to test is whether feval closes, BEFORE any weaken_call steps.

2. **Spec/body alignment check**: Before starting a WP proof, systematically verify that every operation in the bedrock2 body has a structurally matching operation in the Gallina spec. The `sub(sub X B) C` vs `sub X (add B C)` mismatch could have been caught by a 2-minute manual comparison.

3. **Automation for map rewrites**: The sep section map equalities are tedious and error-prone. A tactic that normalizes `map.putmany` expressions (flatten + sort by name + reassociate) would eliminate this class of goals entirely. Worth writing if we'll do 30+ more proofs.

4. **Batch MCP approach**: Instead of one-tactic-at-a-time MCP calls (each taking 5-10 seconds), compose 3-5 tactics per call with `; ` or `. ` separators to reduce round trips.

5. **Context window management**: Fp6_mul_ok consumed 3 full conversation contexts. Future complex proofs should:
   - Start with a focused plan for that specific proof
   - Use subagents for MCP exploration (isolates context)
   - Write proof incrementally to file, rebuilding after each section
   - Keep session summaries in memory files, not just in conversation

6. **Parallel proof development**: Fp6_sqr_ok and Fp6_inv_ok don't depend on Fp6_mul_ok being fully Qed. They can be developed in parallel using the same patterns. Use git worktrees or separate files to avoid conflicts.
