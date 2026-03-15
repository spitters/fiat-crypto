# Parallel Plan: Complete the BLS12-381 Pairing Proof

## Dependency Graph

```
                    Fp (synthesis, DONE)
                         |
                    Fp2 (8/8, DONE)
                    /           \
               Fp6 (ALL DONE)   Fp2_conjugate [A1]
               /        \           |
          Fp12 (DONE)  Fp6_mul_fp2 [A2]    Fp6_frobenius [A3]
          /      \         |                     |
   Fp12_mul    Fp12_sqr  Fp6_frobenius_p2 [A4]  Fp12_frobenius [B1]
   (DONE)      (DONE)    (3 admits left)         |
                    \                     Fp12_frobenius_p2 [B2]
                     \                          |
                      \--- Fp12_inv (DONE) ----/
                                |
                    BLS12_Pairing.v helpers [C1-C5]
                                |
                         Miller loop [D1]
                                |
                      Final exponentiation [D2]
                                |
                           Pairing [D3]
```

## Parallel Task Groups

### Group A: Phase 4 Fp2/Fp6-level (independent of each other)

| Task | File | Calls | Pattern | Est. lines |
|------|------|-------|---------|-----------|
| A1: Fp2_conjugate_ok | PairingFieldOps.v | 2 Fp | Fp2→Fp decomp (like Fp2_felem_copy) | ~150 |
| A2: Fp6_mul_fp2_ok | PairingFieldOps.v | 1 stackalloc + copy + 3 mul | Like Fp6_frobenius_p2 + stackalloc | ~120 |
| A3: Fp6_frobenius_ok | PairingFieldOps.v | 1 stackalloc + 3 conj + copy + 2 mul | A1 as callee | ~150 |
| A4: Fp6_frobenius_p2_ok (finish) | PairingFieldOps.v | 3 final admits | feval/bounded/sep | ~30 |

**Dependencies**: A3 depends on A1 (uses conjugate). A4 is independent. A1, A2 are independent.

### Group B: Phase 4 Fp12-level (depend on Group A)

| Task | File | Calls | Pattern | Est. lines |
|------|------|-------|---------|-----------|
| B1: Fp12_frobenius_ok | PairingFieldOps.v | 2 Fp6_frob + 1 mul_fp2 | Fp12→Fp6 decomp | ~100 |
| B2: Fp12_frobenius_p2_ok | PairingFieldOps.v | 2 Fp6_frob_p2 + 1 mul_fp2 | Same as B1 | ~100 |

**Dependencies**: B1 needs A3 + A2. B2 needs A4 + A2.

### Group C: Phase 5 BLS12 helpers (independent of Group A/B for specs)

| Task | File | What | Est. lines |
|------|------|------|-----------|
| C1: bls12_Fp2_mul_fp spec+proof | BLS12_Pairing.v | 2 Fp mul (like conjugate) | ~100 |
| C2: bls12_make_line spec+proof | BLS12_Pairing.v | ~10 Fp2 calls, line evaluation | ~200 |
| C3-C5: gamma loaders spec+proof | BLS12_Pairing.v | from_list calls | ~50 each |

**Dependencies**: C1 is independent. C2 needs C1. C3-C5 are independent.

### Group D: Phase 6-7 (depend on everything above)

| Task | File | What | Est. effort |
|------|------|------|------------|
| D1: Miller loop spec+invariant+proof | BLS12_Pairing.v | cmd.while, 63 iterations | HARD (~500 lines) |
| D2: Final exp spec+proof | BLS12_Pairing.v | Easy part + hard part loop | ~300 lines |
| D3: Pairing composition | BLS12_Pairing.v | miller + final_exp | ~50 lines |

## Parallel Execution Plan

### Wave 1 (fully parallel, no dependencies)
- **Agent 1**: A1 (Fp2_conjugate) — Fp2→Fp decomposition, follows Fp2_felem_copy pattern
- **Agent 2**: A2 (Fp6_mul_fp2) — stackalloc + copy + 3 mul, follows Fp6_frobenius_p2 pattern
- **Agent 3**: A4 (finish Fp6_frobenius_p2) — 3 final admits: feval/bounded/sep
- **Agent 4**: C1 (bls12_Fp2_mul_fp) — define spec, prove (2 Fp mul)
- **Agent 5**: C3-C5 (gamma loaders) — define specs, prove (from_list calls)

### Wave 2 (depends on Wave 1)
- **Agent 1**: A3 (Fp6_frobenius) — needs A1 result
- **Agent 2**: B2 (Fp12_frobenius_p2) — needs A4 + A2 results
- **Agent 3**: C2 (bls12_make_line) — needs C1 result

### Wave 3 (depends on Wave 2)
- **Agent 1**: B1 (Fp12_frobenius) — needs A3 + A2 results
- **Agent 2**: D1 (Miller loop) — needs all of above, HARDEST PROOF

### Wave 4 (depends on Wave 3)
- **Agent 1**: D2 (Final exponentiation) — needs D1 + B1 + B2
- **Agent 2**: D3 (Pairing) — needs D1 + D2 (trivial once both done)

## Key Patterns for Agents

Each proof follows the established pattern:
1. Use Option D (explicit callee list) for the lemma statement
2. `intros functions EnvContains HF1 HF2 ...`
3. `unfold spec_of_foo. intros ... [bounds.. Hmem_all].`
4. `eapply start_func; [exact EnvContains | clear EnvContains].`
5. Decompose FElems (Fp6→Fp2 or Fp12→Fp6)
6. `split_all_disjointness. rewrite <- ?map.putmany_assoc.`
7. Build master sep via manual `exists`/`split`/`map_disjoint_auto`
8. For each call: `solve_dexprs` + `eapply Semantics.weaken_call` + `ecancel_assumption`
9. Bounds: `cbv [bin_xbounds ...]; apply relax_bounds; exact Hbx`
10. Final: feval (firstn/skipn) + bounded_by + Fp6/Fp12 join

## Files to Create (for parallel compilation)

Each Wave 1 agent works in a separate file to avoid conflicts:
- `PairingFieldOpsConjugate.v` — A1
- `PairingFieldOpsMulFp2.v` — A2
- `PairingFieldOpsFrobP2Final.v` — A4
- `BLS12_PairingHelpers.v` — C1, C3-C5
