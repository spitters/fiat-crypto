# Plan: Replace blst with Verified G1/G2 and Pairing

## Current state

### What's verified and running
- **Fp arithmetic** (add/sub/select/copy): bedrock2→jasminc pipeline, Qed proofs
- **Fp/Fr mul/square**: CryptOpt + check_equivalence, formally verified
- **Fp2/Fp6/Fp12 tower**: pure Rust on verified Fp ops, tested against blst
- **BLS signatures**: working sign/verify (using blst for group ops + pairing)
- **Pairing**: working Miller loop + final exp (delegated to blst)

### What uses blst (28 symbols)
| Category | blst functions | Count |
|---|---|---|
| Miller loop | `blst_miller_loop` | 1 |
| Final exponentiation | `blst_final_exp` | 1 |
| Fp12 identity | `blst_fp12_is_one`, `blst_fp12_one` | 2 |
| G1 operations | `blst_p1_mult`, `blst_p1_to/from_affine`, `blst_p1_affine_generator` | 4 |
| G2 operations | `blst_p2_mult`, `blst_p2_to/from_affine`, `blst_p2_affine_generator` | 4 |
| Hash-to-curve | `blst_hash_to_g1` | 1 |
| Signature | `blst_keygen`, `blst_sk_to_pk_in_g2`, `blst_sign_pk_in_g2`, `blst_core_verify_pk_in_g2` | 4 |
| Scalar | `blst_scalar`, `blst_scalar_from_uint64`, `blst_scalar_from_fr` | 3 |
| **Total** | | **~20 unique** |

### What's already proven in bedrock2 (but not yet in the Rust pipeline)
| Component | File | Lines | Proof status |
|---|---|---|---|
| Miller loop | `BLS12_MillerLoop.v` | 1,682 | **Qed** (bls12_miller_loop_ok) |
| Final exponentiation | `BLS12_FinalExp.v` | 1,434 | **Qed** (bls12_final_exp_ok) |
| Line evaluation | `BLS12_PairingHelpers.v` | 81K | Helpers |
| Fp2 conjugate | `PairingFieldOps.v` | 320 | **Qed** |
| Fp6 mul_fp2 | `PairingFieldOps.v` | 330 | **Qed** |
| Fp6/Fp12 Frobenius | `PairingFieldOps.v` | ~900 | **9 Qed proofs** |
| G1 point addition | `CurveAdd.v` | 269 | **4 Qed** (ladderstep_ok) |
| G1 scalar mult | `LadderStep.v` | 150 | **2 Qed** |
| G2 point addition | `BLS12_G2.v` | 261 | Stub (exact I), real code |
| BLS12 pairing top | `BLS12_Pairing.v` | 1,905 | 9 lemmas |
| Pairing top | `BLS12_PairingTop.v` | 28K | Full proof |

**Key insight**: the hard verification work is ALREADY DONE. The Miller
loop, final exponentiation, Frobenius, and G1 group operations all have
Qed proofs in bedrock2. The gap is getting these proofs into running
assembly via the jasminc pipeline.

## Strategy

Two parallel paths, ordered by practicality:

### Path A: Pure Rust matching verified specs (~3-4 weeks)

Write pure-Rust implementations of G1/G2 group operations, Miller loop,
and final exponentiation on top of our verified Fp/Fp2/Fp6/Fp12 tower.
Test rigorously against blst. Not formally verified at the Rust level,
but the algorithms match the bedrock2 Qed-proven specs.

**Advantage**: Working code quickly, no Rocq compilation bottlenecks.
**Disadvantage**: The Rust code itself is untrusted (only the underlying
field arithmetic is verified).

### Path B: Extract bedrock2 proofs through jasminc pipeline (~2-3 months)

Run the existing bedrock2 functions through `to_jasmin_cmd` → jasminc →
assembly, using the same pipeline as Fp add/sub. This gives fully
verified assembly for G1/G2/pairing.

**Advantage**: End-to-end verification.
**Disadvantage**: Requires extending the pipeline to handle larger
functions (Miller loop = while loop over 63 bits, final exp = loop
over 1268 bits). The `to_jasmin_cmd` translation needs to handle
bedrock2 `while` loops and stack-allocated temporaries.

**Recommendation**: Do Path A first (immediate practical value), then
Path B for the research contribution.

## Path A: Pure Rust implementation

### Phase 1: G1 group operations (~1 week)

#### 1.1 Point representation (Day 1)
```rust
// Projective coordinates: (X : Y : Z) where x = X/Z, y = Y/Z
pub struct G1Projective { pub x: Fp, pub y: Fp, pub z: Fp }

// Affine: (x, y) or infinity
pub struct G1Affine { pub x: Fp, pub y: Fp }  // already exists in pairing.rs
```

#### 1.2 Point addition (Day 1-2)
- **Reference**: `CurveAdd.v` line 28 (`ladderstep_gallina`)
- **Algorithm**: Complete addition formula for short Weierstrass y² = x³ + 4
- Handles: P + Q, P + P (doubling), P + O, O + P
- Test against blst: generate random points, compare results

#### 1.3 Point doubling (Day 2)
- **Reference**: `PointDouble.v` in Group/CurveAdd
- Dedicated doubling formula (more efficient than generic addition)

#### 1.4 Scalar multiplication (Day 3-4)
- **Reference**: `LadderStep.v`, `ScalarMult.v`
- Double-and-add with constant-time windowed NAF
- For non-constant-time version: simple binary method
- Test: sk * G1 vs blst's `blst_p1_mult`

#### 1.5 Generator and on-curve check (Day 4)
- Hardcode the BLS12-381 G1 generator
- `is_on_curve(P)`: check y² = x³ + 4

#### 1.6 Affine ↔ projective conversion (Day 4-5)
- `to_affine`: compute X/Z, Y/Z (requires Fp inversion)
- `from_affine`: set Z = 1
- **Fp inversion**: Fermat's little theorem (p-2 exponentiation) or
  extended Euclidean. The former is simpler, the latter faster.
  Start with Fermat.

### Phase 2: G2 group operations (~3-4 days)

Same as Phase 1 but with Fp2 instead of Fp.

#### 2.1 Point types
```rust
pub struct G2Projective { pub x: Fp2, pub y: Fp2, pub z: Fp2 }
// G2Affine already exists in pairing.rs
```

#### 2.2 Point addition, doubling, scalar multiplication
- **Reference**: `BLS12_G2.v` (lines 139-249 have the full bedrock2 body)
- Same formulas as G1 but all field ops are Fp2 ops
- Curve: y² = x³ + 4(u+1) where u+1 is the twist parameter

#### 2.3 Generator and on-curve check
- Hardcode the BLS12-381 G2 generator (from the standard)
- `is_on_curve(P)`: check y² = x³ + 4(u+1)

### Phase 3: Frobenius and pairing helpers (~3-4 days)

#### 3.1 Frobenius endomorphisms on Fp2/Fp6/Fp12
- **Reference**: `PairingFieldOps.v` (9 Qed proofs)
- `fp2_conjugate`: (a, b) → (a, -b)
- `fp6_frobenius`: multiply each Fp2 component by the Frobenius constant
- `fp12_frobenius`, `fp12_frobenius_p2`, `fp12_frobenius_p3`
- Requires: Frobenius constants (gamma values from the BLS12-381 standard)
- These are already defined in `BLS12_Pairing.v` line 119

#### 3.2 Fp12 inversion
- Needed for the final exponentiation easy part
- Via the tower: compute inverse using Fp6 operations
- **Reference**: `DodecicFieldExtensionsInv.v` (Qed)

#### 3.3 Fp12 conjugation
- `fp12_conjugate(a, b) = (a, -b)` in Fp6 components
- Trivial, using fp6_sub

#### 3.4 Line evaluation (make_line)
- **Reference**: `BLS12_PairingHelpers.v`
- Evaluate the tangent/chord line at the G1 point P
- Output is a "sparse" Fp12 element (most components zero)
- Sparse multiplication: `fp12_mul_by_line` — much cheaper than full Fp12 mul

### Phase 4: Miller loop (~3-4 days)

#### 4.1 Doubling step
- **Reference**: `BLS12_MillerLoop.v` line functions
- Input: G2 projective point T, G1 affine point P
- Output: updated T (2*T), line evaluation ℓ(P)
- Uses: Fp2 arithmetic + line evaluation formula

#### 4.2 Addition step
- Input: G2 projective T, G2 affine Q, G1 affine P
- Output: updated T (T+Q), line evaluation ℓ(P)

#### 4.3 Loop over BLS parameter bits
```rust
pub fn miller_loop(p: &G1Affine, q: &G2Affine) -> Fp12 {
    let mut f = Fp12::one();
    let mut t = G2Projective::from_affine(q);
    for i in (0..63).rev() {
        f = fp12_square(&f);
        let (new_t, line) = doubling_step(&t, p);
        t = new_t;
        f = fp12_mul_by_line(&f, &line);
        if (BLS_X >> i) & 1 == 1 {
            let (new_t, line) = addition_step(&t, q, p);
            t = new_t;
            f = fp12_mul_by_line(&f, &line);
        }
    }
    if BLS_X_IS_NEG { f = fp12_conjugate(&f); }
    f
}
```
- **Reference**: `BLS12_MillerLoop.v` (Qed, 1682 lines)
- The structure matches exactly — the bedrock2 code is this algorithm

#### 4.4 Testing
- Compare `our_miller_loop(P, Q)` vs `blst_miller_loop(Q, P)` for
  random points. Note blst has Q, P argument order.

### Phase 5: Final exponentiation (~4-5 days)

#### 5.1 Easy part
```rust
// f^((p^6 - 1)(p^2 + 1))
fn final_exp_easy(f: &Fp12) -> Fp12 {
    let f_conj = fp12_conjugate(f);          // f^(p^6)
    let f_inv = fp12_inverse(f);             // f^(-1)
    let t0 = fp12_mul(&f_conj, &f_inv);     // f^(p^6 - 1)
    let t1 = fp12_frobenius_p2(&t0);        // t0^(p^2)
    fp12_mul(&t1, &t0)                       // t0^(p^2 + 1)
}
```
- **Reference**: `BLS12_FinalExp.v` lines 305+

#### 5.2 Hard part
- Exponentiate by (p^4 - p^2 + 1) / r
- Uses cyclotomic squaring (cheaper than generic Fp12 squaring)
- Addition chain for the h3 exponent (1268 bits)
- **Reference**: `BLS12_FinalExp.v` (Qed) + `BLS12_FinalExpH3.v`
- This is the most complex single function (~200 lines of Rust)

#### 5.3 Testing
- Compare `final_exp(our_ml)` vs `blst_final_exp(our_ml)`
- Verify `pairing(G1, G2)` is the same as blst's
- Verify bilinearity: `e(aP, Q) = e(P, aQ) = e(P, Q)^a`

### Phase 6: Hash-to-curve and signature integration (~3-4 days)

#### 6.1 Hash-to-G1 (SWU map)
- **Reference**: `Spec/HashToCurveIsogenyProof.v` (Qed)
- Implements: hash_to_field → SWU map → isogeny → clear cofactor
- Or use the simplified SWU + cofactor clear from RFC 9380
- ~100 lines of Rust

#### 6.2 Remove blst from signature.rs
- Replace `blst_keygen` with Fr scalar generation (our verified Fr ops)
- Replace `blst_sk_to_pk_in_g2` with our G2 scalar mult
- Replace `blst_sign_pk_in_g2` with our G1 scalar mult after hash-to-curve
- Replace `blst_core_verify_pk_in_g2` with our pairing check
- Replace `blst_hash_to_g1` with our hash-to-curve

#### 6.3 Remove blst from pairing.rs
- Replace `blst_miller_loop` with our miller_loop
- Replace `blst_final_exp` with our final_exp
- `blst_fp12_is_one` → trivial comparison
- `blst_fp12_one` → constant

#### 6.4 Remove blst from Cargo.toml
- Move blst back to dev-dependencies (or remove entirely)
- Keep it only for the comparison benchmark

### Phase 7: Testing and validation (~2-3 days)

- Differential fuzzing: random inputs, compare our output vs blst
- Edge cases: point at infinity, zero scalar, p * G = O
- Bilinearity: e(aP, bQ) = e(P, Q)^(ab)
- Signature roundtrip without blst
- Performance comparison: our pure-Rust vs blst

## Path B: Extract through jasminc pipeline (future)

### What's needed beyond Path A

1. **Extend `to_jasmin_cmd` for while loops**: The Miller loop uses a
   bedrock2 `while` loop. Currently `to_jasmin_cmd` translates while
   to Jasmin's `Cwhile`, which works, but the `real_jsem_while_true`
   proof needs the recursive structure.

2. **Stack allocation in Jasmin**: The Miller loop and final exp use
   stack-allocated arrays (for G2 coordinates, Fp12 accumulators).
   `to_jasmin_cmd` maps `JCdecl` to Jasmin's stack declarations,
   which jasminc handles. The proofs are structural (already Qed via
   `real_jsem_decl`).

3. **Run CryptOpt + check_equivalence on extracted assembly**: For the
   straight-line parts (line evaluation, Fp12 mul), this gives
   optimal code. For the loopy parts (Miller loop, final exp), jasminc's
   own optimizations apply.

4. **The G1/G2 proofs need strengthening**: `BLS12_G1.v` and
   `BLS12_G2.v` have stub proofs (`exact I`). The function bodies are
   real bedrock2 code, but the WP proofs need to be completed.
   `CurveAdd.v` has the generic proof (Qed), so this is a matter of
   instantiating it with BLS12-381 parameters.

### Effort estimate for Path B

| Step | Effort | Depends on |
|---|---|---|
| G1/G2 WP proof completion | ~1 week | CurveAdd.v (done) |
| Miller loop WP proof | Already Qed | — |
| Final exp WP proof | Already Qed | — |
| to_jasmin_cmd for loops | ~3 days | PolishPassProofs infrastructure |
| Polish pass proofs (general case) | ~2-3 weeks | jeval redesign |
| CryptOpt + check_equivalence | ~2 days per function | — |
| Integration into Rust pipeline | ~1 week | Path A (for the types) |
| **Total** | **~6-8 weeks** | |

## Timeline

### Weeks 1-3 (Path A)
- **Week 1**: G1 group ops (add, double, scalar mul, affine/projective)
- **Week 2**: G2 group ops + Frobenius + Fp12 inverse + line evaluation
- **Week 3**: Miller loop + final exponentiation + testing

### Week 4 (Integration)
- Remove blst from pairing.rs and signature.rs
- Hash-to-curve implementation
- Full test suite: signatures, pairing bilinearity, edge cases
- Performance comparison

### After Week 4 (Path B, optional)
- Strengthen G1/G2 WP proofs (BLS12_G1/G2.v)
- Extract through jasminc
- CryptOpt + check_equivalence for assembly validation

## Dependencies

| Prerequisite | Status | Required for |
|---|---|---|
| Fp add/sub/mul/square | ✅ Verified | Everything |
| Fp2/Fp6/Fp12 arithmetic | ✅ Pure Rust | Miller loop, Frobenius |
| Fp inversion | ❌ Not yet | Affine conversion, final exp |
| Fp2 inversion | ❌ Not yet | G2 affine conversion |
| Fp12 inversion | ❌ Not yet | Final exp easy part |
| Frobenius constants | ❌ Not yet | Final exp, Frobenius |
| BLS12-381 generators | ❌ Not yet | Key generation, tests |
| Cyclotomic squaring | ❌ Not yet | Final exp hard part |
| Hash-to-curve (SWU) | ❌ Not yet | Signatures without blst |

## Risk assessment

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| Fp12 tower Rust ops have bugs | Medium | High | Differential testing against blst |
| Final exp hard part has wrong constants | Medium | High | Compare against blst's known-good output |
| Performance is much worse than blst | High | Medium | Accept 2-5× slowdown for verification; optimize later |
| Fp inversion is slow (Fermat) | Low | Low | Use addition chain; ~350 Fp muls is fine |
| Hash-to-curve constant-time issues | Medium | Medium | Use branchless arithmetic throughout |

## Success criteria

1. **All 23 existing tests pass without blst** (except the blst benchmark)
2. **Bilinearity holds**: `e(aP, bQ) = e(P, Q)^(ab)` for random scalars
3. **Signatures work**: sign/verify without blst, agreeing with blst on test vectors
4. **Performance**: within 5× of blst for the full pairing (acceptable for verification-focused use)
