# Curve Porting Plan: BLS24-509 and Automation

## Target Curves

### BLS24-509 (192-bit security)
- **Tower**: Fp -> Fp2 -> Fp4 -> Fp8 -> Fp24
  - Fp2 = Fp[u]/(u^2+1)          — quadratic
  - Fp4 = Fp2[v]/(v^2-(u+1))     — quadratic
  - Fp8 = Fp4[w]/(w^2-v)         — quadratic
  - Fp24 = Fp8[z]/(z^3-w)        — cubic
- **Twist**: D-type quartic over Fp4 (G2 in E'(Fp4))
- **Seed**: z = -0x800000ffff801 (~51 bits)
- **Prime**: 509 bits (8 limbs)
- **Final exp**: easy (p^12-1)(p^4+1), hard (p^8-p^4+1)/r via Phi_24
- **References**:
  - Costello-Lange-Naehrig 2011 (ePrint 2011/465)
  - Ghammam-Fouotsa 2016 (ePrint 2016/130)
  - efficient-rust-pairings (github.com/kamel78/efficient-rust-pairings)

### BLS12-638 (disputed ~140-160 bit security)
- Same tower as BLS12-381, larger field (638 bits, 10 limbs)
- ~107-bit seed, same final exp structure
- Mechanical port (~4000 lines) but security insufficient for 192-bit target

## Automation Plan

### Phase 1: Generic Quadratic Extension Module ✅ DONE
**Goal**: Single parameterized module for all quadratic extensions (Fp2, Fp4, Fp8, Fp12-over-Fp6).

**Files created**:
- `Theory/QuadraticExtensionsAbstract.v` — Gallina operations on (F × F) for any field F
- `GenericQuadraticSpecs.v` — FieldParameters + FieldRepresentation instances
- `GenericQuadratic.v` — bedrock2 function bodies (copy, zero, one, opp, add, sub, mul, sqr, select_znz)

**Parameterized over**:
- `BaseField : Type` with `FieldParameters` + `FieldRepresentation`
- `nonresidue : BaseField` (quadratic non-residue)
- `mul_by_nr` bedrock2 function (multiplication by nonresidue)
- `prefix : string` for function names

**Can be instantiated for**:
- Fp → Fp2 (existing use case)
- Fp2 → Fp4 (new, BLS24)
- Fp4 → Fp8 (new, BLS24)
- Fp6 → Fp12 (existing, replaces DodecicFieldExtensions.v)

**Estimated savings**: ~800 lines per new quadratic layer (vs ~1200 lines copy-paste)

**Status**: All files compile. WP correctness proofs deferred (need MCP-interactive work).

### Phase 2: Generic Cubic Extension Module ✅ DONE
**Goal**: Single parameterized module for cubic extensions (Fp6, Fp24).

**Files created**:
- `Theory/CubicExtensionsAbstract.v` — Gallina operations on (F × F × F) for any field F
- `GenericCubicSpecs.v` — FieldParameters + FieldRepresentation instances
- `GenericCubic.v` — bedrock2 function bodies (copy, zero, one, opp, add, sub, mul, sqr, inv)

**Parameterized over**:
- `BaseField : Type` with `FieldParameters` + `FieldRepresentation`
- `mul_by_nr : BaseField → BaseField` (multiplication by cubic nonresidue)
- `mul_by_nr` bedrock2 function
- `prefix : string` for function names

**Can be instantiated for**:
- Fp2 → Fp6 (existing use case)
- Fp8 → Fp24 (new, BLS24)

**Estimated savings**: ~500 lines per new cubic layer

### Phase 3: Automated Feval Chain Generation (future)
The 8 feval files per curve (Fp2/Fp6/Fp12/Pairing x2) follow a mechanical pattern.
A tactic or Ltac2 metaprogram could emit feval lemmas from a tower description.

### Phase 4: Per-Curve Instantiation for BLS24-509
With generic modules, the new code needed is:
- Prime/field boilerplate (~40 lines)
- Fp4 instantiation (~150 lines)
- Fp8 instantiation (~150 lines)
- Fp24 instantiation (~200 lines)
- Fp24 pairing operations: Frobenius, cyclotomic sqr, etc. (~800 lines)
- Miller loop with quartic twist line evaluation (~1500 lines)
- Final exponentiation with Phi_24 hard part (~1000 lines)
- Feval chain (~500 lines)
- Total: ~4500 lines (down from ~10000 without generic modules)

## Build Configuration

```bash
eval $(opam env --switch=rocq-native)
export ROCQPATH=~/.opam/rocq-native/lib/coq/user-contrib
make -j4 EXTERNAL_DEPENDENCIES=1 <target>.vo
```

Rocq 9.0.0, rewriter v0.0.15, native compiler enabled.
