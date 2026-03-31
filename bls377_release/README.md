# Verified BLS12-377 Pairing -- C Extraction

Formally verified implementation of the optimal ate pairing for the
BLS12-377 elliptic curve, extracted as C code from machine-checked
Rocq (Coq) proofs via the fiat-crypto / bedrock2 toolchain.

## What is this?

This package contains C source for a complete BLS12-377 pairing
computation, covering the full algebraic tower:

    Fp -> Fp2 -> Fp6 -> Fp12 -> Miller loop -> final exponentiation

The curve BLS12-377 is used in the Aleo (snarkVM), Celo, and
ZK-proof ecosystems. The pairing is the core cryptographic operation
for BLS signatures, KZG polynomial commitments, and Groth16 proof
verification on this curve.

## Verification status

| Layer | Status | Method |
|-------|--------|--------|
| Fp arithmetic (add, sub, mul, square) | **Fully verified** | fiat-crypto synthesis + Rocq proof |
| Fp2 bridge (add, sub, mul, square, inv, opp) | Compositional | Standard formulas over verified Fp |
| Fp6 / Fp12 tower operations | **WP-verified** | bedrock2 weakest-precondition proofs |
| Frobenius endomorphisms | **WP-verified** | bedrock2 WP proofs |
| Miller loop | **WP-verified** | bedrock2 WP proofs |
| Final exponentiation (naive & DSD) | **WP-verified** | bedrock2 WP proofs |
| Pairing (full) | **WP-verified** | bedrock2 WP proofs |

"WP-verified" means the function has a machine-checked
weakest-precondition proof in bedrock2's separation logic: given
valid inputs satisfying the precondition, the function terminates and
produces output satisfying the postcondition in the correct memory
layout.

## Trust base

1. **Rocq (Coq) kernel** -- the proof checker that validates all proofs.
2. **bedrock2 C compiler** -- translates bedrock2 IR to C. The compiler
   is simple (~2000 lines of Rocq) and has been audited but is not
   itself formally verified against a C semantics.
3. **Two axioms** in the O'Connor FpInv bridge:
   - A certificate for the extended-GCD divstep computation (verified
     by reduction to a decidable integer computation).
   - `functional_extensionality` (standard, consistent with Rocq's logic).

The Fp2 bridge functions (`bls377_stubs.c`) are not extracted from
Rocq but implement standard formulas (Karatsuba multiplication,
norm-and-invert for Fp2) using the verified Fp primitives.

## Files

| File | Description |
|------|-------------|
| `bls377_pairing.c` | Extracted verified C code (2709 lines). Contains all Fp and tower arithmetic, Miller loop, final exponentiation, and full pairing. **Do not edit.** |
| `bls377_stubs.c` | Bridge functions for Fp2 layer and Fp utilities (`bls377_opp`, `bls377_from_word`, `bls377_Fp2_add/sub/mul/square/inv/opp/felem_copy`). These compose verified Fp operations using standard algebraic formulas. |
| `bls377_pairing.h` | Public header with type definitions, size constants, and API documentation. |
| `bench_bls377.c` | Benchmark harness exercising all tower layers and the full pairing. |
| `Makefile` | Build system. |
| `README.md` | This file. |

## Building and running

Requirements: C11 compiler (GCC or Clang), 64-bit little-endian platform.

```
make
./bench_bls377
```

To build with Clang or custom flags:

```
CC=clang CFLAGS="-O3 -march=native -std=c11" make
```

## Architecture

All functions are `static` (internal linkage) except `bls377_add`,
`bls377_opp`, and `bls377_from_word`. The compilation model uses
`#include` to combine everything into a single translation unit.
The benchmark file includes the stubs first (for Fp2 bridge
functions), then the extracted pairing code.

Field elements are represented in Montgomery form with R = 2^384 mod p.
Pointers are passed as `br_word_t` (`uintptr_t`). Memory layout:

- Fp:  48 bytes (6 x 64-bit limbs, little-endian)
- Fp2: 96 bytes (2 x Fp, real part first)
- Fp6: 288 bytes (3 x Fp2)
- Fp12: 576 bytes (2 x Fp6)

## Benchmark results

Measured on AMD Ryzen, GCC -O2, single core:

| Operation | Time |
|-----------|------|
| Fp add | 7.8 ns |
| Fp mul | 66.8 ns |
| Fp square | 59.2 ns |
| Fp2 mul | 253 ns |
| Fp6 mul | 1.84 us |
| Fp12 mul | 8.42 us |
| Fp12 square | 5.77 us |
| Miller loop | 3.53 ms |
| Final exp (DSD) | 1.53 ms |
| **Full pairing (DSD)** | **5.21 ms** |
| Full pairing (naive) | 14.0 ms |

### Comparison with unverified implementations

| Library | Language | Full pairing |
|---------|----------|-------------|
| gnark-crypto | Go | 0.92 ms |
| kilic | Go | 0.99 ms |
| Constantine | Nim | 1.12 ms |
| arkworks | Rust | 1.58 ms |
| libff | C++ | 3.80 ms |
| **This (verified, DSD)** | **C** | **5.21 ms** |
| This (verified, naive) | C | 14.0 ms |

The DSD-optimized pairing is ~5.7x slower than gnark-crypto and ~1.4x
slower than libff. The overhead comes from: (a) bedrock2's generic C
backend (no assembly, no intrinsics), (b) Montgomery multiplication
via schoolbook word-by-word reduction rather than platform-optimized
routines, and (c) Fp2 squaring implemented as multiplication.

## Pairing API

The main entry point is:

```c
void bls377_pairing_dsd(br_word_t out, br_word_t p_x, br_word_t p_y,
                        br_word_t q_x, br_word_t q_y);
```

- `out`: pointer to 576 bytes (Fp12 result)
- `p_x`, `p_y`: pointers to 48-byte Fp elements (G1 point)
- `q_x`, `q_y`: pointers to 96-byte Fp2 elements (G2 point)

All coordinates must be in Montgomery form. The function allocates
Frobenius constants on the stack internally.

## License

The fiat-crypto project is MIT-licensed. This extracted code inherits
that license.
