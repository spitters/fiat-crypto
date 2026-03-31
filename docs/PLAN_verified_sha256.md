# Plan: Verified SHA-256 in bedrock2 (Path A)

## Goal

Replace the axiomatized SHA-256 (`Spec/SHA256_axiom.v`) with a fully verified bedrock2 implementation. This eliminates the last axiom in the hash-to-curve pipeline.

## Background

Andrew Appel's group verified OpenSSL's SHA-256 implementation in Coq using the Verified Software Toolchain (VST):
- **Paper**: Appel, "Verification of a Cryptographic Primitive: SHA-256", ACM TOPLAS 37(2), 2015
- **Code**: [github.com/PrincetonUniversity/VST/tree/master/sha](https://github.com/PrincetonUniversity/VST/tree/master/sha)
- **Key file**: `SHA256.v` — pure Gallina functional specification, no VST dependency

The VST Gallina spec is self-contained (no Floyd tactics, no CompCert dependency). It defines SHA-256 block processing, padding, and message scheduling as pure Coq functions matching FIPS 180-4.

## Architecture

```
Spec/SHA256.v                     ← Copy from VST (pure Gallina)
  │
  ├─ Constants: K256, init_registers
  ├─ Operations: Ch, Maj, Σ₀, Σ₁, σ₀, σ₁
  ├─ Message schedule: W(block, t)
  ├─ Round function: rnd_function
  ├─ Block processing: hash_block, hash_blocks
  ├─ Padding: generate_and_pad
  └─ Entry point: SHA_256(msg) → digest
  │
src/Bedrock/SHA256/
  ├─ Specs.v                      ← bedrock2 function specs
  │     spec_of_sha256_block : processes one 512-bit block
  │     spec_of_sha256 : full SHA-256 with padding
  │
  ├─ Implementation.v             ← bedrock2 function bodies
  │     sha256_block_body : 64-round loop + message schedule
  │     sha256_body : block iteration + padding
  │
  └─ Proof.v                      ← WP correctness proofs
        sha256_block_ok : Qed
        sha256_ok : Qed
          feval(output) = SHA_256(input)
```

## Step-by-step plan

### Step 1: Copy VST Gallina spec (1 day)

Copy `VST/sha/SHA256.v` to `src/Spec/SHA256.v`. Remove any VST-specific imports (there should be none — the spec is pure Gallina). Verify it compiles with `rocq c`.

Key definitions to copy:
- `K256 : list int` (64 round constants)
- `init_registers : list int` (H₀...H₇ initial state)
- `Ch`, `Maj`, `Sigma_0`, `Sigma_1`, `sigma_0`, `sigma_1` (bitwise operations)
- `W : list int → nat → int` (message schedule)
- `rnd_function : list int → nat → list int → list int` (one SHA-256 round)
- `Round : list int → nat → list int → nat → list int` (64 rounds)
- `hash_block : list int → list int → list int` (process one block)
- `hash_blocks : list int → list (list int) → list int` (process all blocks)
- `generate_and_pad : list Byte.byte → list int` (padding per RFC 6234)
- `SHA_256 : list Byte.byte → list Byte.byte` (top-level entry point)

### Step 2: Write bedrock2 implementation (2 weeks)

SHA-256's structure in C:
```c
void sha256_block(uint32_t state[8], const uint8_t block[64]) {
    uint32_t W[64], a, b, c, d, e, f, g, h, T1, T2;
    // Message schedule: W[0..15] from block, W[16..63] from expansion
    for (int t = 0; t < 16; t++) W[t] = load_be32(block + 4*t);
    for (int t = 16; t < 64; t++) W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16];
    // Initialize working variables from state
    a=state[0]; ... h=state[7];
    // 64 rounds
    for (int t = 0; t < 64; t++) {
        T1 = h + Σ₁(e) + Ch(e,f,g) + K[t] + W[t];
        T2 = Σ₀(a) + Maj(a,b,c);
        h=g; g=f; f=e; e=d+T1; d=c; c=b; b=a; a=T1+T2;
    }
    // Add to state
    state[0]+=a; ... state[7]+=h;
}
```

In bedrock2 syntax:
- 64-element `W` array via `stackalloc 256` (64 × 4 bytes)
- 8 working variables as bedrock2 locals
- K constants loaded via `expr.literal` or from a constant array
- Big-endian load via shift/mask operations (bedrock2 is little-endian)

Key decisions:
- Use 32-bit operations via `word.and (word.of_Z 0xFFFFFFFF)` masking (bedrock2 is 64-bit)
- Or: use Rupicola's 32-bit word support if available
- K constants: either 64 stores to stack array, or inline `expr.literal` per round (unrolled)

### Step 3: WP correctness proof (3-4 weeks)

The proof structure mirrors the pairing proofs:

1. **sha256_block_ok**: Loop invariant for the 64-round loop
   - Invariant: `state = Round(init_state, W, t)` at iteration `t`
   - Each round: 10 arithmetic operations + 2 bitwise operations
   - Use `wp_loop` tactic from WPTactics.v

2. **Message schedule proof**: Show `W[t]` computation matches `W(block, t)`
   - First 16: direct big-endian load from block
   - Next 48: recurrence `σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]`

3. **Padding proof**: Show `generate_and_pad` matches bedrock2 padding code
   - Length encoding, 0x80 byte, zero padding to 512-bit boundary

4. **Top-level**: Compose block processing over all blocks

Estimated proof size: ~800-1200 lines (comparable to Miller loop proof).

### Step 4: Connect to hash_to_field (1 week)

Replace axioms in `SHA256_axiom.v` with proved lemmas:
- `SHA256` → proved via `sha256_ok`
- `expand_message_xmd` → proved using `SHA256` + HMAC construction
- `hash_to_field` → proved using `expand_message_xmd` + field reduction

### Step 5: HMAC-SHA-256 (optional, 2 weeks)

`expand_message_xmd` uses HMAC internally. HMAC-SHA-256 is:
```
HMAC(K, msg) = SHA256((K ⊕ opad) ++ SHA256((K ⊕ ipad) ++ msg))
```

This is 2 SHA-256 calls with key XOR — relatively straightforward once SHA-256 is verified.

## Estimated effort

| Component | Effort | Lines |
|-----------|--------|-------|
| Spec (copy from VST) | 1 day | ~200 |
| bedrock2 implementation | 2 weeks | ~400 |
| WP correctness proof | 3-4 weeks | ~1200 |
| HMAC + expand_message | 2 weeks | ~500 |
| hash_to_field integration | 1 week | ~200 |
| **Total** | **6-8 weeks** | **~2500** |

## References

1. Appel, "Verification of a Cryptographic Primitive: SHA-256", TOPLAS 2015
   https://www.cs.princeton.edu/~appel/papers/verif-sha.pdf

2. Beringer et al., "Verified Correctness and Security of OpenSSL HMAC",
   USENIX Security 2015

3. FIPS 180-4: Secure Hash Standard
   https://csrc.nist.gov/publications/detail/fips/180/4/final

4. RFC 6234: US Secure Hash Algorithms
   https://datatracker.ietf.org/doc/html/rfc6234

5. RFC 9380: Hashing to Elliptic Curves (hash_to_field, expand_message_xmd)
   https://datatracker.ietf.org/doc/html/rfc9380

6. VST source code
   https://github.com/PrincetonUniversity/VST/tree/master/sha
