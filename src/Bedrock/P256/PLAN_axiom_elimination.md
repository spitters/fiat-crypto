# Plan: Eliminate Remaining P-256 Axioms

## Current Axioms

### Group A: Synthesis valid_func (Synthesis.v)
1. `p256_mul_valid` — `valid_func (res mul_op (fun _ => unit))`
2. `p256_sqr_valid` — `valid_func (res square_op (fun _ => unit))`

### Group B: FElem↔coord bridge (Bridge.v)
3. `coord_bounded` — `bounded_by loose_bounds (bs2felem (coord.to_bytes x))`
4. `coord_feval` — `feval (bs2felem (coord.to_bytes x)) = x`
5. `FElem_to_coord` — `FElem pout out → (coord.to_bytes r)$@pout`

### Group C: Sqr naming (P256.v)
6. `p256_coord_sqr_ok` — synthesis name `"p256_coord_square"` ≠ spec name `"p256_coord_sqr"`

### Group D: Pre-existing bedrock2 (not ours)
7. `br_memset_ok`, `br_memcxor_ok`

---

## Plan

### Step 1: valid_func (axioms 1-2) — boolean reflection

**Problem:** `repeat constructor` produces O(expression_tree_size) proof terms → OOM.

**Fix:** Write a boolean decision procedure `valid_func_b` and soundness lemma.

```
Fixpoint valid_cmd_b {b} (e : @API.expr (fun _ => unit) (type.base b)) : bool := ...
Fixpoint valid_func_b {t} (e : @API.expr (fun _ => unit) t) : bool := ...
Lemma valid_func_reflect : valid_func_b e = true -> valid_func e.
```

Then: `apply valid_func_reflect; native_compute; reflexivity.`

Proof term is constant-size: `valid_func_reflect _ eq_refl`.

**Files:** Add `ValidFuncDecide.v` in `src/Bedrock/Field/Translation/Proofs/`.
**Effort:** ~50 lines (inductive recursion matching valid_cmd constructors).
**Risk:** Low — purely structural boolean check.

### Step 2: coord_feval (axiom 4) — Montgomery identity

**Problem:** Show `feval (bs2felem (coord.to_bytes x)) = x`.

**Proof sketch:**
- `coord.to_bytes x = le_split 32 (F.to_Z (x * R))` where `R = 2^256`
- `bs2felem` converts to words: `proj1_sig (bs2felem bs) = bs2ws 8 bs`
- `feval ws = F.of_Z _ (eval_trans (map word.unsigned ws))`
  where `eval_trans = from_montgomerymod`
- `from_montgomerymod(x * R mod p) = (x * R) * R^(-1) mod p = x`
- Key lemma: `le_combine (le_split n z) = z mod 2^(8*n)` (LittleEndianList)
- Need: `F.to_Z (x * R) < 2^256` (since `p < 2^256`)

**Steps:**
1. Show `map word.unsigned (bs2ws 8 (le_split 32 z)) = Partition.partition (uweight 64) 4 z`
   This connects byte→word conversion with the positional encoding.
2. Show `Positional.eval (uweight 64) 4 (Partition.partition (uweight 64) 4 z) = z mod 2^256`
   This is `Partition.eval_partition`.
3. Show `from_montgomerymod (F.to_Z (x * R)) = F.to_Z x`
   This is the Montgomery identity: `from_mont(x*R) = x`.
4. Combine: `feval (...) = F.of_Z _ (F.to_Z x) = x`

**Files:** Bridge.v
**Effort:** ~30 lines. Uses `Partition.eval_partition`, `LittleEndianList.le_combine_split`, Montgomery inverse properties from WordByWordMontgomery.v.
**Risk:** Medium — need to navigate Partition/Positional eval chain.

### Step 3: coord_bounded (axiom 3) — canonical encoding in bounds

**Problem:** Show `bounded_by loose_bounds (bs2felem (coord.to_bytes x))`.

**Proof sketch:**
- `loose_bounds = wordlist` for WBW Montgomery
- `bounded_by wordlist ws = WordByWordMontgomery.valid 64 4 m (map word.unsigned ws)`
- `valid 64 4 m zs` requires each `zi ∈ [0, 2^64)` and `length zs = 4`
- `bs2felem (coord.to_bytes x)` has words from `bs2ws 8 (le_split 32 z)`
- Each word = `le_combine (le_split 8 (z >> (64*i)))` which is in `[0, 2^64)` by construction

**Steps:**
1. Show `length (proj1_sig (bs2felem ...)) = 4` (from `bs2felem` definition + `length_coord`)
2. Show each word unsigned value is in `[0, 2^64)` (from `le_combine_split` mod property)
3. Show `Positional.eval ... < m` (from `F.to_Z (x*R) < p < 2^256`)

**Files:** Bridge.v
**Effort:** ~20 lines. Mostly `vm_compute` for concrete P-256 bounds.
**Risk:** Low — concrete bounds verification.

### Step 4: FElem_to_coord (axiom 5) — reverse direction

**Problem:** Show `FElem pout out → (coord.to_bytes r)$@pout` when `feval out = r`.

**Proof sketch:**
- From `felem_to_bytes`: `FElem p x ↔ (ws2bs 8 x)$@p`
- Need: `ws2bs 8 (proj1_sig out) = coord.to_bytes r = le_split 32 (F.to_Z (r * R))`
- Since `feval out = r`, and `feval` applies `from_montgomerymod`:
  `from_mont(eval(out)) = r` ⟹ `eval(out) = r * R mod p = F.to_Z (r * R)`
- And `ws2bs 8 out = le_split 32 (eval(out))` by the word↔byte roundtrip
- So `ws2bs 8 out = le_split 32 (F.to_Z (r * R)) = coord.to_bytes r` ✓

**Steps:**
1. Same word↔byte chain as Step 2, in reverse
2. Use `felem_to_bytes` for the sep-logic conversion
3. Rewrite with the equality `ws2bs 8 out = coord.to_bytes r`

**Files:** Bridge.v
**Effort:** ~25 lines. Symmetric to Step 2.
**Risk:** Low — same infrastructure, reverse direction.

### Step 5: p256_coord_sqr_ok (axiom 6) — naming fix

**Problem:** Synthesis uses `"p256_coord_square"`, spec uses `"p256_coord_sqr"`.

**Options (pick one):**
- **A.** Rename spec to `"p256_coord_square"` in Specs.v (cascading changes to Coord.v etc.)
- **B.** Add `spec_of_p256_coord_sqr_from_square` wrapper that adapts the name
- **C.** Use `call_body` directly: enter function body via `map.get ... "p256_coord_sqr" = Some ...`, then the body is identical to `square_op` regardless of name

**Recommended: Option C** — minimal changes, no spec rename needed.

```coq
Lemma p256_coord_sqr_ok : forall functions,
  map.get functions "p256_coord_sqr" = Some p256_coord_sqr ->
  spec_of_p256_coord_sqr functions.
Proof.
  (* Same Proper_call bridge as mul, but use call_body
     to enter the function body directly via Hget *)
  intros functions Hget.
  cbv [spec_of_p256_coord_sqr].
  intros ...
  (* Use WeakestPrecondition.call_body with Hget *)
  eapply Proper_call.
  2: { cbv [Semantics.call WeakestPrecondition.call].
       eexists; split; [exact Hget|].
       (* Body WP is identical to what square_func_correct proves *)
       (* Apply the synthesis proof on the body directly *)
       ... }
  (* Postcondition bridge: same as mul *)
  ...
Qed.
```

**Files:** Bridge.v
**Effort:** ~30 lines
**Risk:** Medium — need to match the body WP with synthesis output.

---

## Execution Order

1. **Step 1** (valid_func reflection) — standalone, unblocks clean Synthesis.v
2. **Steps 2-4** (bridge lemmas) — can be done in parallel, all in Bridge.v
3. **Step 5** (sqr naming) — depends on Steps 2-4 for the bridge infrastructure

## Total Effort

~155 lines of new proof code across 2 files.
All axioms except Group D (br_memset_ok/br_memcxor_ok) are eliminable.
