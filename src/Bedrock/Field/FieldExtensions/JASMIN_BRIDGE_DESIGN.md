# Bedrock2 → Jasmin Formal Bridge Design

## Architecture

```
bedrock2 exec (Rocq, coqutil maps)
    ↓ ToJasmin.tr_cmd (structural homomorphism, Qed)
jasmin_cmd (our intermediate AST)
    ↓ bridge_sem (state relation, this design doc)
Jasmin sem (Rocq, mathcomp/ssreflect maps)
    ↓ jasminc (Jasmin compiler correctness, Rocq)
x86-64 semantics
```

## Key Findings

### Jasmin's Coq Semantics

- **File**: `jasmin/proofs/lang/psem.v` line 48
- **Type**: `Inductive sem : estate -> cmd -> estate -> Prop`
- **estate**: `{ escs: syscall_state; emem: mem; evm: Vm.t }`
- **cmd**: `seq instr` where `instr = MkI info instr_r`
- **instr_r**: `Cassgn | Copn | Cif | Cfor | Cwhile | Ccall | ...`
- **No stackalloc** in instr_r — stack is handled at function level via `f_extra`

### Dependencies

Jasmin uses:
- mathcomp/ssreflect (seq, ssrbool, etc.)
- Custom memory model (`memory_model.v`)
- Custom variable map (`Vm.t`)

bedrock2 uses:
- coqutil (map.map, word.word)
- Standard Rocq stdlib

### State Relation

```
bedrock2                    Jasmin
────────                    ──────
trace                  ↔    escs (syscall_state)
mem (map word byte)    ↔    emem (Jasmin mem)
locals (map string word) ↔  evm (Vm.t)
metrics                     (no equivalent)
```

The memory models are the key challenge:
- bedrock2: `map.map word Byte.byte` (coqutil)
- Jasmin: abstract `mem` type with `read`/`write` operations

### Bridge Approach

**Option A: Shared memory model** (~500 lines)

Define a functor that takes both memory models as parameters and
proves the simulation assuming they implement the same operations.
This avoids importing either library into the other.

```coq
Module Type MemBridge.
  Parameter mem_br2 : Type.  (* bedrock2 mem *)
  Parameter mem_jas : Type.  (* Jasmin mem *)
  Parameter mem_relate : mem_br2 -> mem_jas -> Prop.
  Axiom read_compat : forall mb mj a v,
    mem_relate mb mj ->
    map.get mb a = Some v <-> Jasmin.read mj a = ok v.
  Axiom write_compat : ...
End MemBridge.
```

**Option B: Concrete instantiation** (~1000 lines)

Instantiate both bedrock2 and Jasmin with the same concrete memory
(e.g., `FMap` or sorted lists). Prove the simulation for this
concrete instance. Requires installing mathcomp + building Jasmin's
Coq library.

**Option C: Semantic bridge via extraction** (~200 lines)

Don't prove the bridge in Coq. Instead:
1. Extract both bedrock2's `exec` and Jasmin's `sem` to OCaml
2. Run both on the same inputs
3. Compare results (differential testing)

This is pragmatic but not a formal proof.

### Recommendation

**Option A** is the cleanest. The bridge is parametric over the
memory model — it doesn't need mathcomp. The simulation proof
would be ~500 lines of structural induction, similar to
`flatten_two_stackallocs_equiv`.

The key lemma per constructor:

```coq
Lemma bridge_Cassgn : forall s_br2 s_jas x e v,
  state_relate s_br2 s_jas ->
  eval_expr_br2 m l e = Some v ->
  eval_pexpr_jas s_jas (tr_expr_to_pexpr e) = ok (to_jasmin_val v) ->
  ... (write to x in both) ...
  state_relate s_br2' s_jas'.
```

### Prerequisites

1. Install Jasmin Coq library: `opam install coq-jasmin` or build from source
2. Install mathcomp: `opam install coq-mathcomp-ssreflect`
3. Add Jasmin's `-R` paths to our `_CoqProject`
4. Write the `MemBridge` functor + state relation
5. Prove simulation by structural induction on `cmd_jasmin_equiv`

### Estimated Effort

| Component | Lines | Depends on |
|-----------|-------|------------|
| MemBridge module type | 50 | nothing |
| State relation | 100 | MemBridge |
| Expression bridge | 100 | State relation |
| Command simulation (per constructor) | 300 | Expression bridge |
| **Total** | **~550** | mathcomp + Jasmin Coq |
