# Aliased Calling Conventions in bedrock2: Cookbook

## Problem

bedrock2's separation logic requires pointer arguments to be **disjoint** (non-aliasing). The `spec_of_ladderstep` requires 9 distinct FElem regions:

```
(FElem pX1 X1 * FElem pX2 X2 * ... * FElem pXout Xoutold * ... * R) m
```

But many algorithms (scalar multiplication, in-place accumulation) need **aliased** calling conventions where output overwrites input:

```
curve_add(pX1, pX2, pY1, pY2, pZ1, pZ2, pX1, pY1, pZ1)
                                          ^^^  ^^^  ^^^  output = input1
```

## Why derivation fails

You **cannot** derive the aliased spec from the non-aliased spec:

```coq
(* This is IMPOSSIBLE: *)
Lemma inplace_from_nonaliased :
  spec_of_ladderstep functions ->
  spec_of_ladderstep_inplace functions.
```

Because instantiating `pXout := pX1` in the non-aliased precondition creates `(FElem pX1 X1 * FElem pX1 Xoutold * ...)`, which is `False` (two FElems at the same address violates sep).

## Solution: Stack-Temporary Wrapper

Define a NEW bedrock2 function that:
1. **Allocates** stack temporaries for the output
2. **Calls** the original function with non-aliased args (input pointers + stack temps)
3. **Copies** results from stack temps back to the aliased output pointers
4. **Deallocates** the stack temporaries

```coq
Definition curve_add_inplace_wrapper : function_t :=
  ("curve_add_inplace",
   (["pX1"; "pX2"; "pY1"; "pY2"; "pZ1"; "pZ2"], [],
    cmd.stackalloc "tx" felem_size_in_bytes
    (cmd.stackalloc "ty" felem_size_in_bytes
    (cmd.stackalloc "tz" felem_size_in_bytes
    (cmd.seq
      (cmd.call [] "curve_add"
        [expr.var "pX1"; expr.var "pX2";
         expr.var "pY1"; expr.var "pY2";
         expr.var "pZ1"; expr.var "pZ2";
         expr.var "tx";  expr.var "ty";  expr.var "tz"])
    (cmd.seq
      (cmd.call [] felem_copy [expr.var "pX1"; expr.var "tx"])
    (cmd.seq
      (cmd.call [] felem_copy [expr.var "pY1"; expr.var "ty"])
      (cmd.call [] felem_copy [expr.var "pZ1"; expr.var "tz"])))))))).
```

## Proof Structure (~120 lines)

The wrapper correctness proof has 5 phases, all using standard bedrock2 tactics:

### Phase 1: Function Entry
```coq
eapply start_func; [exact HEnv|].
cbv [WeakestPrecondition.func]. simpl snd.
eexists. split. { exact eq_refl. }
```

### Phase 2: Stack Allocations
For each of `tx`, `ty`, `tz`:
```coq
repeat straightline.
split. { apply felem_size_in_bytes_mod. }           (* alignment *)
intros a_tx mStack_tx mComb_tx Hany_tx Hsplit_tx.   (* intro stack ptr/mem *)
```
Then convert anybytes to FElem:
```coq
pose proof (P_from_bytes a_tx mStack_tx Hany_tx) as [tx_init Hfe_tx].
```

### Phase 3: Non-Aliased Function Call
```coq
eapply Semantics.weaken_call.
1: { eapply HCurveAdd. ecancel_assumption. }
intros tr' m' rets [Xo' [Yo' [Zo' [HEq Hpost]]]].
```

### Phase 4: Copy Back (3x felem_copy)
For each output coordinate:
```coq
repeat straightline.
eapply Semantics.weaken_call.
1: { eapply HFelemCopy. ecancel_assumption. }
intros tr' m'' rets'' [Hrets'' [Htr'' Hsep'']]. subst.
```

### Phase 5: Stack Deallocation
Convert FElems back to anybytes and provide map.split witnesses:
```coq
pose proof (P_to_bytes a_tx _ _ Hfe_tx) as Hany_tx'.
eexists _, _. split. { exact Hany_tx'. }
split. { (* map.split from chain *) ... }
```

## Codebase Precedent

The existing BLS12 GLV chain (`BLS12_GLV_ScalarMultBedrock.v`) uses the same pattern:
- Lines 590-634: 6 stackallocs with `P_from_bytes` / `anybytes_to_scalar`
- Lines 1178, 1204: `gcall_clean HCurveAddInplace` applies the aliased spec
- `HCurveAddInplace` is taken as a Section hypothesis (never proved in src/)

The wrapper approach provides a concrete discharge path for these hypotheses.

## When to Use This Pattern

Use the stack-temporary wrapper when:
- A function's spec requires disjoint input/output (via sep)
- Callers need aliased input = output for in-place accumulation
- The function body does NOT natively support aliasing

Do NOT use when:
- The function body already copies inputs to stack (then aliasing is natively safe, but requires re-proving the body)
- The function has explicit in/out overlap support in its spec (like some `felem_copy` implementations)

## File Reference

- `CurveAddInplaceWrapper.v`: wrapper definition + spec + proof template
- `CurveAddInplace.v`: original (intractable) approach with direct admits
- `BLS12_GLV_ScalarMultBedrock.v`: precedent for taking HCurveAddInplace as hypothesis
- `BLS12_PowGeneric.v`: example of start_func + stackalloc + weaken_call pattern
