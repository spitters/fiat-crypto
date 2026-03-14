# Plan: WP Proof Automation for Field Extension Operations (Option C)

## Goal

Build three Ltac tactics that reduce 300-1000 line manual WP proofs to ~15-30 lines. No changes to Rupicola. Targets the bedrock2 WeakestPrecondition proofs for Fp6/Fp12 operations.

## Current State

Every WP proof follows the same 4-phase structure:

```
SETUP → PER-CALL (×N) → STACK DEALLOCATION → POSTCONDITION
```

The phases are 90%+ mechanical. The only parts that vary are:
- Number/types of stackallocs
- Number/types of sub-calls (binop vs unop vs copy vs custom)
- Pointer expressions for each call
- Which output feeds into which subsequent input
- Bridge lemmas in feval section (for cross-module Gallina spec mismatches)

## Architecture

```
┌─────────────────────────────────────────────────────┐
│ field_ext_setup                                     │
│   program_logic_goal_for unfold                     │
│   start_func                                        │
│   stackalloc handling (N stackallocs)               │
│   FElem_from_bytes for each stack allocation         │
│   precondition decomposition (Hmemx/Hmemy/Hmemout)  │
│   FElem_to_bytes aliasing resolution                │
│   FElem split (Fp12→Fp6 or Fp6→Fp2)                │
│   bounded_by decomposition                          │
│   big sep fact construction                         │
└─────────────────────────────────────────────────────┘
                         │
                         ▼ (repeat N times)
┌─────────────────────────────────────────────────────┐
│ field_ext_call                                      │
│   exists [arg_words]. split. { solve_dexprs. }      │
│   eapply Semantics.weaken_call                      │
│   1: { eapply (HFk args values frame tr).           │
│        split; [solve_bounds |]. ...                  │
│        ecancel_assumption (×2-3) }                  │
│   intros ... [Hrets [Htr [out' [Hfeval [Hbound      │
│              Hsep]]]]].                             │
│   subst. cbv [map.putmany_of_list_zip].             │
│   exists lN. split. { exact eq_refl. }              │
│   repeat straightline.                              │
└─────────────────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────┐
│ field_ext_finish                                    │
│   destructure final sep into atomic maps            │
│   split_all_disjointness                            │
│   FElem_length for each component                   │
│   per-stack deallocation:                           │
│     FElem_join (sub-components → compound FElem)    │
│     FElem_to_bytes → anybytes                       │
│     exists remaining, deallocated. split.            │
│     { exact Hanybytes. }                            │
│     split. { split. solve_putmany_eq. disjoint. }   │
│   final postcondition:                              │
│     cbv [list_map get]. split. { exact eq_refl. }   │
│     exists (out0' ++ out1' [++ out2']).              │
│     split. { feval_eq + rewrite + reflexivity }     │
│     split. { bounded_by_eq + split + assumptions }  │
│     { FElem_join + exists + solve_putmany_eq }      │
└─────────────────────────────────────────────────────┘
```

## Tactic Specifications

### Tactic 1: `field_ext_setup` (Day 1)

**Input:** Goal from `program_logic_goal_for_function!`

**Output:** Goal ready for the first `field_ext_call`, with:
- All stackallocs processed, `FElem_from_bytes` applied
- Preconditions decomposed into individual map hypotheses
- Aliasing resolved (FElem_to_bytes + anybytes_unique_domain)
- FElems split into sub-components (Fp12→Fp6 or Fp6→Fp2)
- `bounded_by` decomposed to sub-field level
- A master sep fact `Hsep` containing all FElem regions + Rr

**Implementation strategy:**

This is the hardest tactic because the setup varies the most between proofs. Rather than fully automating it, provide a semi-automated version:

```coq
Ltac field_ext_preamble :=
  cbv beta delta [program_logic_goal_for];
  intros;
  match goal with
  | H : spec_of _ |- _ => unfold_head H
  end;
  intros;
  eapply start_func; [assumption | clear_env];
  cbv_func_body;
  eexists; split; [exact eq_refl |];
  repeat straightline.

Ltac process_stackalloc :=
  split; [apply Z_mod_mult |];
  intros ? ? ? ? ?;
  repeat straightline;
  match goal with
  | Hstack : Memory.anybytes ?ptr _ ?mstack |- _ =>
    let Hfb := fresh "Hfb" in
    let val := fresh "val" in
    let Hfe := fresh "Hfe" in
    pose_FElem_from_bytes ptr mstack Hstack val Hfe
  end.

Ltac decompose_preconditions :=
  (* Destruct Hmemx, Hmemy (if binop), Hmemout *)
  (* Apply FElem_to_bytes + anybytes_unique_domain *)
  (* Subst all join equalities *)
  ...
```

**Complexity:** Medium-high. The big sep fact construction is the hardest part — it depends on the number of regions (7 for Fp12 binop, 5 for Fp12 unop, 10 for Fp6 binop, etc.). May need a helper that takes a list of `(ptr, val, map)` triples.

**Fallback:** If full automation is too fragile, provide `field_ext_preamble` + `process_stackalloc` as building blocks and let the user manually construct the big sep fact. This still saves ~100 lines per proof.

### Tactic 2: `field_ext_call` (Day 2-3)

**Input:**
- Current goal: a `WeakestPrecondition.cmd` for a `cmd.call`
- In context: a master sep hypothesis `Hsep` and function spec hypothesis `HFk`

**Output:**
- Call completed
- New hypotheses: `Hfeval_k`, `Hbound_k`, updated `Hsep`
- Goal advanced to next `cmd.call` or postcondition

**Implementation strategy:**

The per-call pattern is highly uniform. Key insight: `ecancel_assumption` already handles sep frame inference. The main things to automate:

1. **Argument computation:** `exists [args]. split. { solve_dexprs. }` — already automated by `solve_dexprs`
2. **Call dispatch:** `eapply Semantics.weaken_call` + `eapply (HFk ...)` — needs to figure out which hypothesis to use and what arguments to pass
3. **Precondition provision:** `split; [solve_bounds|]. ... ecancel_assumption` — already mostly automated
4. **Post-call cleanup:** `intros ... subst. cbv. exists. split. { exact eq_refl. } repeat straightline.` — fully mechanical

```coq
Ltac field_ext_call :=
  (* Step 1: Solve dexprs *)
  lazymatch goal with
  | |- WeakestPrecondition.cmd _ _ _ _ (cmd.seq (cmd.call _ _ _) _) =>
    repeat straightline;
    eexists; split; [solve_dexprs |]
  end;
  (* Step 2: weaken_call + apply function hypothesis *)
  eapply Semantics.weaken_call;
  [ match goal with
    | HF : forall _ _ _, _ |- _ => eapply HF
    | HF : forall _ _, _ |- _ => eapply HF
    end;
    (* Step 3: Provide preconditions *)
    repeat first
      [ solve_bounds
      | split
      | eexists; ecancel_assumption_with_copy
      | ecancel_assumption_with_copy ]
  | ];
  (* Step 4: Post-call cleanup *)
  intros ? ? ? ?;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  end;
  subst;
  try (cbv [map.putmany_of_list_zip]);
  try (eexists; split; [exact eq_refl |]);
  repeat straightline.
```

Where `ecancel_assumption_with_copy` is:
```coq
Ltac ecancel_assumption_with_copy :=
  match goal with
  | Hsep : (_ * _)%sep ?m |- _ =>
    let H' := fresh "H'" in
    pose proof Hsep as H'; ecancel_assumption
  end.
```

**Complexity:** Medium. The main risk is that `ecancel_assumption` may not always find the right frame, especially after several calls have modified the sep state. May need to rebuild the sep fact between calls.

**Key insight from analysis:** After the big sep fact is established, EVERY operation call uses the same `pose proof Hsep as H'. ecancel_assumption` pattern for all 2-3 sep obligations. This is because `ecancel_assumption` is smart enough to find the right sub-frame from the big sep fact. The big sep fact persists unchanged — each call produces a NEW sep fact that becomes the Hsep for the next call.

### Tactic 3: `field_ext_finish` (Day 3-4)

**Input:** Goal after all calls complete. Context has:
- Final sep hypothesis with N FElem regions
- `Hfeval_k`, `Hbound_k` for each output sub-component
- Stack allocation pointers and original input values

**Output:** Proof completed (Qed).

**Implementation strategy:**

Split into sub-tactics:

```coq
(* Peel N layers of sep into individual map hypotheses *)
Ltac destructure_sep H :=
  lazymatch type of H with
  | (_ * _)%sep _ =>
    let m1 := fresh "m" in let m2 := fresh "m" in
    let Heq := fresh "Heq" in let Hd := fresh "Hd" in
    let H1 := fresh "H" in let H2 := fresh "H" in
    destruct H as [m1 [m2 [[Heq Hd] [H1 H2]]]];
    subst; destructure_sep H2
  | _ => idtac
  end.

(* Deallocate one stack region *)
Ltac dealloc_stack ptr felem_inst repr_inst map_var Hfe :=
  let Hbytes := fresh "Hbytes" in
  pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
    felem_inst repr_inst ptr _ map_var Hfe) as Hbytes;
  unfold AbstractField.Placeholder in Hbytes;
  eexists _, map_var;
  split; [exact Hbytes |];
  split; [split; [solve_putmany_eq | map_disjoint_auto] |].

(* For compound stacks: join sub-FElems first *)
Ltac join_and_dealloc_stack join_lemma decomp_lemma ... :=
  ...

(* Assemble final postcondition *)
Ltac field_ext_postcondition feval_tac bounded_tac :=
  cbv [list_map get];
  split; [exact eq_refl |];  (* rets = nil *)
  eexists;                    (* exists out *)
  split; [feval_tac |];       (* feval *)
  split; [bounded_tac |];     (* bounded_by *)
  ...                         (* sep *)
```

**Complexity:** Medium. The stack deallocation order must match the allocation order (innermost first). The final postcondition's feval section may need proof-specific bridge lemmas.

## Implementation Plan

### Day 1: Foundation + `field_ext_call`

Start with the highest-ROI tactic. Build `field_ext_call` and test it on the already-proved `Fp12_add_ok`:

1. Define `ecancel_assumption_with_copy` helper
2. Define `field_ext_call` core logic
3. Refactor `Fp12_add_ok` to use it — verify each of the 4 calls (2 copies + 2 adds) works
4. Test on `Fp12_sub_ok` (should be identical)
5. Test on `Fp12_opp_ok` (unop variant: 1 copy + 2 opps)

**Success metric:** Each sub-call goes from ~20-80 lines to 1 line (`field_ext_call.`)

### Day 2: `field_ext_setup` building blocks

Build the setup automation, starting with the most mechanical parts:

1. `field_ext_preamble` — everything before stackallocs
2. `process_stackalloc` — one stackalloc iteration
3. `decompose_preconditions` — destruct Hmemx/Hmemy/Hmemout + aliasing
4. `split_felems` — apply `FpN_raw_FElem_split` to all input/output FElems
5. `build_sep` — construct the master sep fact from decomposed maps

Test by refactoring `Fp12_add_ok` setup section.

**Success metric:** Setup goes from ~200 lines to ~5 lines.

### Day 3: `field_ext_finish` + bridge lemmas

1. `destructure_sep` — peel final sep into atomic maps
2. `dealloc_stack` — single stack deallocation
3. `join_and_dealloc` — compound stack (Fp6/Fp12 in Fp2/Fp6 components)
4. `field_ext_postcondition` — final feval/bounded/sep assembly
5. Bridge lemmas: `BLS12Fp6Spec.fp6_mul = BLS12Fp12Spec.fp6_mul` etc.

Test by refactoring `Fp12_add_ok` finish section.

**Success metric:** Finish goes from ~100 lines to ~5 lines.

### Day 4: New proofs using automation

With automation in place, prove the remaining stubs:

1. `Fp6_mul_by_v_ok` — 6 Fp2 calls (needs Fp6→Fp2 decomposition; may need CubicFieldExtensions import)
2. `Fp12_conjugate_ok` — 2 Fp6 calls, no stackalloc
3. `Fp12_mul_ok` — 9 Fp6 calls, 4 stackallocs (Karatsuba)
4. `Fp12_sqr_ok` — 7 Fp6 calls, 3 stackallocs
5. `Fp12_inv_ok` — 10 Fp6 calls, 2 stackallocs

**Success metric:** Each proof is 15-30 lines.

### Day 5: Hardening + remaining proofs

1. Fix edge cases found in Day 4
2. Prove Phase 4 ops (Frobenius, cross-cutting)
3. Document the tactics for future use

## File Organization

All automation goes in a single new file:

```
src/Bedrock/Field/FieldExtensions/FieldExtensionAutomation.v
```

This file:
- Imports Rupicola.Lib.Api, AbstractField, bedrock2.WeakestPrecondition
- Defines all `Ltac` tactics at the top level (not inside a Section)
- Has NO Section variables — tactics are fully generic
- Is imported by DodecicFieldExtensions.v, CubicFieldExtensions.v, PairingFieldOps.v

Existing per-file tactics (`solve_dexprs`, `fp12_feval_eq`, etc.) remain as `Local Ltac` — they handle file-specific instance bridging.

## Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| `ecancel_assumption` fails for complex sep frames | Fall back to manual sep frame construction; add `Hint` lemmas |
| `field_ext_call` can't determine which `HF` to use | Pass it as argument: `field_ext_call HFadd2` |
| Copy calls have different structure than op calls | Separate `field_ext_copy_call` tactic |
| Compound stack deallocation (FElem join) is fragile | Provide `join_and_dealloc` as explicit helper, not fully automatic |
| Bridge lemmas between BLS12Fp6Spec/BLS12Fp12Spec | Prove once, add to hint database |
| feval section needs proof-specific rewrites | Accept manual feval for complex ops; automate only for componentwise ops |

## Expected Outcome

| Proof | Manual (lines) | Automated (lines) |
|-------|---------------|-------------------|
| Fp12_add_ok | 325 | ~15 |
| Fp12_sub_ok | 316 | ~15 |
| Fp12_opp_ok | 186 | ~12 |
| Fp12_conjugate_ok | ~180 | ~12 |
| Fp12_mul_ok | ~800 | ~25 |
| Fp12_sqr_ok | ~600 | ~20 |
| Fp12_inv_ok | ~800 | ~25 |
| Fp6_mul_by_v_ok | ~500 | ~20 |
| bls12_G2_ok (34 calls) | ~2000 | ~50 |

Total: ~5700 manual lines → ~200 automated lines + ~300 lines of tactic definitions.
