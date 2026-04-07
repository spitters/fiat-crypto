# Upstream Patch: straightline_cleanup optimization

## Change
In `bedrock2/ProgramLogic.v`, line 149:

```diff
-  | _ => progress (cbn [Semantics.interp_binop] in * )
+  | _ => progress (cbn [Semantics.interp_binop])
```

## Rationale
`Semantics.interp_binop` only appears in the GOAL during `straightline`
(introduced by `cmd_body` unfolding). It does NOT appear in user hypotheses.
The `in *` causes `cbn` to re-normalize every hypothesis (20-30 sep facts
in typical WP proofs), which is the dominant cost.

## Benchmark
- BN254_FinalExpHardDSD (35 straightline calls): **14m9s → 7m13s (49% faster)**
- BN254_FinalExpDSD (6 straightline calls): **23s → 20s (13% faster)**

## Compatibility
The optimization is safe for all bedrock2 WP proofs where `interp_binop`
does not appear in hypotheses (which is the standard case). If a user
manually introduces `interp_binop` in a hypothesis, they can add
`cbn [Semantics.interp_binop] in H` explicitly.

## Workaround (without upstream change)
Import `BN_StraightlineFast.v` after `bedrock2.ProgramLogic` to override
`straightline_cleanup` via `Ltac ... ::=`.
