(** * BLS12 wNAF GLV scalar multiplication — WP proof skeleton.

    Architecture for the WP proof. The loop invariant and proof body
    are outlined; filling them in follows the pattern of
    BLS12_GLV_ScalarMultBedrock.v with:
    - Read-only tables (no P/Phi doubling in loop)
    - Digit loading from word arrays
    - Table lookup + conditional negate + conditional add
    - wNAF partial-sum accumulator invariant *)

From Stdlib Require Import ZArith Lia List.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Architecture overview

    The WP proof has these components:

    1. SECTION PARAMETERS (same as BLS12_GLV_ScalarMultBedrock.v):
       - Field parameters, representation, bounds
       - curve_add and its properties
       - Function specs: HCurveAdd, HCurveDouble, HStoreZero, etc.
       - NEW: HTableLookup, HPointNegate (table + negate specs)

    2. LOOP INVARIANT:
       - Output point = curve_add (scmul (partial_k1) P) (scmul (partial_k2) Phi)
         where partial_k = weighted_sum (firstn iter digits_k)
       - Tables in sep frame (read-only, 12 FElems each)
       - Digit arrays in sep frame (read-only, S len words each)
       - Aux point in sep (scratch space)
       - Iteration counter: iter from 0 to S len

    3. PROOF STRUCTURE:
       a. Apply Loops.while_localsmap with wnaf_loop_inv
       b. TRUE branch (iter < S len):
          - gcall HCurveDouble (double acc)
          - Load digit d1 from memory
          - If d1 != 0: table lookup + negate + gcall HCurveAddInplace
          - Load digit d2, same with Phi table
          - Increment iter
          - Restore invariant using weighted_sum_firstn_succ
       c. FALSE branch (iter = S len):
          - vi = 0, all digits processed
          - By wnaf_correct: partial_sum = k
          - Provide postcondition witnesses

    4. KEY DIFFERENCES from bit-by-bit GLV:
       - No shift_scalar calls (digits precomputed)
       - No P/Phi doubling (tables static)
       - No cmov_alt + store_zero (table lookup replaces this)
       - Fewer sep conjuncts per iteration (tables in frame)
       - ecancel_fast applies directly

    5. ESTIMATED SIZE: ~1200 lines
       (vs ~1500 for BLS12_GLV_ScalarMultBedrock.v, simpler loop body)
*)

(** ** Algebraic connection *)

(** The key bridge: wnaf_shamir_correct connects the loop to [k1]*P + [k2]*Phi.
    This is already proven in wNAF_ScalarMult.v.

    The per-iteration algebraic step: after processing digit d at position n,
      new_acc = 2 * old_acc + d * table_entry
    which corresponds to:
      weighted_sum (firstn (n+1) digits) = 2^n * d + weighted_sum (firstn n digits)
    This is weighted_sum_firstn_succ from wNAF_ScalarMult.v. *)
