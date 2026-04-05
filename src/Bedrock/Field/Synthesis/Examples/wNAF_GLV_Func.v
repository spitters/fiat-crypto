(** * wNAF GLV Shamir bedrock2 function body.

    This defines the bedrock2 function for wNAF-based GLV scalar
    multiplication. The loop body:
    1. Double accumulator
    2. Load wNAF digit for k1, conditionally add from table_P
    3. Load wNAF digit for k2, conditionally add from table_Phi

    Unlike the bit-by-bit GLV, P and Phi are NOT doubled each iteration —
    they're stored in precomputed tables. This eliminates 2 doublings
    per iteration (the main speedup source).

    The function assumes:
    - wNAF digits are precomputed and stored as signed bytes
    - Tables of [1]P, [3]P, [5]P, [7]P are precomputed
    - A constant-time table lookup function is available *)

From Stdlib Require Import ZArith Lia.
Require Import Rupicola.Lib.Api.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section WNAFGLVFunc.
  Context (curve_add_name : string).
  Context (curve_double_name : string).
  Context (store_zero_name : string).

  (* Number of wNAF iterations (for BLS12-381: 129, for BLS12-377: 128) *)
  Context (wnaf_iterations : Z).

  (** The bedrock2 function body.

      Parameters:
        outx, outy, outz    — accumulator point (output)
        table_px, ...       — table of [1]P, [3]P, [5]P, [7]P
                              (12 FElems = 4 Jacobian points)
        table_phix, ...     — table for Phi (same layout)
        digits_k1           — wNAF digits for k1 (byte array, S len entries)
        digits_k2           — wNAF digits for k2 (same)

      The tables and digit arrays are precomputed by the caller.
      This function only performs the main Shamir loop.

      For each iteration i from (wnaf_iterations-1) down to 0:
        1. Double acc
        2. d1 = load_byte(digits_k1 + i)
           if d1 != 0:
             idx = (abs(d1) - 1) / 2
             ct_table_lookup(aux, table_P, idx)
             if d1 < 0: negate(auxy)
             curve_add(out, aux, out)
        3. Same for d2 with table_Phi
  *)

  (** For now, we define the SIMPLIFIED loop that assumes the caller
      has already set up everything. The bedrock2 body is parameterized
      over the table operations. *)

  Definition wnaf_glv_loop : Syntax.cmd :=
    cmd.seq
      (cmd.call [] store_zero_name
         [expr.var "outx"; expr.var "outy"; expr.var "outz"])
    (cmd.seq
      (cmd.set "iter" (expr.literal 0))
      (cmd.while
        (expr.op bopname.ltu (expr.var "iter") (expr.literal wnaf_iterations))
        (cmd.seq
          (* Double accumulator *)
          (cmd.call [] curve_double_name
             [expr.var "outx"; expr.var "outy"; expr.var "outz";
              expr.var "outx"; expr.var "outy"; expr.var "outz"])
        (cmd.seq
          (* TODO: load d1, table lookup, conditional add for P *)
          (cmd.skip)
        (cmd.seq
          (* TODO: load d2, table lookup, conditional add for Phi *)
          (cmd.skip)
          (* Increment iter *)
          (cmd.set "iter"
             (expr.op bopname.add (expr.var "iter") (expr.literal 1)))))))).

End WNAFGLVFunc.

(** ** Status

    This file provides the SKELETON of the wNAF GLV bedrock2 function.
    The full implementation requires:

    1. Digit loading: load signed byte from digit array
       - Needs bedrock2 byte-level memory access
       - Or: store digits as word-sized values (simpler, more memory)

    2. Table lookup: constant-time selection from 4 Jacobian points
       - Unrolled loop with select_znz for each FElem
       - Needs array pointer arithmetic

    3. Conditional add: if digit != 0, add table result to accumulator
       - Branch on digit value (or use always-add with identity)

    4. Point negation: if digit < 0, negate Y before adding
       - Single opp call on Y coordinate

    The WP proof follows the same structure as BLS12_GLV_ScalarMultBedrock.v
    but with:
    - wNAF loop invariant (partial weighted sum of digits)
    - Table sep predicates (12 FElems per table, unchanged in loop)
    - Digit array sep predicate (byte/word array, unchanged in loop)

    Estimated: ~1500 lines for the full bedrock2 function + WP proof.
*)
