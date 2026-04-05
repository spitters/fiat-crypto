(** * wNAF GLV Shamir — bedrock2 function body + WP proof skeleton.

    The main loop: for each iteration, double acc then conditionally
    add table entries based on wNAF digits. Tables and digits are
    precomputed by the caller and passed as pointers.

    This file defines the function body and spec. The WP proof follows
    the same pattern as BLS12_GLV_ScalarMultBedrock.v but with:
    - No P/Phi doubling (tables are read-only)
    - Digit loading from word arrays instead of shift_scalar
    - Table lookup + conditional negate instead of cmov_alt *)

From Stdlib Require Import ZArith Lia.
Require Import Rupicola.Lib.Api.
Require Import bedrock2.Syntax bedrock2.Loops.
Require Import bedrock2.NotationsCustomEntry.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** ** Function body *)

Section FuncBody.
  Context (curve_add_name curve_double_name store_zero_name : string).
  Context (felem_copy_name opp_name : string).
  Context (wnaf_iterations : Z).
  Context (felem_size_bytes : Z). (* bytes per field element *)

  (** Process one digit: branch on d != 0, then lookup + negate + add.
      Uses branching (not constant-time) for simplicity. *)
  Definition process_one_digit
    (digit_var table_base auxx auxy auxz outx outy outz : string) : Syntax.cmd :=
    cmd.cond (expr.var digit_var)
      (* digit != 0 *)
      (cmd.seq
        (* Compute table offset: idx = (|d| - 1) / 2; offset = idx * 3 * felem_size *)
        (* For signed d: if d > 0, idx = (d-1)/2; if d < 0, idx = (-d-1)/2 *)
        (cmd.seq
          (cmd.cond
            (expr.op bopname.lts (expr.var digit_var) (expr.literal 0))
            (cmd.set "lookup_d" (expr.op bopname.sub (expr.literal 0) (expr.var digit_var)))
            (cmd.set "lookup_d" (expr.var digit_var)))
          (cmd.seq
            (cmd.set "tab_idx"
              (expr.op bopname.sru
                (expr.op bopname.sub (expr.var "lookup_d") (expr.literal 1))
                (expr.literal 1)))
            (cmd.set "tab_off"
              (expr.op bopname.mul (expr.var "tab_idx")
                (expr.literal (3 * felem_size_bytes))))))
        (cmd.seq
          (* Copy table[idx] to aux *)
          (cmd.seq
            (cmd.call [] felem_copy_name
              [expr.var auxx;
               expr.op bopname.add (expr.var table_base) (expr.var "tab_off")])
            (cmd.seq
              (cmd.call [] felem_copy_name
                [expr.var auxy;
                 expr.op bopname.add (expr.var table_base)
                   (expr.op bopname.add (expr.var "tab_off")
                     (expr.literal felem_size_bytes))])
              (cmd.call [] felem_copy_name
                [expr.var auxz;
                 expr.op bopname.add (expr.var table_base)
                   (expr.op bopname.add (expr.var "tab_off")
                     (expr.literal (2 * felem_size_bytes)))])))
          (cmd.seq
            (* If d < 0: negate aux_y *)
            (cmd.cond
              (expr.op bopname.lts (expr.var digit_var) (expr.literal 0))
              (cmd.call [] opp_name [expr.var auxy; expr.var auxy])
              cmd.skip)
            (* curve_add(out, aux, out) *)
            (cmd.call [] curve_add_name
              [expr.var outx; expr.var auxx;
               expr.var outy; expr.var auxy;
               expr.var outz; expr.var auxz;
               expr.var outx; expr.var outy; expr.var outz]))))
      (* digit = 0: skip *)
      cmd.skip.

  (** Main wNAF loop body *)
  Definition wnaf_loop_body
    (digits_k1 digits_k2 table_P table_Phi : string) : Syntax.cmd :=
    let word_size := expr.literal (Memory.bytes_per_word 64) in
    cmd.seq
      (* Double accumulator *)
      (cmd.call [] curve_double_name
        [expr.var "outx"; expr.var "outy"; expr.var "outz";
         expr.var "outx"; expr.var "outy"; expr.var "outz"])
    (cmd.seq
      (* Load d1 = digits_k1[iter] *)
      (cmd.set "d1"
        (expr.load access_size.word
          (expr.op bopname.add (expr.var digits_k1)
            (expr.op bopname.mul (expr.var "iter") word_size))))
      (cmd.seq
        (* Process d1 with table_P *)
        (process_one_digit "d1" table_P "auxx" "auxy" "auxz" "outx" "outy" "outz")
      (cmd.seq
        (* Load d2 = digits_k2[iter] *)
        (cmd.set "d2"
          (expr.load access_size.word
            (expr.op bopname.add (expr.var digits_k2)
              (expr.op bopname.mul (expr.var "iter") word_size))))
        (cmd.seq
          (* Process d2 with table_Phi *)
          (process_one_digit "d2" table_Phi "auxx" "auxy" "auxz" "outx" "outy" "outz")
          (* iter++ *)
          (cmd.set "iter"
            (expr.op bopname.add (expr.var "iter") (expr.literal 1))))))).

  (** Full function: init + while loop *)
  Definition wnaf_glv_func_body
    (digits_k1 digits_k2 table_P table_Phi : string) : Syntax.cmd :=
    cmd.seq
      (* Initialize accumulator to identity *)
      (cmd.call [] store_zero_name
        [expr.var "outx"; expr.var "outy"; expr.var "outz"])
      (cmd.seq
        (cmd.set "iter" (expr.literal 0))
        (cmd.while
          (expr.op bopname.ltu (expr.var "iter")
            (expr.literal wnaf_iterations))
          (wnaf_loop_body digits_k1 digits_k2 table_P table_Phi))).

End FuncBody.

(** ** Complete function definition for BLS12-381 *)

Section BLS12_381.
  Definition bls12_wnaf_glv_func : function_t :=
    ("bls12_wnaf_glv_shamir",
     (["outx"; "outy"; "outz";
       "table_P"; "table_Phi";
       "digits_k1"; "digits_k2";
       "auxx"; "auxy"; "auxz"],
      []:list String.string,
      wnaf_glv_func_body "curve_add" "curve_double" "store_zero"
        "felem_copy" "opp" 129
        48 (* felem_size_bytes for BLS12-381: 6 × 8 = 48 *)
        "digits_k1" "digits_k2" "table_P" "table_Phi")).
End BLS12_381.

(** ** WP proof would go here.

    The proof follows BLS12_GLV_ScalarMultBedrock.v pattern:
    1. Section with generic curve parameters
    2. Loop invariant: wnaf_loop_inv
    3. Apply Loops.while_localsmap
    4. TRUE branch: process loop body calls
    5. FALSE branch: postcondition

    Key invariant:
      (Out_x, Out_y, Out_z) =
        curve_add (scmul (wsum (firstn iter digits_k1)) P_init)
                  (scmul (wsum (firstn iter digits_k2)) Phi_init)

    Tables and digit arrays are READ-ONLY (in sep frame, unchanged).
    This simplifies the sep compared to the bit-by-bit GLV where P/Phi
    are modified each iteration.

    Estimated: ~1200 lines for the WP proof.
    The ecancel_fast tactic from BLS12_GLV_ScalarMultBedrock.v applies.
*)
