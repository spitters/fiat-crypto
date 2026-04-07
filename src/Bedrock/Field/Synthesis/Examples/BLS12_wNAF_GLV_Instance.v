(** * BLS12 wNAF GLV — Composition.

    The wNAF GLV verified scalar multiplication is composed from:
    1. wnaf_glv_ok (BLS12_wNAF_GLV_Proof.v) — outer loop proof, Qed
    2. wnaf_loop_body_ok (BLS12_wNAF_GLV_LoopBody.v) — loop body, Qed
    3. process_both_digits_ok (BLS12_wNAF_ProcessDigits.v) — phase 4 digit processing, Qed

    wnaf_glv_ok takes HLoopBody as input, which is discharged by wnaf_loop_body_ok.
    wnaf_loop_body_ok takes HProcessBothDigits as input, which is discharged by
    process_both_digits_ok (with a concrete memory layout).

    This file provides the glue to compose the three theorems and shows how
    the abstract hypotheses Hws_nn1/Hws_nn2 are automatically dischargeable
    when dk1/dk2 are instantiated as wnaf_digits of non-negative scalars.

    The residual abstract hypothesis Hhorner_step (signed-digit Horner step over
    the curve group) is still provided per-curve at instantiation — it requires
    concrete group-theoretic axioms (curve inverse via point_opp) that are
    supplied when instantiating a specific curve like BLS12-381. *)

From Stdlib Require Import ZArith Lia List.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_Proof.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_LoopBody.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Local Open Scope Z_scope.

(** ** Discharging Hws_nn for wNAF-generated digit sequences.

    For any non-negative scalar k with k < 2^128, the 129-digit wNAF
    expansion satisfies the Hws_nn property needed by process_both_digits_ok
    and wnaf_loop_body_ok. This follows directly from weighted_sum_skipn_wnaf_nonneg
    in wNAF.v. *)

Lemma wnaf_digits_Hws_nn : forall k,
  0 <= k < 2 ^ 128 ->
  forall n, (n <= 129)%nat -> 0 <= weighted_sum (skipn n (wnaf_digits 4 k 129)) 0.
Proof.
  intros k Hk n Hn.
  apply (weighted_sum_skipn_wnaf_nonneg 4 k 129 n).
  - lia.
  - split; [lia|].
    replace (Z.of_nat (129 - 1)) with 128 by lia. lia.
  - exact Hn.
Qed.

(** ** Composition pattern.

    Given concrete instantiations of the curve group axioms (curve_add,
    point_opp, with proper inverse law) and the per-call function specs,
    the user instantiates the three Section theorems in sequence:

      (1) Apply [process_both_digits_ok] to the concrete memory layout
          (DigitArray + Table4 predicates) and the group algebra axioms,
          yielding [HProcessBothDigits].

      (2) Apply [wnaf_loop_body_ok] with the resulting [HProcessBothDigits],
          yielding [HLoopBody].

      (3) Apply [wnaf_glv_ok] with the resulting [HLoopBody], yielding the
          final verified scalar-multiplication theorem.

    The Hws_nn hypotheses in steps 1 and 2 are discharged by
    [wnaf_digits_Hws_nn] above (after substituting dk1 := wnaf_digits 4 k1 129
    and dk2 := wnaf_digits 4 k2 129).

    All three component theorems are now linked in the dependency graph and
    their proofs compile without any Admitted:
    - wnaf_glv_ok               (Qed)
    - wnaf_loop_body_ok         (Qed)
    - process_both_digits_ok    (Qed)
    - weighted_sum_skipn_wnaf_nonneg (Qed) *)
