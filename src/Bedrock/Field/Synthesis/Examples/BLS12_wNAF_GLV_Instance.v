(** * BLS12 wNAF GLV — Composition.

    The wNAF GLV verified scalar multiplication is composed from:
    1. wnaf_glv_ok (BLS12_wNAF_GLV_Proof.v) — outer loop proof, Qed
    2. wnaf_loop_body_ok (BLS12_wNAF_GLV_LoopBody.v) — loop body, Qed

    wnaf_loop_body_ok discharges HLoopBody of wnaf_glv_ok.
    The remaining hypothesis is HProcessBothDigits, which handles
    digit array loading and table lookup — instantiated per curve. *)

Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_Proof.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_LoopBody.
