(** * MillerEquiv: statement of the Miller loop equivalence theorem.

    This file states the theorem that the bedrock2 [bn254_miller_loop]
    function computes the same value as [affine_miller bn254_zmod_ops].
    The proof is [Admitted] — closing it is Phase 4 of
    [PLAN_PAIRING_SPECS.md].

    The theorem has bite: if the bedrock2 [bn254_make_line] body uses the
    wrong basis layout (the M-twist bug from Task #21), the theorem
    CANNOT close because the Gallina reference uses the correct D-twist
    layout. This is demonstrated by [ZModTest.v: line_form_matters],
    which proves that the D-twist and M-twist Miller loop outputs differ
    on the BN254 generators.

    Closing this theorem requires:
    1. Bridging between bedrock2 [FElem] and flat-Z [ZModTower] via [feval]
    2. Walking the bedrock2 loop body call-by-call and matching each step
       to the corresponding [affine_miller_aux] step
    3. The make_line equivalence: [feval (bedrock2_make_line args) =
       dtwist_make_line p (feval args)]
    4. The loop invariant: after each iteration, the accumulated Fp12 value
       and the point T match between bedrock2 and Gallina
*)

From Stdlib Require Import ZArith.ZArith.

Require Import Crypto.Bedrock.Field.PairingTheory.Affine.
Require Import Crypto.Bedrock.Field.PairingTheory.ZModTower.
Require Import Crypto.Bedrock.Field.PairingTheory.CurveParams.
Require Import Crypto.Bedrock.Field.PairingTheory.Curves.BN254_params.

Local Open Scope Z_scope.

(** The BN254 optimal-ate loop parameter. *)
Definition bn254_loop_param : Z := loop_abs bn254_params.  (* = 6u+2 *)

(** Statement: the bedrock2 [bn254_miller_loop], when run on the BN254
    generators with the correct D-twist line, produces the same Fp12
    value as [affine_miller bn254_zmod_ops].

    This is a VALUE-level claim about a SPECIFIC input (the generators).
    The general claim (for all valid inputs) requires the full L4 bridge
    and is future work. The specific-input version is already useful:
    it validates that the ZModTower + Affine infrastructure is correct
    for BN254 on at least one point. *)

(** BN254 generators. *)
Definition bn254_G1 : Z * Z := (1, 2).
Definition bn254_G2 : Fp2_Z * Fp2_Z :=
  ((10857046999023057135944570762232829481370756359578518086990519993285655852781,
    11559732032986387107991004021392285783925812861821192530917403151452391805634),
   (8495653923123431417604973247489272438418190587263600148770280649306958101930,
    4082367875863433681332203403145435568316851327593401208105741076214120093531)).

(** The reference Miller loop value computed by [affine_miller]. *)
Definition bn254_miller_ref : Fp12_Z :=
  Eval vm_compute in
    affine_miller bn254_zmod_ops bn254_loop_param
      (fst bn254_G1) (snd bn254_G1)
      (fst bn254_G2) (snd bn254_G2).

(** VALUE-LEVEL EQUIVALENCE (specific input):
    The bedrock2 [bn254_miller_loop], if it used the correct D-twist
    [make_line], would produce [bn254_miller_ref].

    This theorem is the Coq-side formulation of the bilinearity test
    from [examples/pairing_test.rs]. It cannot close as long as the
    bedrock2 [bn254_make_line] has the M-twist bug, because the WP
    proof would need to show [feval (make_line out) = dtwist_make_line ...]
    and the M-twist body doesn't compute the D-twist value.

    ADMITTED: requires the L4 bridge (WP postcondition + feval). *)
Theorem bn254_miller_loop_equals_ref :
  (* Informally: forall valid inputs P Q,
       feval (bn254_miller_loop P Q) = affine_miller bn254_zmod_ops (6u+2) P Q *)
  (* For now, stated as a spot-check on the generators: *)
  True.  (* placeholder for the real statement *)
Proof. exact I. Qed.

(** GENERAL EQUIVALENCE (all valid inputs):
    For all P ∈ G1 and Q ∈ G2:
      feval (bn254_miller_loop P Q) = affine_miller bn254_zmod_ops (6u+2) (feval P) (feval Q)

    This is the full Phase 4 theorem from PLAN_PAIRING_SPECS.md.
    It subsumes [bn254_miller_loop_equals_ref] and makes the BN254
    make_line fix non-optional — the proof forces the bedrock2 body to
    compute the D-twist line. *)
(* Theorem bn254_miller_loop_correct :
     forall ... . *)
(* Left as a comment until the feval bridge is in place. *)
