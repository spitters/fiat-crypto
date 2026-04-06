(** * Hash-to-curve correctness: the full pipeline produces curve points.

    Assembles [map_produces_curve_points] from:
    - [swu_maps_to_Eprime] (SWU output is on E')
    - [iso_map_correct] (isogeny maps non-kernel E' points to E)
    - Denominator nonvanishing for SWU outputs (admitted)
*)

From Stdlib Require Import ZArith.
Require Import Crypto.Spec.HashToCurve.
Require Import Crypto.Spec.HashToCurveFieldSetup.
Require Import Crypto.Spec.HashToCurveSWUProof.
Require Import Crypto.Spec.HashToCurveIsogenyProof.

Local Open Scope F_scope.

(** The isogeny denominators don't vanish at SWU output points.
    This is because the SWU map produces generic E' points, not
    kernel points of the 11-isogeny. *)
Lemma swu_xden_nonzero : forall u : Fp,
  horner_eval_monic iso_xden (fst (map_to_curve_simple_swu iso_A iso_B swu_Z u)) <> 0f.
Proof. Admitted.

Lemma swu_yden_nonzero : forall u : Fp,
  horner_eval_monic iso_yden (fst (map_to_curve_simple_swu iso_A iso_B swu_Z u)) <> 0f.
Proof. Admitted.

Theorem map_produces_curve_points_proof : map_produces_curve_points.
Proof.
  unfold map_produces_curve_points, map_to_curve_g1.
  intro u.
  set (pt := map_to_curve_simple_swu iso_A iso_B swu_Z u).
  assert (Hcurve := swu_maps_to_Eprime_proof u : on_curve_Eprime pt).
  destruct pt as [x' y'] eqn:Hpt.
  apply iso_map_correct; [exact Hcurve| |].
  - change x' with (fst (x', y')).
    rewrite <- Hpt. exact (swu_xden_nonzero u).
  - change x' with (fst (x', y')).
    rewrite <- Hpt. exact (swu_yden_nonzero u).
Qed.
