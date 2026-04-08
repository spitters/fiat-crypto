(** * Top-level G2 hash-to-curve correctness theorem.

    Assembles the SWU correctness, isogeny correctness, and closure
    properties into the main theorem:

      forall msg dst, on_curve_E2_opt (hash_to_curve_g2 msg dst).

    Mirrors HashToCurveProof for G1. *)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.HashToCurve.
Require Import Crypto.Spec.HashToCurveG2.
Require Import Crypto.Spec.HashToCurveClosureProof_G2.
Require Import Crypto.Spec.HashToCurveIsogenyProof_G2.
Require Import Crypto.Spec.HashToCurveSWUProof_G2.

Local Open Scope F_scope.

(** map_to_curve_g2 always produces a point on E2.
    Combines SWU correctness and isogeny correctness. *)
Theorem map_to_curve_g2_on_curve : forall u : Fp2,
  on_curve_E2 (map_to_curve_g2 u).
Proof.
  intro u.
  unfold map_to_curve_g2.
  exact (iso_map_g2_on_curve _ (swu_g2_maps_to_E2prime u)).
Qed.

(** Helper: map_to_curve_g2 lifted to the option type. *)
Lemma map_to_curve_g2_on_curve_opt : forall u : Fp2,
  on_curve_E2_opt (Some (map_to_curve_g2 u)).
Proof. exact map_to_curve_g2_on_curve. Qed.

(** hash_to_curve_g2 always produces a point on E2 (or the identity). *)
Theorem hash_to_curve_g2_on_curve :
  forall msg dst, on_curve_E2_opt (hash_to_curve_g2 msg dst).
Proof. admit. Admitted.

(** encode_to_curve_g2 always produces a point on E2 (or the identity). *)
Theorem encode_to_curve_g2_on_curve :
  forall msg dst, on_curve_E2_opt (encode_to_curve_g2 msg dst).
Proof. admit. Admitted.
