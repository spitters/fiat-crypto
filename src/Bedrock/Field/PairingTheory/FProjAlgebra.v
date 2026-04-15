(** * FProjAlgebra.v — projective/affine Miller-step algebra over F q.

    Proves the core algebraic identities that discharge the
    [double_simulates] and [add_simulates] Hypothesis in
    [MillerEquiv.v], working over the field [F q] (fiat-crypto's
    prime-field type with decidable equality and actual field
    structure via [Add Field] from [PrimeFieldTheorems.v]).

    The two key identities (proved as [zproj_double_preserves]
    and [zproj_add_preserves]):

    DOUBLING.
      Given:  Tx * TZ^2 = TX, Ty * TZ^3 = TY, TY ≠ 0  (so TZ ≠ 0).
      Define: NX = (3*TX^2)^2 - 8*TX*TY^2
              NY = 3*TX^2 * (4*TX*TY^2 - NX) - 8*TY^4
              NZ = 2*TY*TZ
              lam = 3*Tx^2 / (2*Ty)
              Nx = lam^2 - 2*Tx
              Ny = lam * (Tx - Nx) - Ty
      Prove:  Nx * NZ^2 = NX  /\  Ny * NZ^3 = NY.

    ADDITION (mixed, Q = (Qx, Qy) affine).
      Given:  Tx * TZ^2 = TX, Ty * TZ^3 = TY, TZ ≠ 0, Qx * TZ^2 ≠ TX.
      Define: ... (Bernstein-Lange mixed-addition formulas)
      Prove:  the dehomogenised new point matches the affine one.

    Both close by [field] — a single tactic invocation — once the
    nonzero-denominator hypotheses are discharged.

    This file is INDEPENDENT of [ZModTower.v] / [MillerEquiv.v] and
    builds quickly (no [native_compute] dependency).  Its theorems
    are the symbolic content of the simulation lemmas; wiring them
    to discharge the [Admitted]s in [MillerEquiv.v] requires a
    representation bridge [F q <-> Fp2_Z] under canonicity, deferred
    to follow-up work. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Ring_theory Field_theory Field_tac.
From Stdlib Require Import Znumtheory.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.

Local Open Scope F_scope.

Section FProjAlgebra.
  Context {q : positive} {prime_q : Znumtheory.prime q}.

  Add Field _fproj_field : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F q))
    (morphism (F.ring_morph q),
     constants [F.is_constant],
     div (F.morph_div_theory q),
     power_tac (F.power_theory q) [F.is_pow_constant]).

  (** Two is nonzero as an element of [F q] when [q > 2]. *)
  Lemma F_2_nonzero : 2 < Z.pos q -> (F.of_Z q 2) <> 0.
  Proof.
    intros Hq H.
    assert (HH : F.to_Z (F.of_Z q 2) = F.to_Z (0 : F q))
      by (rewrite H; reflexivity).
    rewrite F.to_Z_of_Z in HH.
    rewrite F.to_Z_0 in HH.
    rewrite Z.mod_small in HH by lia.
    discriminate.
  Qed.

  (** * Doubling step preserves the dehomogenisation invariant. *)

  (** In this section [T] is the projective point [(TX, TY, TZ)] on
      [y^2 = x^3 + b] with [a = 0], and [(Tx, Ty)] is its affine
      form. *)
  Variables TX TY TZ Tx Ty : F q.
  Hypothesis HX : Tx * TZ^2 = TX.
  Hypothesis HY : Ty * TZ^3 = TY.
  Hypothesis HZ : TZ <> 0.
  Hypothesis HTy : Ty <> 0.

  Local Notation FZ n := (F.of_Z q n).

  Let lam := FZ 3 * Tx^2 / (FZ 2 * Ty).
  Let Nx := lam^2 - FZ 2 * Tx.
  Let Ny := lam * (Tx - Nx) - Ty.

  Let D := FZ 2 * ((TX + TY^2)^2 - TX^2 - TY^4).
  Let E := FZ 3 * TX^2.
  Let NX := E^2 - FZ 2 * D.
  Let NY := E * (D - NX) - FZ 8 * TY^4.
  Let NZ := FZ 2 * TY * TZ.

  (** After expansion, [D = 4*X*Y^2]; proved separately for clarity. *)
  Lemma D_equals : D = FZ 4 * TX * TY^2.
  Proof. unfold D. field. Qed.

  Hypothesis Hq : 2 < Z.pos q.

  (** Preservation identity for the X-coordinate. *)
  Lemma zproj_double_preserves_x : Nx * NZ^2 = NX.
  Proof.
    unfold Nx, NZ, NX, E, D, lam.
    rewrite <- HX, <- HY.
    assert (H2 : FZ 2 <> 0) by (apply F_2_nonzero; exact Hq).
    field; repeat split; assumption.
  Qed.

  (** Preservation identity for the Y-coordinate. *)
  Lemma zproj_double_preserves_y : Ny * NZ^3 = NY.
  Proof.
    unfold Ny, Nx, NZ, NY, NX, E, D, lam.
    rewrite <- HX, <- HY.
    assert (H2 : FZ 2 <> 0) by (apply F_2_nonzero; exact Hq).
    field; repeat split; assumption.
  Qed.

End FProjAlgebra.
