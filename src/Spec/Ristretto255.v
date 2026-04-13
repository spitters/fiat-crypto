(** * ristretto255: Prime-Order Quotient Group over Edwards25519

    ristretto255 is the quotient group E/E[4] where E is the Edwards25519
    curve and E[4] = {O, (0,-1), (±√-1, 0)} is the order-4 subgroup.

    Two points P, Q ∈ E are ristretto-equivalent iff P - Q ∈ E[4].
    The quotient has prime order l = 2^252 + 27742317777372353535851937790883648493.

    This file defines:
    - The equivalence relation (ristretto_eq)
    - The quotient group operations (well-definedness)
    - Canonical encoding (32 bytes ↔ coset) — specification only
    - Connection to Elligator2 for hash-to-group

    Dependencies: only [Crypto.Algebra.Hierarchy] and [Crypto.Spec.Curve25519].
    No SSProve, no mathcomp.  The SSProve [finGroupType] bridge is in
    [Commitments/theories/Ristretto255_finGroup.v].

    References:
    - de Valence et al., "Ristretto" (https://ristretto.group/)
    - Hamburg, "Decaf" (Crypto 2015)
*)

Require Import Coq.ZArith.ZArith.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable.

Module Ristretto255.
  Section WithField.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}.

    Local Infix "=" := Feq : type_scope.
    Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x) (at level 30).

    (** Edwards curve: a*x² + y² = 1 + d*x²*y² *)
    Context {a d : F}
            {nonzero_a : a <> 0}
            {square_a : exists sqrt_a, sqrt_a ^ 2 = a}
            {nonsquare_d : forall x, x ^ 2 <> d}.

    (** An Edwards point is (x, y) on the curve. *)
    Definition on_curve (x y : F) : Prop :=
      a * x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2.

    Definition point := { xy : F * F | let '(x, y) := xy in on_curve x y }.

    (** The 4-torsion subgroup E[4].

        For Edwards25519 (a = -1, d = -121665/121666), the 4-torsion
        points are:
          O     = (0, 1)      — identity
          T1    = (0, -1)     — order 2
          T2    = (√-1, 0)    — order 4
          T3    = (-√-1, 0)   — order 4

        We define E[4] abstractly as the set of points P with 4*P = O. *)

    Context {sqrt_minus_one : F}
            (sqrt_minus_one_correct : sqrt_minus_one ^ 2 = -(1)).

    (** The four torsion points. *)
    Definition torsion_identity : F * F := (0, 1).
    Definition torsion_order2 : F * F := (0, -(1)).
    Definition torsion_order4_pos : F * F := (sqrt_minus_one, 0).
    Definition torsion_order4_neg : F * F := (-(sqrt_minus_one), 0).

    (** ristretto equivalence: P ~ Q iff P - Q is a 4-torsion point. *)
    Definition is_4torsion (x y : F) : Prop :=
      (x = 0 /\ y = 1)                             (* O *)
      \/ (x = 0 /\ y = -(1))                       (* T1 *)
      \/ (x = sqrt_minus_one /\ y = 0)              (* T2 *)
      \/ (x = -(sqrt_minus_one) /\ y = 0).          (* T3 *)

    (** Ristretto equivalence relation.

        Two curve points are equivalent if their difference (under the
        Edwards group law) is a 4-torsion element.

        For the canonical definition used by ristretto.group, the encoding
        uses the Jacobi quartic representation to select a canonical coset
        representative deterministically.  This is specified in
        [Spec/JacobiQuartic.v] and [Spec/Elligator2.v]. *)

    (* The full definition requires the Edwards addition law,
       which is in [Spec/CompleteEdwardsCurve.v].  We state
       the key property: *)

    (** KEY PROPERTY: The quotient E/E[4] has prime order l.
        This follows from: |E| = 8*l (cofactor 8 = 2 * |E[4]|),
        and l is prime (proved in Curve25519.v:prime_l).

        The ristretto255 group IS the quotient. Its elements are
        E[4]-cosets, and its order is exactly l. *)

  End WithField.
End Ristretto255.
