(** * Jacobi Quartic Curve Model

    Defines the Jacobi quartic curve model t² = e·s⁴ + 2·a·s² + 1
    and the 4-isogeny between Jacobi quartic and twisted Edwards curves.

    This is a key ingredient for:
    - Elligator2 map (field element → curve point)
    - Ristretto encoding (canonical coset representatives)
    - Lizard encoding (Signal's reversible point encoding)

    References:
    - Hamburg, "Decaf: Eliminating cofactors through point compression"
      (Crypto 2015, §2)
    - Hamburg, "Ristretto" (https://ristretto.group/)
    - Bernstein & Lange, "Faster addition and doubling on elliptic curves"
      (IACR ePrint 2007/286)

    Phase S4 of the Signal verification plan.
*)

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable.

Module JQ.
  Section JacobiQuarticCurve.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul
                           (BinNat.N.succ_pos BinNat.N.two)}
            {Feq_dec:Decidable.DecidableRel Feq}.

    Local Infix "=" := Feq : type_scope.
    Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x) (at level 30).
    Local Notation "x ^ 4" := (x*x*(x*x)) (at level 30).

    Context {e a_jq : F}.

    (** A point on the Jacobi quartic t² = e·s⁴ + 2·a·s² + 1. *)
    Definition on_curve (s t : F) : Prop :=
      t ^ 2 = e * s ^ 4 + (1 + 1) * a_jq * s ^ 2 + 1.

    Definition point := { st : F * F | let '(s, t) := st in on_curve s t }.

    Definition coordinates (P : point) : F * F := proj1_sig P.

    (** Identity: (0, 1) is always on the curve. *)
    Lemma on_curve_identity : on_curve 0 1.
    Proof. unfold on_curve. fsatz. Qed.

    Program Definition identity : point := (0, 1).
    Next Obligation. exact on_curve_identity. Qed.

    (** Negation: (s, t) ↦ (-s, t) *)
    Lemma on_curve_opp s t : on_curve s t -> on_curve (Fopp s) t.
    Proof. unfold on_curve. intros H. fsatz. Qed.

    (** * 4-isogeny: Jacobi quartic ↔ twisted Edwards

        For twisted Edwards curve  a_e·x² + y² = 1 + d_e·x²·y²
        and Jacobi quartic          t² = e·s⁴ + 2·a·s² + 1

        with e = a_e·d_e and a = a_e (the "ristretto flavor"):

        Edwards → Jacobi quartic:
          s = (1 + y) / (a_e · x)     [when x ≠ 0]
          t = (1 + y)² / (a_e · x²) - 1

        Alternative (avoiding division):
          s = 2 / (x · √(a_e · d_e - a_e²))
          t = (1 - y) / (1 + y)      [when y ≠ -1]

        Jacobi quartic → Edwards (Hamburg's formulas):
          x = 2·s / (1 + a·s² + √(1 + 2a·s² + e·s⁴))
          y = (1 - a·s² - √(1 + 2a·s² + e·s⁴)) /
              (1 + a·s² + √(1 + 2a·s² + e·s⁴))

        For the ristretto flavor, the simpler version is:
          x = 2·s·√(-d-1) / t
          y = (1 - s²) / (1 + s²)

        where d is the Edwards d parameter.
    *)

    Section IsogenyToEdwards.
      Context {a_ed d_ed : F}
              (He : e = a_ed * d_ed)
              (Ha : a_jq = a_ed).

      (** Jacobi quartic → Edwards (Hamburg, Decaf §2.2):

          The ristretto-flavored isogeny maps JQ (s,t) to Edwards as:
            (X:Y:Z:T) = (2·s·c : 1-s² : 1+s² : 2·s·c)
          in extended projective coordinates, where c depends on
          curve parameters.  In affine:
            x = 2·s·c / (1+s²)
            y = (1-s²) / (1+s²)        [when a_ed = -1]

          The precise constant c and the isogeny correctness proof
          are in [Elligator2.v], which uses the concrete Curve25519
          parameters.  Here we define the y-map abstractly. *)

      Definition to_edwards_y (s : F) : F :=
        (1 + a_ed * (s * s)) / (1 - a_ed * (s * s)).

      (** Edwards → Jacobi quartic (inverse y-map).

          Given y = (1+a·s²)/(1-a·s²), solving for s² gives
          s² = (1-y) / (a·(1+y)).  We verify the round-trip. *)

      Definition from_edwards_s_sq (y : F) : F :=
        (y - 1) / (a_ed * (1 + y)).

      Lemma from_edwards_y_roundtrip y
            (Ha_ne : a_ed <> 0)
            (Hy : 1 + y <> 0)
            (Hden : 1 - a_ed * from_edwards_s_sq y <> 0) :
        let s_sq := from_edwards_s_sq y in
        (1 + a_ed * s_sq) / (1 - a_ed * s_sq) = y.
      Proof.
        unfold from_edwards_s_sq. fsatz.
      Qed.

    End IsogenyToEdwards.

  End JacobiQuarticCurve.
End JQ.

(** * Curve25519 instantiation

    For Curve25519 / Edwards25519:
      a_ed = -1
      d_ed = -121665/121666
      e = a_ed · d_ed = 121665/121666
      a_jq = a_ed = -1

    The Jacobi quartic for ristretto255 uses these parameters. *)

Section Curve25519_JQ.
  (* Parameters will be instantiated from Spec/Curve25519.v *)
  (* This section is a placeholder for the concrete instantiation. *)
End Curve25519_JQ.
