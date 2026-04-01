(** * Generic algebraic identities for quadratic extensions.

    Proves ring-theoretic identities about the abstract quadratic
    extension operations (from QuadraticExtensionsAbstract.v) that
    hold for any commutative base field.

    These identities are the building blocks of per-curve feval chains.
    Each curve's feval file instantiates these with specific beta/xi
    values and bridges to its pairing spec.

    Key lemmas:
    - [qe_mul_self_alt]       : qe_mul x x has 2ab in imaginary part
    - [qe_sub_sub_eq_sub_add] : (x-y)-z = x-(y+z) componentwise
    - [qe_add_sub_eq_sub_add] : (x-y)+z = (x+z)-y componentwise
    - [qe_mul_comm]           : qe_mul x y = qe_mul y x

    Requires: a stdlib [ring_theory] for the base field. *)

Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.

Section QuadraticFeval.

  Context {F : Type}.
  Variable Fzero Fone : F.
  Variable Fopp : F -> F.
  Variable Finv : F -> F.
  Variable Fadd Fsub Fmul : F -> F -> F.
  Variable Fdiv : F -> F -> F.
  Variable nonresidue : F.

  Hypothesis Frt : ring_theory Fzero Fone Fadd Fmul Fsub Fopp (@eq F).
  Add Ring base_ring : Frt.

  Local Notation QE := (F * F)%type.
  Local Notation qe_add := (qe_add Fadd).
  Local Notation qe_sub := (qe_sub Fsub).
  Local Notation qe_opp := (qe_opp Fopp).
  Local Notation qe_mul := (qe_mul Fadd Fmul nonresidue).

  (* ================================================================ *)
  (* Sub-associativity and grouping (componentwise ring algebra)       *)
  (* ================================================================ *)

  Lemma qe_sub_sub_eq_sub_add : forall x y z : QE,
    qe_sub (qe_sub x y) z = qe_sub x (qe_add y z).
  Proof.
    intros [x0 x1] [y0 y1] [z0 z1].
    unfold QuadraticExtensionsAbstract.qe_sub, QuadraticExtensionsAbstract.qe_add;
      simpl fst; simpl snd.
    f_equal; ring.
  Qed.

  Lemma qe_add_sub_eq_sub_add : forall x y z : QE,
    qe_add (qe_sub x y) z = qe_sub (qe_add x z) y.
  Proof.
    intros [x0 x1] [y0 y1] [z0 z1].
    unfold QuadraticExtensionsAbstract.qe_add, QuadraticExtensionsAbstract.qe_sub;
      simpl fst; simpl snd.
    f_equal; ring.
  Qed.

  (* ================================================================ *)
  (* Multiplication commutativity                                      *)
  (* ================================================================ *)

  Lemma qe_mul_comm : forall x y : QE,
    qe_mul x y = qe_mul y x.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold QuadraticExtensionsAbstract.qe_mul; simpl fst; simpl snd.
    f_equal; ring.
  Qed.

  (* ================================================================ *)
  (* mul(x,x) alternative form (for squaring optimization)             *)
  (* ================================================================ *)

  (** qe_mul x x computes:
        re = Fmul a a + nr * (Fmul b b)
        im = Fmul a b + Fmul b a = 2 * Fmul a b  (by commutativity)

      The bedrock2 squaring function uses this "2ab" form for im,
      and "a² + nr*b²" for re.  This lemma shows qe_mul x x has
      the same form. *)
  Lemma qe_mul_self_alt : forall x : QE,
    qe_mul x x =
    (Fadd (Fmul (fst x) (fst x)) (Fmul nonresidue (Fmul (snd x) (snd x))),
     Fadd (Fmul (fst x) (snd x)) (Fmul (fst x) (snd x))).
  Proof.
    intros [a0 a1].
    unfold QuadraticExtensionsAbstract.qe_mul; simpl fst; simpl snd.
    f_equal; ring.
  Qed.

  (* ================================================================ *)
  (* Karatsuba cross-term: (a+b)² - a² - b² = 2ab                    *)
  (* ================================================================ *)

  Lemma qe_karatsuba_cross_term : forall a b : QE,
    qe_sub (qe_sub (qe_mul (qe_add a b) (qe_add a b))
                    (qe_mul a a))
           (qe_mul b b) =
    qe_add (qe_mul a b) (qe_mul a b).
  Proof.
    intros [a0 a1] [b0 b1].
    unfold QuadraticExtensionsAbstract.qe_mul,
           QuadraticExtensionsAbstract.qe_add,
           QuadraticExtensionsAbstract.qe_sub;
      simpl fst; simpl snd.
    f_equal; ring.
  Qed.

End QuadraticFeval.
