(** * Generic algebraic identities for cubic extensions.

    Proves ring-theoretic identities about the abstract cubic
    extension operations (from CubicExtensionsAbstract.v) that
    hold for any commutative base field.

    Key lemmas:
    - [ce_mul_self_eq_sqr]       : ce_mul a a = ce_sqr a
    - [ce_karatsuba_cross_term]  : (a+b)²-a²-b² = 2ab at cubic level
    - [ce_sub_sub_eq_sub_add]    : (x-y)-z = x-(y+z) componentwise
    - [ce_add_sub_eq_sub_add]    : (x-y)+z = (x+z)-y componentwise
    - [ce_mul_comm]              : ce_mul x y = ce_mul y x

    Requires: a stdlib [ring_theory] for the base field, and
    a [mul_by_nr_is_mul] hypothesis connecting mul_by_nr to Fmul. *)

Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.

Section CubicFeval.

  Context {F : Type}.
  Variable Fzero Fone : F.
  Variable Fopp : F -> F.
  Variable Finv : F -> F.
  Variable Fadd Fsub Fmul : F -> F -> F.
  Variable Fdiv : F -> F -> F.
  Variable mul_by_nr : F -> F.

  Hypothesis Frt : ring_theory Fzero Fone Fadd Fmul Fsub Fopp (@eq F).
  Add Ring base_ring_ce : Frt.

  (** mul_by_nr distributes as multiplication by a constant.
      This is the key bridge between the mul_by_nr function
      and the algebraic formula.  For Fp6: mul_by_nr x = fp2_mul xi x.

      For ring-level proofs, we only need linearity:
        mul_by_nr (Fadd x y) = Fadd (mul_by_nr x) (mul_by_nr y)
        mul_by_nr (Fsub x y) = Fsub (mul_by_nr x) (mul_by_nr y)
      But the simplest hypothesis is just pointwise equality. *)

  Local Notation CE := (F * F * F)%type.
  Local Notation ce_add := (ce_add Fadd).
  Local Notation ce_sub := (ce_sub Fsub).
  Local Notation ce_opp := (ce_opp Fopp).
  Local Notation ce_mul := (ce_mul Fadd Fsub Fmul mul_by_nr).
  Local Notation ce_sqr := (ce_sqr Fadd Fsub Fmul mul_by_nr).

  (* ================================================================ *)
  (* Sub-associativity and grouping (componentwise)                    *)
  (* ================================================================ *)

  Lemma ce_sub_sub_eq_sub_add : forall x y z : CE,
    ce_sub (ce_sub x y) z = ce_sub x (ce_add y z).
  Proof.
    intros [[x0 x1] x2] [[y0 y1] y2] [[z0 z1] z2].
    unfold CubicExtensionsAbstract.ce_sub, CubicExtensionsAbstract.ce_add,
           CubicExtensionsAbstract.ce_build; simpl fst; simpl snd.
    f_equal; [f_equal |]; ring.
  Qed.

  Lemma ce_add_sub_eq_sub_add : forall x y z : CE,
    ce_add (ce_sub x y) z = ce_sub (ce_add x z) y.
  Proof.
    intros [[x0 x1] x2] [[y0 y1] y2] [[z0 z1] z2].
    unfold CubicExtensionsAbstract.ce_add, CubicExtensionsAbstract.ce_sub,
           CubicExtensionsAbstract.ce_build; simpl fst; simpl snd.
    f_equal; [f_equal |]; ring.
  Qed.

  (* ================================================================ *)
  (* mul(a,a) = sqr(a) identity                                       *)
  (* ================================================================ *)

  (** The Karatsuba multiplication applied to equal arguments produces
      the same result as the Chung-Hasan SQR3 squaring formula.

      Requires mul_by_nr to distribute over addition:
        mul_by_nr(a + b) = mul_by_nr(a) + mul_by_nr(b)
      This is true when mul_by_nr is "multiply by constant nr". *)

  Hypothesis mul_by_nr_add : forall x y,
    mul_by_nr (Fadd x y) = Fadd (mul_by_nr x) (mul_by_nr y).

  Lemma ce_mul_self_eq_sqr : forall a : CE,
    ce_mul a a = ce_sqr a.
  Proof.
    intros [[a0 a1] a2].
    unfold CubicExtensionsAbstract.ce_mul, CubicExtensionsAbstract.ce_sqr,
           CubicExtensionsAbstract.ce_build,
           CubicExtensionsAbstract.ce_c0, CubicExtensionsAbstract.ce_c1,
           CubicExtensionsAbstract.ce_c2;
      simpl fst; simpl snd.
    f_equal; [f_equal |].
    (* c0: a0*a0 + mul_by_nr((a1+a2)(a1+a2) - a1*a1 - a2*a2)
         = a0*a0 + mul_by_nr(2*a1*a2)
         = a0*a0 + mul_by_nr(a1*a2 + a1*a2)
         = a0*a0 + mul_by_nr(a1*a2) + mul_by_nr(a1*a2)  [by linearity]
       vs: s0 + mul_by_nr(s3) = a0*a0 + mul_by_nr(a1*a2 + a1*a2)
       Equal by mul_by_nr_add. *)
    - rewrite !mul_by_nr_add. ring.
    (* c1: (a0+a1)(a0+a1) - a0*a0 - a1*a1 + mul_by_nr(a2*a2)
         = 2*a0*a1 + mul_by_nr(a2*a2)
       vs: s1 + mul_by_nr(s4) = (a0*a1 + a0*a1) + mul_by_nr(a2*a2)
       Equal. *)
    - ring.
    (* c2: (a0+a2)(a0+a2) - a0*a0 - a2*a2 + a1*a1
         = 2*a0*a2 + a1*a1
       vs: s1+s2+s3-s0-s4
         = (a0*a1+a0*a1) + (a0-a1+a2)^2 + (a1*a2+a1*a2) - a0^2 - a2^2
         = ... = 2*a0*a2 + a1^2
       Equal by ring. *)
    - ring.
  Qed.

  (* ================================================================ *)
  (* Karatsuba cross-term at cubic level                               *)
  (* ================================================================ *)

  (** (a+b)² - a² - b² = 2·a·b  using Karatsuba multiplication. *)
  Lemma ce_karatsuba_cross_term : forall a b : CE,
    ce_sub (ce_sub (ce_mul (ce_add a b) (ce_add a b))
                   (ce_mul a a))
           (ce_mul b b) =
    ce_add (ce_mul a b) (ce_mul a b).
  Proof.
    intros [[a0 a1] a2] [[b0 b1] b2].
    unfold CubicExtensionsAbstract.ce_mul,
           CubicExtensionsAbstract.ce_add,
           CubicExtensionsAbstract.ce_sub,
           CubicExtensionsAbstract.ce_build,
           CubicExtensionsAbstract.ce_c0,
           CubicExtensionsAbstract.ce_c1,
           CubicExtensionsAbstract.ce_c2;
      simpl fst; simpl snd.
    f_equal; [f_equal |]; rewrite ?mul_by_nr_add; ring.
  Qed.

  (* ================================================================ *)
  (* Multiplication commutativity at cubic level                       *)
  (* ================================================================ *)

  Lemma ce_mul_comm : forall x y : CE,
    ce_mul x y = ce_mul y x.
  Proof.
    intros [[a0 a1] a2] [[b0 b1] b2].
    unfold CubicExtensionsAbstract.ce_mul,
           CubicExtensionsAbstract.ce_build,
           CubicExtensionsAbstract.ce_c0,
           CubicExtensionsAbstract.ce_c1,
           CubicExtensionsAbstract.ce_c2;
      simpl fst; simpl snd.
    f_equal; [f_equal |]; rewrite ?mul_by_nr_add; ring.
  Qed.

End CubicFeval.
