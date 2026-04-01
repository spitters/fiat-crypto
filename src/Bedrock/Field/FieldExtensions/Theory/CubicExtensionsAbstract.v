(** * Generic cubic extension F[v]/(v³ - nr) for any field F.
    Elements are triples (c0, c1, c2) representing c0 + c1·v + c2·v².

    Parameterized by base field operations and a `mul_by_nonresidue`
    function (multiplication by nr in the base field).

    Used by GenericCubicSpecs.v to build FieldParameters/FieldRepresentation
    for arbitrary base fields (Fp2→Fp6, Fp8→Fp24, etc.). *)

Section CubicExtAbstract.
  Context {F : Type}.
  Variable Fzero Fone : F.
  Variable Fopp : F -> F.
  Variable Finv : F -> F.
  Variable Fadd Fsub Fmul : F -> F -> F.
  Variable Fdiv : F -> F -> F.

  (** mul_by_nr(x) = nr · x in the base field.
      For Fp6 = Fp2[v]/(v³ - ξ), this is fp2_mul_xi. *)
  Variable mul_by_nr : F -> F.

  Local Notation CE := (F * F * F)%type.

  (* Projections — note (F * F * F) = ((F * F) * F). *)
  Definition ce_c0 (x : CE) : F := fst (fst x).
  Definition ce_c1 (x : CE) : F := snd (fst x).
  Definition ce_c2 (x : CE) : F := snd x.
  Definition ce_build (c0 c1 c2 : F) : CE := ((c0, c1), c2).

  Definition ce_zero : CE := ce_build Fzero Fzero Fzero.
  Definition ce_one  : CE := ce_build Fone Fzero Fzero.

  Definition ce_add (a b : CE) : CE :=
    ce_build (Fadd (ce_c0 a) (ce_c0 b))
             (Fadd (ce_c1 a) (ce_c1 b))
             (Fadd (ce_c2 a) (ce_c2 b)).

  Definition ce_sub (a b : CE) : CE :=
    ce_build (Fsub (ce_c0 a) (ce_c0 b))
             (Fsub (ce_c1 a) (ce_c1 b))
             (Fsub (ce_c2 a) (ce_c2 b)).

  Definition ce_opp (a : CE) : CE :=
    ce_build (Fopp (ce_c0 a)) (Fopp (ce_c1 a)) (Fopp (ce_c2 a)).

  (** Multiply by v in the extension: v·(c0 + c1·v + c2·v²) = nr·c2 + c0·v + c1·v². *)
  Definition ce_mul_by_v (a : CE) : CE :=
    ce_build (mul_by_nr (ce_c2 a)) (ce_c0 a) (ce_c1 a).

  (** Cubic extension multiplication (Karatsuba-like).
      c0 = a0·b0 + nr·((a1+a2)(b1+b2) - a1·b1 - a2·b2)
      c1 = (a0+a1)(b0+b1) - a0·b0 - a1·b1 + nr·(a2·b2)
      c2 = (a0+a2)(b0+b2) - a0·b0 - a2·b2 + a1·b1 *)
  Definition ce_mul (a b : CE) : CE :=
    let a0 := ce_c0 a in let a1 := ce_c1 a in let a2 := ce_c2 a in
    let b0 := ce_c0 b in let b1 := ce_c1 b in let b2 := ce_c2 b in
    let a0b0 := Fmul a0 b0 in
    let a1b1 := Fmul a1 b1 in
    let a2b2 := Fmul a2 b2 in
    let t0 := Fsub (Fsub (Fmul (Fadd a1 a2) (Fadd b1 b2)) a1b1) a2b2 in
    let c0 := Fadd a0b0 (mul_by_nr t0) in
    let t1 := Fsub (Fsub (Fmul (Fadd a0 a1) (Fadd b0 b1)) a0b0) a1b1 in
    let c1 := Fadd t1 (mul_by_nr a2b2) in
    let t2 := Fsub (Fsub (Fmul (Fadd a0 a2) (Fadd b0 b2)) a0b0) a2b2 in
    let c2 := Fadd t2 a1b1 in
    ce_build c0 c1 c2.

  (** Cubic extension squaring (Chung-Hasan SQR3).
      s0 = a0²,  s1 = 2·a0·a1,  s2 = (a0-a1+a2)²,
      s3 = 2·a1·a2,  s4 = a2²
      c0 = s0 + nr·s3,  c1 = s1 + nr·s4,
      c2 = s1 + s2 + s3 - s0 - s4 *)
  Definition ce_sqr (a : CE) : CE :=
    let a0 := ce_c0 a in let a1 := ce_c1 a in let a2 := ce_c2 a in
    let s0 := Fmul a0 a0 in
    let ab := Fmul a0 a1 in
    let s1 := Fadd ab ab in
    let s2 := Fmul (Fadd (Fsub a0 a1) a2) (Fadd (Fsub a0 a1) a2) in
    let bc := Fmul a1 a2 in
    let s3 := Fadd bc bc in
    let s4 := Fmul a2 a2 in
    let c0 := Fadd s0 (mul_by_nr s3) in
    let c1 := Fadd s1 (mul_by_nr s4) in
    let c2 := Fsub (Fsub (Fadd (Fadd s1 s2) s3) s0) s4 in
    ce_build c0 c1 c2.

  (** Cubic extension inverse.
      A = a0² - nr·(a1·a2)
      B = nr·(a2²) - a0·a1
      C = a1² - a0·a2
      FF = a0·A + nr·(a2·B + a1·C)
      result = (A/FF, B/FF, C/FF) *)
  Definition ce_inv (a : CE) : CE :=
    let a0 := ce_c0 a in let a1 := ce_c1 a in let a2 := ce_c2 a in
    let c0_sq := Fmul a0 a0 in
    let c1_sq := Fmul a1 a1 in
    let c2_sq := Fmul a2 a2 in
    let c0c1  := Fmul a0 a1 in
    let c0c2  := Fmul a0 a2 in
    let c1c2  := Fmul a1 a2 in
    let A := Fsub c0_sq (mul_by_nr c1c2) in
    let B := Fsub (mul_by_nr c2_sq) c0c1 in
    let C := Fsub c1_sq c0c2 in
    let FF := Fadd (Fmul a0 A) (mul_by_nr (Fadd (Fmul a2 B) (Fmul a1 C))) in
    let FF_inv := Finv FF in
    ce_build (Fmul A FF_inv) (Fmul B FF_inv) (Fmul C FF_inv).

  Definition ce_div (a b : CE) : CE := ce_mul a (ce_inv b).

  (** Decidable Leibniz equality from base field decidable equality. *)
  Hypothesis eq_dec_F : forall x y : F, {x = y} + {x <> y}.

  Lemma eq_dec_CE : forall x y : CE, {x = y} + {x <> y}.
  Proof.
    intros [[a0 a1] a2] [[b0 b1] b2].
    destruct (eq_dec_F a0 b0); [|right; intro H; inversion H; contradiction].
    destruct (eq_dec_F a1 b1); [|right; intro H; inversion H; contradiction].
    destruct (eq_dec_F a2 b2); [|right; intro H; inversion H; contradiction].
    left; subst; reflexivity.
  Defined.

End CubicExtAbstract.

Arguments ce_c0 {F}.
Arguments ce_c1 {F}.
Arguments ce_c2 {F}.
Arguments ce_build {F}.
Arguments ce_zero {F} Fzero.
Arguments ce_one  {F} Fone Fzero.
Arguments ce_add  {F} Fadd.
Arguments ce_sub  {F} Fsub.
Arguments ce_opp  {F} Fopp.
Arguments ce_mul_by_v {F} mul_by_nr.
Arguments ce_mul  {F} Fadd Fsub Fmul mul_by_nr.
Arguments ce_sqr  {F} Fadd Fsub Fmul mul_by_nr.
Arguments ce_inv  {F} Fadd Fsub Fmul Finv mul_by_nr.
Arguments ce_div  {F} Fadd Fsub Fmul Finv mul_by_nr.
Arguments eq_dec_CE {F} eq_dec_F.
