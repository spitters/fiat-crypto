(* Fp12 = Fp6[w]/(w^2 - v) arithmetic for BLS12-381 pairing.
 *
 * This file is self-contained: it includes Fp2, Fp6, and Fp12 definitions
 * to avoid complications with Rocq Section variable export.
 *
 * Tower of extensions:
 *   Fp2 = Fp[u]/(u^2 + 1)
 *   Fp6 = Fp2[v]/(v^3 - xi)   where xi = 1 + u
 *   Fp12 = Fp6[w]/(w^2 - v)
 *
 * Reference: hax BLS12-381 specification and Algorithm 5.16/5.17
 * from "Guide to Pairing-Based Cryptography".
 *)

From Stdlib Require Import ZArith BinPos List.
Require Import Crypto.Spec.ModularArithmetic.

Import ListNotations.

Section BLS12_Fp12.
  Variable p : positive.

  (* ================================================================== *)
  (* Fp2 = Fp[u]/(u^2 + 1)                                             *)
  (* Duplicated from Fp6.v for self-containment.                        *)
  (* ================================================================== *)

  Notation F := (F p).
  Notation Fp2 := (F * F)%type.

  Definition fp2_zero : Fp2 := (@F.zero p, @F.zero p).
  Definition fp2_one  : Fp2 := (@F.one p, @F.zero p).

  Definition fp2_add (a b : Fp2) : Fp2 :=
    (F.add (fst a) (fst b), F.add (snd a) (snd b)).

  Definition fp2_sub (a b : Fp2) : Fp2 :=
    (F.sub (fst a) (fst b), F.sub (snd a) (snd b)).

  Definition fp2_neg (a : Fp2) : Fp2 :=
    (F.opp (fst a), F.opp (snd a)).

  (* (a0 + a1*u)(b0 + b1*u) = (a0*b0 - a1*b1) + (a0*b1 + a1*b0)*u *)
  Definition fp2_mul (a b : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    let b0 := fst b in let b1 := snd b in
    let v0 := F.mul a0 b0 in
    let v1 := F.mul a1 b1 in
    (F.sub v0 v1,
     F.sub (F.mul (F.add a0 a1) (F.add b0 b1)) (F.add v0 v1)).

  (* (a0 + a1*u)^2 = (a0^2 - a1^2) + 2*a0*a1*u *)
  Definition fp2_sqr (a : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    let v0 := F.mul a0 a1 in
    (F.sub (F.mul (F.add a0 a1) (F.sub a0 a1)) (@F.zero p),
     F.add v0 v0).

  (* Norm: a0^2 + a1^2 (since u^2 = -1) *)
  Definition fp2_inv (a : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    let norm := F.add (F.mul a0 a0) (F.mul a1 a1) in
    let inv_norm := F.inv norm in
    (F.mul a0 inv_norm, F.opp (F.mul a1 inv_norm)).

  (* Frobenius on Fp2: conjugation (a0 + a1*u) -> (a0 - a1*u) *)
  Definition fp2_conjugate (a : Fp2) : Fp2 :=
    (fst a, F.opp (snd a)).

  (* Multiply by xi = 1 + u in Fp2:
     (a0 + a1*u)(1 + u) = (a0 - a1) + (a0 + a1)*u *)
  Definition fp2_mul_xi (a : Fp2) : Fp2 :=
    (F.sub (fst a) (snd a), F.add (fst a) (snd a)).

  (* Scalar multiplication: Fp2 * Fp -> Fp2 *)
  Definition fp2_mul_fp (a : Fp2) (s : F) : Fp2 :=
    (F.mul (fst a) s, F.mul (snd a) s).

  (* ================================================================== *)
  (* Fp6 = Fp2[v]/(v^3 - xi)  where xi = 1 + u                        *)
  (* Elements: c0 + c1*v + c2*v^2  stored as ((c0, c1), c2)            *)
  (* Duplicated from Fp6.v for self-containment.                        *)
  (* ================================================================== *)

  Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.

  Definition fp6_c0 (x : Fp6) : Fp2 := fst (fst x).
  Definition fp6_c1 (x : Fp6) : Fp2 := snd (fst x).
  Definition fp6_c2 (x : Fp6) : Fp2 := snd x.
  Definition mk_fp6 (c0 c1 c2 : Fp2) : Fp6 := ((c0, c1), c2).

  Definition fp6_zero : Fp6 := mk_fp6 fp2_zero fp2_zero fp2_zero.
  Definition fp6_one  : Fp6 := mk_fp6 fp2_one fp2_zero fp2_zero.

  Definition fp6_add (a b : Fp6) : Fp6 :=
    mk_fp6 (fp2_add (fp6_c0 a) (fp6_c0 b))
            (fp2_add (fp6_c1 a) (fp6_c1 b))
            (fp2_add (fp6_c2 a) (fp6_c2 b)).

  Definition fp6_sub (a b : Fp6) : Fp6 :=
    mk_fp6 (fp2_sub (fp6_c0 a) (fp6_c0 b))
            (fp2_sub (fp6_c1 a) (fp6_c1 b))
            (fp2_sub (fp6_c2 a) (fp6_c2 b)).

  Definition fp6_neg (a : Fp6) : Fp6 :=
    mk_fp6 (fp2_neg (fp6_c0 a))
            (fp2_neg (fp6_c1 a))
            (fp2_neg (fp6_c2 a)).

  (* Multiply by v: shift coefficients and use v^3 = xi.
     v * (c0 + c1*v + c2*v^2) = xi*c2 + c0*v + c1*v^2 *)
  Definition fp6_mul_by_v (a : Fp6) : Fp6 :=
    mk_fp6 (fp2_mul_xi (fp6_c2 a))
            (fp6_c0 a)
            (fp6_c1 a).

  (* Fp6 multiplication using schoolbook with v^3 = xi reduction.
     (a0 + a1*v + a2*v^2)(b0 + b1*v + b2*v^2):
       v0 = a0*b0, v1 = a1*b1, v2 = a2*b2
       c0 = v0 + xi*((a1+a2)(b1+b2) - v1 - v2)
       c1 = (a0+a1)(b0+b1) - v0 - v1 + xi*v2
       c2 = (a0+a2)(b0+b2) - v0 + v1 - v2 *)
  Definition fp6_mul (a b : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let b0 := fp6_c0 b in let b1 := fp6_c1 b in let b2 := fp6_c2 b in
    let v0 := fp2_mul a0 b0 in
    let v1 := fp2_mul a1 b1 in
    let v2 := fp2_mul a2 b2 in
    let c0 := fp2_add v0
                (fp2_mul_xi (fp2_sub (fp2_sub (fp2_mul (fp2_add a1 a2)
                                                        (fp2_add b1 b2))
                                               v1) v2)) in
    let c1 := fp2_add (fp2_sub (fp2_sub (fp2_mul (fp2_add a0 a1)
                                                   (fp2_add b0 b1))
                                         v0) v1)
                       (fp2_mul_xi v2) in
    let c2 := fp2_add (fp2_sub (fp2_sub (fp2_mul (fp2_add a0 a2)
                                                   (fp2_add b0 b2))
                                         v0) v2) v1 in
    mk_fp6 c0 c1 c2.

  (* Fp6 squaring (Chung-Hasan SQ2 or simple expansion):
     s0 = a0^2, s1 = 2*a0*a1, s2 = (a0 - a1 + a2)^2
     s3 = 2*a1*a2, s4 = a2^2
     c0 = s0 + xi*s3
     c1 = s1 + xi*s4
     c2 = s1 + s2 + s3 - s0 - s4 *)
  Definition fp6_sqr (a : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let s0 := fp2_sqr a0 in
    let ab := fp2_mul a0 a1 in
    let s1 := fp2_add ab ab in
    let s2 := fp2_sqr (fp2_add (fp2_sub a0 a1) a2) in
    let bc := fp2_mul a1 a2 in
    let s3 := fp2_add bc bc in
    let s4 := fp2_sqr a2 in
    let c0 := fp2_add s0 (fp2_mul_xi s3) in
    let c1 := fp2_add s1 (fp2_mul_xi s4) in
    let c2 := fp2_sub (fp2_add (fp2_add s1 s2) s3) (fp2_add s0 s4) in
    mk_fp6 c0 c1 c2.

  (* Fp6 scalar multiplication by an Fp2 element *)
  Definition fp6_mul_fp2 (a : Fp6) (s : Fp2) : Fp6 :=
    mk_fp6 (fp2_mul (fp6_c0 a) s)
            (fp2_mul (fp6_c1 a) s)
            (fp2_mul (fp6_c2 a) s).

  (* Fp6 inverse using the formula for cubic extensions:
     Given a = a0 + a1*v + a2*v^2, the inverse uses:
       t0 = a0^2 - xi*a1*a2
       t1 = xi*a2^2 - a0*a1
       t2 = a1^2 - a0*a2
       factor = 1/(a0*t0 + xi*(a2*t1 + a1*t2))
       inv = (t0*factor, t1*factor, t2*factor) *)
  Definition fp6_inv (a : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let t0 := fp2_sub (fp2_sqr a0) (fp2_mul_xi (fp2_mul a1 a2)) in
    let t1 := fp2_sub (fp2_mul_xi (fp2_sqr a2)) (fp2_mul a0 a1) in
    let t2 := fp2_sub (fp2_sqr a1) (fp2_mul a0 a2) in
    let factor := fp2_inv (fp2_add (fp2_mul a0 t0)
                            (fp2_mul_xi (fp2_add (fp2_mul a2 t1)
                                                  (fp2_mul a1 t2)))) in
    mk_fp6 (fp2_mul t0 factor)
            (fp2_mul t1 factor)
            (fp2_mul t2 factor).

  (* Frobenius constants for Fp6 and Fp12.
     These are declared as Variables to be instantiated for BLS12-381.
     After section close they become extra parameters. *)

  (* gamma_1 = xi^{(p-1)/3}, gamma_2 = xi^{2(p-1)/3} *)
  Variable frobenius_gamma1 : Fp2.
  Variable frobenius_gamma2 : Fp2.
  (* gamma_1^{p} = xi^{p(p-1)/3}, gamma_2^{p} = xi^{2p(p-1)/3} -- for p^2 Frobenius *)
  Variable frobenius_gamma1_p2 : Fp2.
  Variable frobenius_gamma2_p2 : Fp2.

  (* Fp6 Frobenius: phi_p(a0 + a1*v + a2*v^2) =
       conj(a0) + conj(a1)*gamma1*v + conj(a2)*gamma2*v^2 *)
  Definition fp6_frobenius (a : Fp6) : Fp6 :=
    mk_fp6 (fp2_conjugate (fp6_c0 a))
            (fp2_mul (fp2_conjugate (fp6_c1 a)) frobenius_gamma1)
            (fp2_mul (fp2_conjugate (fp6_c2 a)) frobenius_gamma2).

  (* Fp6 Frobenius p^2: phi_{p^2}(a0 + a1*v + a2*v^2) =
       a0 + a1*gamma1_p2*v + a2*gamma2_p2*v^2
     (No conjugation since p^2 ~ 1 mod 2 on Fp2) *)
  Definition fp6_frobenius_p2 (a : Fp6) : Fp6 :=
    mk_fp6 (fp6_c0 a)
            (fp2_mul (fp6_c1 a) frobenius_gamma1_p2)
            (fp2_mul (fp6_c2 a) frobenius_gamma2_p2).

  (* ================================================================== *)
  (* Fp12 = Fp6[w]/(w^2 - v)                                           *)
  (* Elements: c0 + c1*w  stored as (c0, c1)                           *)
  (* Key relation: w^2 = v (the "v" element of Fp6)                    *)
  (* ================================================================== *)

  Notation Fp12 := (Fp6 * Fp6)%type.

  Definition fp12_c0 (x : Fp12) : Fp6 := fst x.
  Definition fp12_c1 (x : Fp12) : Fp6 := snd x.
  Definition mk_fp12 (c0 c1 : Fp6) : Fp12 := (c0, c1).

  Definition fp12_zero : Fp12 := mk_fp12 fp6_zero fp6_zero.
  Definition fp12_one  : Fp12 := mk_fp12 fp6_one fp6_zero.

  Definition fp12_add (a b : Fp12) : Fp12 :=
    mk_fp12 (fp6_add (fp12_c0 a) (fp12_c0 b))
             (fp6_add (fp12_c1 a) (fp12_c1 b)).

  Definition fp12_sub (a b : Fp12) : Fp12 :=
    mk_fp12 (fp6_sub (fp12_c0 a) (fp12_c0 b))
             (fp6_sub (fp12_c1 a) (fp12_c1 b)).

  Definition fp12_neg (a : Fp12) : Fp12 :=
    mk_fp12 (fp6_neg (fp12_c0 a))
             (fp6_neg (fp12_c1 a)).

  (* Fp12 multiplication:
     (a0 + a1*w)(b0 + b1*w) = (a0*b0 + a1*b1*v) + (a0*b1 + a1*b0)*w
     Using Karatsuba:
       v0 = a0*b0, v1 = a1*b1
       c0 = v0 + mul_by_v(v1)       -- since w^2 = v
       c1 = (a0+a1)(b0+b1) - v0 - v1 *)
  Definition fp12_mul (a b : Fp12) : Fp12 :=
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let b0 := fp12_c0 b in let b1 := fp12_c1 b in
    let v0 := fp6_mul a0 b0 in
    let v1 := fp6_mul a1 b1 in
    let c0 := fp6_add v0 (fp6_mul_by_v v1) in
    let c1 := fp6_sub (fp6_sub (fp6_mul (fp6_add a0 a1)
                                         (fp6_add b0 b1))
                                v0) v1 in
    mk_fp12 c0 c1.

  (* Fp12 squaring:
     (a0 + a1*w)^2 = (a0^2 + a1^2*v) + 2*a0*a1*w
       c0 = a0^2 + mul_by_v(a1^2)
       c1 = 2*a0*a1 *)
  Definition fp12_sqr (a : Fp12) : Fp12 :=
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let a0_sq := fp6_sqr a0 in
    let a1_sq := fp6_sqr a1 in
    let cross := fp6_mul a0 a1 in
    let c0 := fp6_add a0_sq (fp6_mul_by_v a1_sq) in
    let c1 := fp6_add cross cross in
    mk_fp12 c0 c1.

  (* Unitary inverse / conjugation in Fp12:
     For elements on the cyclotomic subgroup (norm 1),
     the inverse is simply the conjugate: (a0, -a1).
     This is the map w -> -w, i.e., the automorphism of Fp12/Fp6. *)
  Definition fp12_conjugate (a : Fp12) : Fp12 :=
    mk_fp12 (fp12_c0 a) (fp6_neg (fp12_c1 a)).

  (* Full Fp12 inverse using the norm form:
     inv(a0 + a1*w) where norm = a0^2 - v*a1^2
       norm_inv = fp6_inv(norm)
       result = (a0 * norm_inv, -a1 * norm_inv) *)
  Definition fp12_inv (a : Fp12) : Fp12 :=
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let norm := fp6_sub (fp6_sqr a0) (fp6_mul_by_v (fp6_sqr a1)) in
    let norm_inv := fp6_inv norm in
    mk_fp12 (fp6_mul a0 norm_inv)
             (fp6_neg (fp6_mul a1 norm_inv)).

  (* ================================================================== *)
  (* Frobenius endomorphisms on Fp12                                    *)
  (* ================================================================== *)

  (* Frobenius constants for the w-coefficient.
     w^p     = w * xi^{(p-1)/6}
     w^{p^2} = w * xi^{(p^2-1)/6}
     w^{p^3} = w * xi^{(p^3-1)/6}  *)
  Variable w_frobenius_c1     : Fp2.  (* xi^{(p-1)/6}   *)
  Variable w_frobenius_p2_c1  : Fp2.  (* xi^{(p^2-1)/6} *)
  Variable w_frobenius_p3_c1  : Fp2.  (* xi^{(p^3-1)/6} *)

  (* phi_p on Fp12:
     phi_p(a0 + a1*w) = phi_p(a0) + phi_p(a1) * w^p
                       = fp6_frobenius(a0) + fp6_frobenius(a1) * xi^{(p-1)/6} * w *)
  Definition fp12_frobenius (a : Fp12) : Fp12 :=
    let c0' := fp6_frobenius (fp12_c0 a) in
    let c1' := fp6_mul_fp2 (fp6_frobenius (fp12_c1 a)) w_frobenius_c1 in
    mk_fp12 c0' c1'.

  (* phi_{p^2} on Fp12:
     phi_{p^2}(a0 + a1*w) = fp6_frobenius_p2(a0)
                            + fp6_frobenius_p2(a1) * xi^{(p^2-1)/6} * w *)
  Definition fp12_frobenius_p2 (a : Fp12) : Fp12 :=
    let c0' := fp6_frobenius_p2 (fp12_c0 a) in
    let c1' := fp6_mul_fp2 (fp6_frobenius_p2 (fp12_c1 a)) w_frobenius_p2_c1 in
    mk_fp12 c0' c1'.

  (* phi_{p^3} on Fp12:
     phi_{p^3} = phi_p o phi_{p^2}
     phi_{p^3}(a0 + a1*w) = fp6_frobenius(fp6_frobenius_p2(a0))
                            + fp6_frobenius(fp6_frobenius_p2(a1)) * xi^{(p^3-1)/6} * w *)
  Definition fp12_frobenius_p3 (a : Fp12) : Fp12 :=
    let c0' := fp6_frobenius (fp6_frobenius_p2 (fp12_c0 a)) in
    let c1' := fp6_mul_fp2 (fp6_frobenius (fp6_frobenius_p2 (fp12_c1 a)))
                            w_frobenius_p3_c1 in
    mk_fp12 c0' c1'.

  (* ================================================================== *)
  (* Exponentiation                                                     *)
  (* ================================================================== *)

  (* General exponentiation by nat using binary method (left-to-right).
     Uses the positive binary representation for efficiency. *)
  Fixpoint fp12_pow_pos (base : Fp12) (e : positive) : Fp12 :=
    match e with
    | xH => base
    | xO e' => fp12_sqr (fp12_pow_pos base e')
    | xI e' => fp12_mul base (fp12_sqr (fp12_pow_pos base e'))
    end.

  Definition fp12_pow_nat (base : Fp12) (n : nat) : Fp12 :=
    match n with
    | O => fp12_one
    | S _ => fp12_pow_pos base (Pos.of_nat n)
    end.

  Definition fp12_pow_N (base : Fp12) (n : N) : Fp12 :=
    match n with
    | N0 => fp12_one
    | Npos e => fp12_pow_pos base e
    end.

  Definition fp12_pow_Z (base : Fp12) (z : Z) : Fp12 :=
    match z with
    | Z0 => fp12_one
    | Zpos e => fp12_pow_pos base e
    | Zneg e => fp12_inv (fp12_pow_pos base e)
    end.

  (* ================================================================== *)
  (* BLS12-381 parameter and power-by-x                                 *)
  (* ================================================================== *)

  (* The BLS12-381 curve parameter |x| (absolute value).
     x = -0xd201000000010000, so |x| = 0xd201000000010000.
     Binary: 1101_0010_0000_0001_0000_0000_0000_0000_0000_0000_0000_0001_0000_0000_0000_0000 *)
  Definition bls_x : Z := 0xd201000000010000.

  (* The BLS parameter as a positive number for direct use. *)
  Definition bls_x_pos : positive := 0xd201000000010000%positive.

  (* Compute a^|x| where x is the BLS12-381 parameter.
     This is used extensively in the final exponentiation.
     Since the actual BLS parameter x is negative, the caller should
     conjugate the result: a^x = conjugate(a^|x|). *)
  Definition fp12_pow_bls_x (a : Fp12) : Fp12 :=
    fp12_pow_pos a bls_x_pos.

  (* Convenience: compute a^x accounting for the sign.
     The BLS12-381 parameter x is negative, so:
       a^x = (a^|x|)^{-1} = conjugate(a^|x|)
     (The conjugate equals the inverse for elements of norm 1,
      which is always the case after the easy part of final exp.) *)
  Definition fp12_pow_bls_x_signed (a : Fp12) : Fp12 :=
    fp12_conjugate (fp12_pow_bls_x a).

  (* ================================================================== *)
  (* Cyclotomic squaring (optimization for elements with norm 1)        *)
  (* In the cyclotomic subgroup, a^{-1} = conjugate(a), so             *)
  (* a*conjugate(a) = 1. This allows a faster squaring formula.        *)
  (* ================================================================== *)

  (* For an element f = (a0, a1) in the cyclotomic subgroup of Fp12:
     f^2 can be computed more efficiently using the Granger-Scott method.
     We decompose each Fp6 component into its three Fp2 sub-components
     and exploit the constraint a0^2 + v*a1^2 = 1. *)

  (* Extract Fp2 components from an Fp12 element:
     If f = (g0, g1) where g0 = ((a,b),c) and g1 = ((d,e),f_),
     the six Fp2 components are a, b, c, d, e, f_. *)

  Definition fp12_cyclotomic_sqr (f : Fp12) : Fp12 :=
    let g0 := fp12_c0 f in
    let g1 := fp12_c1 f in
    let a := fp6_c0 g0 in let b := fp6_c1 g0 in let c := fp6_c2 g0 in
    let d := fp6_c0 g1 in let e := fp6_c1 g1 in let f_ := fp6_c2 g1 in
    (* Compute pairs using Fp2 squaring *)
    (* A = a^2, B = b^2 (not used directly -- we use the Karabina/GS approach) *)
    (* Simpler approach: just use the quadratic formula *)
    (* (a + d*w)^2 in Fp2[w]/(w^2 - v_coeff) ... *)
    (* For simplicity and correctness, fall back to standard squaring.
       A dedicated cyclotomic squaring can be added as an optimization. *)
    fp12_sqr f.

  (* ================================================================== *)
  (* Sparse multiplication (for pairing line functions)                 *)
  (* ================================================================== *)

  (* Multiply an Fp12 element by a "sparse" Fp12 element arising from
     a line evaluation in the pairing. A typical line function produces
     an element of the form (c0, c1) where c0 and c1 have specific
     zero patterns depending on twist type.

     For a D-twist (BLS12-381 uses M-twist, but the structure is similar):
     The line function gives an Fp12 element where only certain Fp2
     coefficients are nonzero. Specialized multiplication can skip
     multiplications by zero.

     For BLS12-381 (M-twist), line evaluation gives:
       ell = ((0, ell_vv, 0), (ell_vw, 0, 0)) in terms of Fp2 components
     i.e., c0 = mk_fp6 0 ell_vv 0, c1 = mk_fp6 ell_vw 0 0

     We provide a general sparse multiply for this pattern. *)

  Definition fp12_mul_by_024 (a : Fp12) (ell0 ell2 ell4 : Fp2) : Fp12 :=
    (* ell represents the sparse element:
       c0 = mk_fp6 ell0 ell2 0
       c1 = mk_fp6 ell4 0 0
       This is the "024" sparse form used in BLS12 optimal ate pairing. *)
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let b := mk_fp6 ell0 ell2 fp2_zero in
    let b1_c0 := ell4 in
    (* Full computation:
       result_c0 = a0 * b + mul_by_v(a1 * (ell4, 0, 0))
       result_c1 = a1 * b + a0 * (ell4, 0, 0)
       But a1 * (ell4,0,0) simplifies since c1=c2=0:
         (x0,x1,x2) * (ell4,0,0) = (x0*ell4, x1*ell4, x2*ell4)
       Wait -- that's fp6_mul_fp2 with ell4! No, fp6_mul is more complex.
       Actually (x0+x1*v+x2*v^2)*(ell4) = x0*ell4 + x1*ell4*v + x2*ell4*v^2
       which IS fp6_mul_fp2. *)
    let t0 := fp6_mul a0 b in
    let t1 := fp6_mul_fp2 a1 b1_c0 in
    let c0 := fp6_add t0 (fp6_mul_by_v t1) in
    (* For c1: a1*b + a0*(ell4,0,0) *)
    let t2 := fp6_mul a1 b in
    let t3 := fp6_mul_fp2 a0 b1_c0 in
    let c1 := fp6_add t2 t3 in
    mk_fp12 c0 c1.

End BLS12_Fp12.
