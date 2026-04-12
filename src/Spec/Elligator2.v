(** * Elligator2 Map for Curve25519 / ristretto255

    Defines the Elligator2 map (field element → curve point) and its
    inverse (curve point → up to 8 field element preimages) following
    Hamburg's ristretto-flavored variant.

    This is required for:
    - ristretto255 encoding (hash-to-group via Elligator2)
    - Lizard encoding (reversible 16-byte ↔ ristretto point)
    - Signal's UID encoding in zkgroup

    ## References
    - Hamburg, "Decaf: Eliminating cofactors through point compression"
      (Crypto 2015)
    - Bernstein et al., "Elligator: elliptic-curve points indistinguishable
      from uniform random strings" (CCS 2013)
    - de Valence et al., "Ristretto: prime-order elliptic curve groups
      with non-malleable encodings" (ristretto.group)
    - Hamburg, ePrint 2020/1513

    Phase S4 of the Signal verification plan.
*)

Require Import Coq.ZArith.ZArith.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable.

Module Elligator2.
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

    (** Edwards curve parameters: a*x² + y² = 1 + d*x²*y² *)
    Context {a_ed d_ed : F}
            {nonzero_a : a_ed <> 0}
            {a_is_minus_one : a_ed = -(1)}  (* For Curve25519: a = -1 *)
            {nonsquare_d : forall x, x ^ 2 <> d_ed}.

    (** Non-square constant for Elligator2.
        For GF(2^255-19), we use i = √(-1). *)
    Context {nonsquare_const : F}
            {nonsquare_const_nonsquare : forall x, x ^ 2 <> nonsquare_const}.

    (** Square root function: sqrt(x) returns Some r if x is a square
        (with r² = x), None otherwise. *)
    Context {sqrt_fn : F -> option F}
            {sqrt_fn_correct : forall x r, sqrt_fn x = Some r -> r ^ 2 = x}
            {sqrt_fn_complete : forall x r, r ^ 2 = x -> exists r', sqrt_fn x = Some r'}.

    (** InvSqrtI: compute 1/√(x) or 1/√(i·x) if x or i·x is a square.
        For p ≡ 5 (mod 8): r = x^{(p-5)/8}, then check r²·x ∈ {1, -1, i, -i}.
        Returns (is_square, result) where is_square indicates which case. *)
    Context {inv_sqrt_i : F -> (bool * F)}
            {inv_sqrt_i_correct : forall x b r,
                inv_sqrt_i x = (b, r) ->
                if b then r * r * x = 1
                else r * r * (nonsquare_const * x) = 1}.

    (** * Forward Map: field element → Edwards point

        Hamburg's ristretto-flavored Elligator2.
        Input: r0 ∈ GF(p)
        Output: point on twisted Edwards curve (as Jacobi quartic, then convert)

        Algorithm:
          r = nonsquare_const · r0²
          D = -(d_ed · r + 1) · (r + d_ed)
          Ns = (d_ed² - 1) · (r + 1)
          (was_square, s_inv) = InvSqrtI(Ns · D)
          s_inv = |s_inv|   (take positive square root)
          s = s_inv · Ns
          if was_square: s = -s
          c = r   (if was_square: c = -1)
          N = c · s · (r - 1) · (d_ed - 1)² - D
          W = ... (depending on was_square)
          Return Edwards point derived from (s, N, W, D) *)

    (** The forward map is TOTAL: every field element maps to a curve point.
        This is the key property that makes Elligator2 useful for hashing. *)

    Definition elligator2_forward (r0 : F) : F * F :=
      let r := nonsquare_const * r0 * r0 in
      let D := Fopp ((d_ed * r + 1) * (r + d_ed)) in
      let Ns := (d_ed * d_ed - 1) * (r + 1) in
      let '(was_sq, s_inv) := inv_sqrt_i (Ns * D) in
      (* TODO: Complete the algorithm following Hamburg's spec *)
      (* For now, return placeholder *)
      (0, 1). (* identity point *)

    (** * Inverse Map: Edwards point → up to 8 field element preimages

        Given a ristretto255 point P, compute all r0 such that
        elligator2_forward(r0) is in the same ristretto coset as P.

        A ristretto point has 4 coset representatives (E[4]-coset).
        Each Edwards point has up to 2 Jacobi quartic preimages.
        Each Jacobi quartic point has up to 1 Elligator2 preimage.
        Total: up to 4 × 2 = 8 preimage candidates.

        Returns a bitmask (which of the 8 are valid) and the 8 candidates. *)

    Definition elligator2_inverse (x y : F) : list F :=
      (* TODO: implement the 8-case inverse *)
      (* This is the hardest proof obligation: completeness *)
      nil.

    (** Completeness theorem (the key property for Lizard):
        For any r0, r0 appears among the preimages of elligator2_forward(r0). *)
    Theorem elligator2_inverse_complete :
      forall r0,
        let '(x, y) := elligator2_forward r0 in
        In r0 (elligator2_inverse x y).
    Proof.
      (* This is the hardest proof in the Lizard development.
         Requires case analysis over:
         - 4 ristretto coset representatives
         - 2 Jacobi quartic lifts per representative
         - Degenerate cases: s=0, x=0, y=0, y=-1
         Estimated: 3-4 weeks. *)
    Admitted.

  End WithField.
End Elligator2.

(** * Curve25519 Instantiation

    For GF(2^255 - 19):
      a_ed = -1
      d_ed = -121665/121666
      nonsquare_const = √(-1)  (exists since p ≡ 5 mod 8)
      inv_sqrt_i uses the exponentiation x^{(p-5)/8}

    The primality and field axioms come from [Spec/Curve25519.v]. *)
