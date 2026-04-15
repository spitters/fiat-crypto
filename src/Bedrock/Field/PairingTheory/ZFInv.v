(** * ZFInv.v — Fermat's LT bridge for [zfp_inv] / [zfp2_inv].

    The Z-level [zfp_inv p x] is implemented as [x^(p-2) mod p] via
    square-and-multiply in [zpow_mod_aux].  For prime [p], this is
    the multiplicative inverse.  Fiat-crypto has the F-level fact in
    [PrimeFieldTheorems.F.inv_nonzero] / [Fq_inv_fermat].  This file
    bridges the two and lifts to Fp2. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Znumtheory.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.PairingTheory.ZModTower.

Local Open Scope Z_scope.

(** ** Step 1.1: [zpow_mod_aux] implements modular exponentiation.

    When [fuel] is at least [Z.log2 exp + 1], [zpow_mod_aux] computes
    [base^exp * acc mod p].  Proof by induction on [fuel]. *)

Section ZPowModAux.
  Context (p : Z) (Hp : 0 < p).

  (* Deferred: proof by induction on fuel + case analysis on parity
     of exp. Standard square-and-multiply correctness. *)
  Lemma zpow_mod_aux_correct : forall (fuel : nat) (base exp acc : Z),
    0 <= exp ->
    (Z.to_nat (Z.log2 exp) + 1 <= fuel)%nat ->
    zpow_mod_aux base exp acc p fuel = ((base ^ exp) * acc) mod p.
  Admitted.

End ZPowModAux.

(** ** Step 1.2: [zfp_inv] is [F.inv] on canonical Z representatives.

    Using [zpow_mod_aux_correct] + [Fq_inv_fermat]. *)

Section ZFpInvRelation.
  Context {q : positive} {prime_q : prime q}.

  (* Deferred: combine zpow_mod_aux_correct with F.pow_of_Z and
     Fq_inv_fermat. *)
  Lemma F_of_Z_zfp_inv : forall (x : Z),
    0 <= x < Z.pos q ->
    x <> 0 ->
    F.of_Z q (zfp_inv (Z.pos q) x) = F.inv (F.of_Z q x).
  Admitted.

End ZFpInvRelation.

(** ** Step 1.3: Left-inverse of [zfp_inv] for nonzero canonical x.

    The core property needed downstream: [zfp_mul (zfp_inv x) x = 1]. *)

Section ZFpInvLeft.
  Context {q : positive} {prime_q : prime q}.

  Lemma zfp_inv_left : forall (x : Z),
    0 < x < Z.pos q ->
    zfp_mul (Z.pos q) (zfp_inv (Z.pos q) x) x = 1.
  Admitted.

End ZFpInvLeft.

(** ** Step 1.4: Fp2 left-inverse. *)

Section ZFp2InvLeft.
  Context {q : positive} {prime_q : prime q}.
  Context {q_3mod4 : Z.pos q mod 4 = 3}.

  (* Fp2 = (a, b) with i^2 = -1; inverse is (a/n, -b/n) where
     n = a^2 + b^2.  For q ≡ 3 mod 4, -1 is a non-residue in F q,
     so a^2 + b^2 != 0 mod q whenever (a, b) != (0, 0). *)
  Lemma zfp2_inv_left : forall (a b : Z),
    0 <= a < Z.pos q -> 0 <= b < Z.pos q ->
    (a, b) <> (0, 0) ->
    zfp2_mul (Z.pos q) (zfp2_inv (Z.pos q) (a, b)) (a, b) = (1, 0).
  Admitted.

End ZFp2InvLeft.
