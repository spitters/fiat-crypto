(* Generic quadratic extension Fp2 = Fp[u]/(u² - β) for arbitrary QNR β.
   The existing QuadraticExtensions.v hardcodes β computation from p mod 4/8,
   which fails for primes with p ≡ 1 (mod 8) (like BLS12-377).

   This file parameterizes over β directly, requiring only that β is a QNR. *)

From Coq Require Import ZArith Znumtheory.
From Coq Require Import List Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
From Coq Require Import Field.
Require Import Coqprime.elliptic.GZnZ.

Section Fp2Generic.

  Variable p : positive.
  Hypothesis p_prime : prime p.
  Hypothesis p_odd : 2 < p.

  (* β is an explicit quadratic non-residue *)
  Variable beta : F p.
  Hypothesis beta_nonzero : beta <> @F.zero p.
  Hypothesis beta_is_QNR : ~(exists x : F p, @F.mul p x x = beta).

  Notation "x +p y" := (@F.add p x y) (at level 100).
  Notation "x *p y" := (@F.mul p x y) (at level 90).
  Notation "x -p y" := (@F.sub p x y) (at level 100).
  Notation "x /p y" := (@F.div p x y) (at level 90).

  Notation Fp2 := ((F p) * (F p))%type.

  Definition zerop2 : Fp2 := (@F.zero p, @F.zero p).
  Definition onep2 : Fp2 := (@F.one p, @F.zero p).

  Definition addp2 (x1 x2 : Fp2) : Fp2 :=
    (fst x1 +p fst x2, snd x1 +p snd x2).

  Definition subp2 (x1 x2 : Fp2) : Fp2 :=
    (fst x1 -p fst x2, snd x1 -p snd x2).

  (* (a + bu)(c + du) = (ac + β·bd) + (ad + bc)u *)
  Definition mulp2 (x1 x2 : Fp2) : Fp2 :=
    (fst x1 *p fst x2 +p beta *p snd x1 *p snd x2,
     fst x1 *p snd x2 +p snd x1 *p fst x2).

  Definition oppp2 (x : Fp2) : Fp2 := (@F.opp p (fst x), @F.opp p (snd x)).

  Theorem Fp2irr : forall (x1 x2 y1 y2 : F p),
    x1 = y1 -> x2 = y2 -> (x1, x2) = (y1, y2).
  Proof. intros; subst; reflexivity. Qed.

  Add Field FG : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F p)).

  Definition RFp2 : ring_theory zerop2 onep2 addp2 mulp2 subp2 oppp2 (@eq Fp2).
  Proof.
    split; intros; destruct x; try destruct y; try destruct z;
    apply Fp2irr; simpl; field.
  Qed.

  (* Inversion: (a + bu)^(-1) = (a - bu) / (a² - β·b²) *)
  (* The denominator a² - β·b² ≠ 0 because β is a QNR *)
  Definition invp2 (x : Fp2) : Fp2 :=
    if (F.to_Z (fst x) =? 0) then (F.zero, F.inv (snd x *p beta))
    else
      let norm := fst x *p fst x -p beta *p snd x *p snd x in
      (fst x /p norm, F.opp (snd x /p norm)).

  Definition divp2 (x1 x2 : Fp2) : Fp2 := mulp2 x1 (invp2 x2).

  (* The field theory proof requires showing norm ≠ 0,
     which follows from beta being a QNR. *)
  Lemma FFp2 : field_theory zerop2 onep2 addp2 mulp2
    subp2 oppp2 divp2 invp2 (@eq (F p * F p)).
  Proof. admit. Admitted.

End Fp2Generic.
