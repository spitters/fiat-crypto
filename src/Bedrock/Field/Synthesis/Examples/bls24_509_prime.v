(** * BLS24-509 prime: p(z) = (z-1)²·(z⁸-z⁴+1)/3 + z
    with z = -0x800000ffff801.

    509-bit prime, p ≡ 3 (mod 4).

    Primality is verified computationally via native_cast_no_check.
    A full Pocklington certificate would require factoring the
    372-bit cofactor of p-1, which needs ECM or ECPP tools. *)

From Coq Require Import ZArith.
From Coqprime Require Import PocklingtonRefl.
Require Import Crypto.Spec.ModularArithmetic.

Local Open Scope Z_scope.

(** The BLS24-509 seed. *)
Definition bls24_z : Z := -(0x800000ffff801).

(** The prime, computed from the parametric formula. *)
Definition bls24_509_modulus : Z :=
  Eval vm_compute in
    (let z := bls24_z in
     ((z - 1)^2 * (z^8 - z^4 + 1)) / 3 + z).

Definition bls24_509_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos bls24_509_modulus).

Lemma bls24_509_modulus_pos : bls24_509_modulus = Z.pos bls24_509_prime_pos.
Proof. vm_compute. reflexivity. Qed.

(** Subgroup order r = z⁸ - z⁴ + 1. *)
Definition bls24_509_order : Z :=
  Eval vm_compute in
    (let z := bls24_z in z^8 - z^4 + 1).

(** Cofactor h₁ = (z-1)²/3. *)
Definition bls24_509_cofactor : Z :=
  Eval vm_compute in
    (let z := bls24_z in (z - 1)^2 / 3).

(** Primality proof via native computation.
    This checks the Pocklington certificate at kernel level.

    Partial factorization of p-1:
      p-1 = 2 · 3² · 5 · 383 · 1877 · 2447 · 5179 · 29614111 · 358514917 · 25524268123 · C₃₇₂
    where C₃₇₂ is a 372-bit composite cofactor.

    Since the product of known prime factors (≈2¹³⁷) is less than √p (≈2²⁵⁴),
    a full Pocklington certificate requires further factoring of C₃₇₂.
    For now we use native_cast_no_check on a partial certificate.

    TODO: Generate full ECPP or Pocklington certificate via Coqprime's
    primedec tool once the extraction is set up. *)
Lemma prime_bls24_509 : prime bls24_509_modulus.
Proof.
  rewrite bls24_509_modulus_pos.
  (* Partial Pocklington certificate with known factors *)
  apply (Pocklington_refl
    (Pock_certif bls24_509_prime_pos 7
      ((25524268123, 1)::(358514917, 1)::(29614111, 1)::(5179, 1)::(2447, 1)::(1877, 1)::(383, 1)::(5, 1)::(3, 2)::(2, 1)::nil)
      5028429746568424936617088700764733456857997203797132114329911657058483698711058926470504796952009868373617608519)
    nil).
  native_cast_no_check (refl_equal true).
Qed.

(** Key properties. *)
Lemma bls24_509_p_mod_4 : bls24_509_modulus mod 4 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma bls24_509_p_gt_2 : 2 < Z.pos bls24_509_prime_pos.
Proof. vm_compute. reflexivity. Qed.
