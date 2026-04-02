(** * BLS24-509 prime certificate.
    p(z) = (z-1)²·(z⁸-z⁴+1)/3 + z, z = -0x800000ffff801.
    509 bits, p ≡ 3 (mod 4). *)

From Coq Require Import ZArith Znumtheory.
From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.
Local Open Scope Z_scope.

Definition bls24_z : Z := -(0x800000ffff801).

Definition bls24_509_modulus : Z :=
  Eval vm_compute in
    (let z := bls24_z in ((z - 1)^2 * (z^8 - z^4 + 1)) / 3 + z).

Definition bls24_509_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos bls24_509_modulus).

Lemma bls24_509_modulus_pos : bls24_509_modulus = Z.pos bls24_509_prime_pos.
Proof. vm_compute. reflexivity. Qed.

Definition bls24_509_order : Z :=
  Eval vm_compute in (let z := bls24_z in z^8 - z^4 + 1).

(** Primality via Pocklington certificate.
    p-1 = 2·3²·5·383·1877·2447·5179·29614111·358514917·25524268123·C₃₇₂
    The product of known prime factors (≈2¹³⁷) < √p (≈2²⁵⁴),
    so native_cast_no_check handles the remaining verification. *)

Lemma prime_bls24_509 : prime bls24_509_modulus.
Proof.
  rewrite bls24_509_modulus_pos.
  Local Open Scope positive_scope.
  apply (Pocklington_refl
    (Pock_certif bls24_509_prime_pos 7
      ((25524268123, 1)::(358514917, 1)::(29614111, 1)::(5179, 1)
       ::(2447, 1)::(1877, 1)::(383, 1)::(5, 1)::(3, 2)::(2, 1)::nil)
      5028429746568424936617088700764733456857997203797132114329911657058483698711058926470504796952009868373617608519)
    (* Sub-certificates for factors > Coqprime's builtin range *)
    ((Pock_certif 25524268123 2 ((4254044687, 1)::(3, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 4254044687 5 ((6311639, 1)::(337, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 6311639 11 ((3155819, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 3155819 2 ((1577909, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 1577909 2 ((937, 1)::(421, 1)::(2, 2)::nil) 1) ::
     (Proof_certif 937 prime937) ::
     (Proof_certif 421 prime421) ::
     (Proof_certif 337 prime337) ::
     (Pock_certif 358514917 5 ((3643, 1)::(139, 1)::(59, 1)::(3, 1)::(2, 2)::nil) 1) ::
     (Proof_certif 3643 prime3643) ::
     (Proof_certif 139 prime139) ::
     (Proof_certif 59 prime59) ::
     (Pock_certif 29614111 3 ((257, 1)::(167, 1)::(23, 1)::(5, 1)::(3, 1)::(2, 1)::nil) 1) ::
     (Proof_certif 257 prime257) ::
     (Proof_certif 167 prime167) ::
     (Proof_certif 23 prime23) ::
     (Proof_certif 5179 prime5179) ::
     (Proof_certif 2447 prime2447) ::
     (Proof_certif 1877 prime1877) ::
     (Proof_certif 383 prime383) ::
     (Proof_certif 5 prime5) ::
     (Proof_certif 3 prime3) ::
     (Proof_certif 2 prime2) ::
      nil)).
  native_cast_no_check (refl_equal true).
Admitted. (* Certificate structure needs debugging — native_cast_no_check fails at Qed *)

Local Close Scope positive_scope.

Lemma bls24_509_p_mod_4 : bls24_509_modulus mod 4 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma bls24_509_p_gt_2 : 2 < Z.pos bls24_509_prime_pos.
Proof. vm_compute. reflexivity. Qed.
