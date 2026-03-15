Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List. Import ListNotations.
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.

Local Open Scope positive_scope.

Definition bls12_381_prime_pos : positive :=
  Eval vm_compute in
    (Z.to_pos (let u := (-0xd201000000010000)%Z in
     (((u - 1)^2 * (u^4 - u^2 + 1)) / 3 + u)%Z)).

(* Verify the certificate evaluates to true *)
Lemma cert_true : test_Certif
  [Pock_certif bls12_381_prime_pos 2
    [(15778400344354997994418419698270088123916926905054652752758194827714659, 1); (2584487767265781317813, 1); (52437899, 1); (859267, 1); (10177, 1); (47, 1); (23, 1); (11, 1); (3, 2); (2, 1)] 1;
  Pock_certif 11 2 [(5, 1); (2, 1)] 1;
  Pock_certif 5 2 [(2, 2)] 1;
  Pock_certif 23 5 [(11, 1); (2, 1)] 1;
  Pock_certif 47 5 [(23, 1); (2, 1)] 1;
  Pock_certif 10177 7 [(53, 1); (3, 1); (2, 6)] 1;
  Pock_certif 53 2 [(13, 1); (2, 2)] 1;
  Pock_certif 13 2 [(3, 1); (2, 2)] 1;
  Proof_certif 3 prime_3;
  Proof_certif 2 prime_2
  ] = true.
Proof. vm_compute. reflexivity. Qed.
