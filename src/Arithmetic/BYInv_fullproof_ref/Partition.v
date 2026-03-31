Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.

Require Import Crypto.Arithmetic.BYInv.Definitions.

Local Open Scope Z_scope.

Lemma partition_in_bounded machine_wordsize limbs a :
  (0 < machine_wordsize) ->
  in_bounded machine_wordsize (Partition.partition (uweight machine_wordsize) limbs a).
Proof.
  intros mw0.
  pose proof uwprops machine_wordsize mw0.
  intros x Hin.
  unfold Partition.partition in Hin. apply ListAux.in_map_inv in Hin.
  destruct Hin as [y [Hin]].
  rewrite H0, !uweight_eq_alt by lia. split.
  - apply Z.div_le_lower_bound;
      ring_simplify; try apply Z.mod_pos_bound;
      apply Z.pow_pos_nonneg; try apply Z.pow_pos_nonneg; lia.
  - apply Z.div_lt_upper_bound.
    apply Z.pow_pos_nonneg; try apply Z.pow_pos_nonneg; lia.
    replace ((_ ^ _) ^ _ * _) with ((2 ^ machine_wordsize) ^ Z.of_nat (S y)).
    apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; try apply Z.pow_pos_nonneg; lia.
    rewrite Z.mul_comm, Pow.Z.pow_mul_base;
      try (replace (Z.of_nat (S y)) with ((Z.of_nat y + 1)) by lia; lia).
Qed.
