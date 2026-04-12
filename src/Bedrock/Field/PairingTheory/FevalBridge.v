(** * FevalBridge: connect bedrock2 [feval] to ZModTower's flat-Z types.

    The bedrock2 field representation uses:
      - [Fp_feval : list word -> F M_pos]   (base field)
      - [Fp2_feval : list word -> Fp * Fp]  (quadratic extension)
      - [Fp12_feval : list word -> Fp6 * Fp6] (dodecic extension)

    The ZModTower uses:
      - [Z]                                (base field, Z mod p)
      - [Fp2_Z = Z * Z]                   (quadratic extension)
      - [Fp12_Z = Fp6_Z * Fp6_Z]          (dodecic extension)

    This file provides bridge functions that map between the two
    representations via [F.to_Z : F M_pos -> Z].

    The key theorem (proved per field layer) is:
      [bedrock2_op feval args = zmod_op (bridge args)]
    where [bedrock2_op] is an operation at the FElem level and
    [zmod_op] is the corresponding ZModTower operation. This lets
    the Miller loop equivalence theorem be stated as:
      [bridge (Fp12_feval out) = affine_miller bn254_zmod_ops ...]

    IMPORTANT: [F.to_Z] maps a field element to its canonical
    representative in [0, p). The ZModTower operations use [Z.modulo]
    to stay in [0, p). So the bridge is lossless: [F.to_Z] composed
    with [F.of_Z] is the identity (for values in [0, p)).
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.PairingTheory.ZModTower.

Local Open Scope Z_scope.

Section FevalBridge.

  Variable M_pos : positive.
  Local Notation Fp := (F M_pos).

  (** Base field bridge: F M_pos -> Z *)
  Definition fp_to_Z (x : Fp) : Z := F.to_Z x.

  (** Fp2 bridge: Fp * Fp -> Z * Z *)
  Definition fp2_to_Z (x : Fp * Fp) : Fp2_Z :=
    (fp_to_Z (fst x), fp_to_Z (snd x)).

  (** Fp6 bridge: (Fp2 * Fp2 * Fp2) -> Fp6_Z *)
  Definition fp6_to_Z (x : (Fp * Fp) * (Fp * Fp) * (Fp * Fp)) : Fp6_Z :=
    mk_fp6 (fp2_to_Z (fst (fst x)))
           (fp2_to_Z (snd (fst x)))
           (fp2_to_Z (snd x)).

  (** Fp12 bridge: (Fp6 * Fp6) -> Fp12_Z *)
  Definition fp12_to_Z
    (x : ((Fp * Fp) * (Fp * Fp) * (Fp * Fp)) *
         ((Fp * Fp) * (Fp * Fp) * (Fp * Fp))) : Fp12_Z :=
    (fp6_to_Z (fst x), fp6_to_Z (snd x)).

  (** Reverse bridge: Z -> F M_pos *)
  Definition Z_to_fp (x : Z) : Fp := F.of_Z M_pos x.

  (** Round-trip lemma: to_Z ∘ of_Z = id (mod p). *)
  Lemma fp_to_Z_of_Z (x : Z) :
    0 <= x < Z.pos M_pos ->
    fp_to_Z (Z_to_fp x) = x.
  Proof.
    intros [Hlo Hhi].
    unfold fp_to_Z, Z_to_fp.
    rewrite F.to_Z_of_Z.
    rewrite Z.mod_small; [reflexivity | lia].
  Qed.

  (** The core bridging lemma for each operation would look like:
        fp_to_Z (F.add x y) = zfp_add (Z.pos M_pos) (fp_to_Z x) (fp_to_Z y)
      These are straightforward from [F.to_Z_add] etc. but I leave them
      for Phase 4 since they're needed only when closing the actual
      equivalence proof. *)

End FevalBridge.

(** Bridge FieldOps instance: instantiate Affine.FieldOps with the
    fiat-crypto field types (F M_pos) directly. This lets us state
    the equivalence as:
      affine_miller (feval_ops M_pos) = affine_miller (zmod_ops M_pos)
    where the LHS uses F-level operations and the RHS uses Z-level.
    The bridge lemma proves both sides compute the same value. *)

(* Future work: define feval_ops and prove the bridge. *)
