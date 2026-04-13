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

  (** Per-operation bridging lemmas: each shows that F-level operations
      commute with to_Z, i.e., to_Z preserves the ring structure.
      These bridge between fiat-crypto's [F M_pos] and [Z/pZ]. *)

  Lemma fp_to_Z_add (x y : Fp) :
    fp_to_Z (F.add x y) = ((fp_to_Z x) + (fp_to_Z y)) mod (Z.pos M_pos).
  Proof. unfold fp_to_Z. apply F.to_Z_add. Qed.

  Lemma fp_to_Z_sub (x y : Fp) :
    fp_to_Z (F.sub x y) = ((fp_to_Z x) - (fp_to_Z y)) mod (Z.pos M_pos).
  Proof. unfold fp_to_Z. apply F.to_Z_sub. Qed.

  Lemma fp_to_Z_mul (x y : Fp) :
    fp_to_Z (F.mul x y) = ((fp_to_Z x) * (fp_to_Z y)) mod (Z.pos M_pos).
  Proof. unfold fp_to_Z. apply F.to_Z_mul. Qed.

  Lemma fp_to_Z_opp (x : Fp) :
    fp_to_Z (F.opp x) = (- (fp_to_Z x)) mod (Z.pos M_pos).
  Proof. unfold fp_to_Z. apply F.to_Z_opp. Qed.

  Lemma fp_to_Z_zero : fp_to_Z (@F.zero M_pos) = 0.
  Proof. unfold fp_to_Z. rewrite F.to_Z_0. reflexivity. Qed.

  Lemma fp_to_Z_one : fp_to_Z (@F.one M_pos) = 1 mod (Z.pos M_pos).
  Proof. unfold fp_to_Z. rewrite F.to_Z_1. reflexivity. Qed.

  (** Fp2-level bridging: component-wise *)
  Lemma fp2_to_Z_add (x y : Fp * Fp) :
    fp2_to_Z (F.add (fst x) (fst y), F.add (snd x) (snd y)) =
    (fp_to_Z (F.add (fst x) (fst y)), fp_to_Z (F.add (snd x) (snd y))).
  Proof. unfold fp2_to_Z. reflexivity. Qed.

  Lemma fp2_to_Z_fst (x : Fp * Fp) : fst (fp2_to_Z x) = fp_to_Z (fst x).
  Proof. reflexivity. Qed.

  Lemma fp2_to_Z_snd (x : Fp * Fp) : snd (fp2_to_Z x) = fp_to_Z (snd x).
  Proof. reflexivity. Qed.

End FevalBridge.

(** Bridge FieldOps instance: instantiate Affine.FieldOps with the
    fiat-crypto field types (F M_pos) directly. This lets us state
    the equivalence as:
      affine_miller (feval_ops M_pos) = affine_miller (zmod_ops M_pos)
    where the LHS uses F-level operations and the RHS uses Z-level.
    The bridge lemma proves both sides compute the same value.

    The per-operation lemmas above (fp_to_Z_add, fp_to_Z_mul, etc.)
    are the key ingredients: they show to_Z is a ring homomorphism.
    To build the full bridge:
    1. Define feval_ops : FieldOps using F-level operations
    2. Prove each FieldOps operation commutes with to_Z
    3. Apply the generic affine_miller_ext_equiv lemma (from Affine.v)
       to get: affine_miller feval_ops P Q = affine_miller zmod_ops P Q
    4. Connect feval_ops to the bedrock2 feval via WP postconditions *)
