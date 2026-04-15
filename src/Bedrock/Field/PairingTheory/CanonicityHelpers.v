(** * CanonicityHelpers.v — pointwise discharge of [zproj_initial_rel]
    under a canonicity hypothesis.

    Separated from [MillerEquiv.v] so iterating on arithmetic-level
    tactics doesn't re-trigger the 6-minute [native_compute]
    cross-check on the BN254 generators.

    The lemma [zproj_initial_rel_canonical] proved here closes the
    structural-equality form of [proj_affine_rel] for any [Fp2_Z]
    input with canonical components.  It is NOT directly usable to
    fill the universal [initial_rel] Hypothesis in
    [Section ProjEqAffine] (which asserts [forall Qx Qy, ...] and is
    FALSE for arbitrary non-canonical inputs).  Future work
    restructures the Section to accept canonicity; then
    [zproj_initial_rel] closes by this lemma. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Bedrock.Field.PairingTheory.Affine.
Require Import Crypto.Bedrock.Field.PairingTheory.Projective.
Require Import Crypto.Bedrock.Field.PairingTheory.ZModTower.
Require Import Crypto.Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

(** Canonicity predicate: both components of an [Fp2_Z] lie in [0, p). *)
Definition fp2_canonical (p : Z) (x : Fp2_Z) : Prop :=
  0 <= fst x < p /\ 0 <= snd x < p.

(** --- Unit lemmas on [zfp_*] --- *)

Lemma zfp_mul_0_r p x : zfp_mul p x 0 = 0.
Proof. unfold zfp_mul. rewrite Z.mul_0_r, Zmod_0_l. reflexivity. Qed.

Lemma zfp_mul_0_l p x : zfp_mul p 0 x = 0.
Proof. unfold zfp_mul. rewrite Z.mul_0_l, Zmod_0_l. reflexivity. Qed.

Lemma zfp_mul_1_r p x : 1 < p -> 0 <= x < p -> zfp_mul p x 1 = x.
Proof. intros. unfold zfp_mul. rewrite Z.mul_1_r, Z.mod_small; lia. Qed.

Lemma zfp_sub_0_r p x : 0 <= x < p -> zfp_sub p x 0 = x.
Proof. unfold zfp_sub. intros. rewrite Z.sub_0_r, Z.mod_small; lia. Qed.

Lemma zfp_add_0_l p x : 0 <= x < p -> zfp_add p 0 x = x.
Proof. unfold zfp_add. intros. rewrite Z.add_0_l, Z.mod_small; lia. Qed.

(** --- [zfp2_*] on unit values --- *)

Lemma zfp2_sqr_one p (Hp : 1 < p) :
  zfp2_sqr p (1, 0) = (1, 0).
Proof.
  assert (H0 : 0 mod p = 0) by (apply Z.mod_0_l; lia).
  assert (H1 : 1 mod p = 1) by (apply Z.mod_1_l; lia).
  unfold zfp2_sqr, zfp2_mul, zfp_mul, zfp_sub, zfp_add.
  cbn [fst snd].
  replace (1 * 1) with 1 by ring.
  replace (0 * 0) with 0 by ring.
  replace (1 * 0) with 0 by ring.
  replace (0 * 1) with 0 by ring.
  rewrite H0, H1.
  replace (1 - 0) with 1 by ring.
  replace (0 + 0) with 0 by ring.
  rewrite H1, H0.
  reflexivity.
Qed.

Lemma zfp2_mul_one_r p (Hp : 1 < p) Qx :
  fp2_canonical p Qx ->
  zfp2_mul p Qx (1, 0) = Qx.
Proof.
  intros [H0 H1]. unfold zfp2_mul. destruct Qx as [x0 x1]; simpl in *.
  rewrite zfp_mul_0_r, zfp_mul_1_r by lia.
  rewrite zfp_mul_0_r, zfp_mul_1_r by lia.
  rewrite zfp_sub_0_r by lia.
  rewrite zfp_add_0_l by lia.
  reflexivity.
Qed.

Lemma zfp2_mul_one_cube p (Hp : 1 < p) :
  zfp2_mul p (zfp2_sqr p (1, 0)) (1, 0) = (1, 0).
Proof.
  rewrite zfp2_sqr_one by lia.
  apply zfp2_mul_one_r; [lia | split; simpl; lia].
Qed.

(** --- Canonicity is preserved by all [zfp*] operations.
    Crucial for the simulation argument: if the Miller loop starts
    in canonical form, every intermediate value stays canonical, so
    the structural-equality [proj_affine_rel] is well-defined. *)

Lemma zfp_mul_canonical p : forall x y, 0 < p -> 0 <= zfp_mul p x y < p.
Proof. intros. unfold zfp_mul. apply Z.mod_pos_bound; lia. Qed.

Lemma zfp_add_canonical p : forall x y, 0 < p -> 0 <= zfp_add p x y < p.
Proof. intros. unfold zfp_add. apply Z.mod_pos_bound; lia. Qed.

Lemma zfp_sub_canonical p : forall x y, 0 < p -> 0 <= zfp_sub p x y < p.
Proof. intros. unfold zfp_sub. apply Z.mod_pos_bound; lia. Qed.

Lemma zfp2_mul_canonical p : forall x y, 0 < p ->
  fp2_canonical p (zfp2_mul p x y).
Proof.
  intros x y Hp. unfold zfp2_mul, fp2_canonical. cbn [fst snd].
  split.
  - apply zfp_sub_canonical; exact Hp.
  - apply zfp_add_canonical; exact Hp.
Qed.

Lemma zfp2_sqr_canonical p : forall x, 0 < p ->
  fp2_canonical p (zfp2_sqr p x).
Proof. intros. apply zfp2_mul_canonical; assumption. Qed.

Lemma zfp2_add_canonical p : forall x y, 0 < p ->
  fp2_canonical p (zfp2_add p x y).
Proof.
  intros x y Hp. unfold zfp2_add, fp2_canonical. cbn [fst snd].
  split; apply zfp_add_canonical; exact Hp.
Qed.

Lemma zfp2_sub_canonical p : forall x y, 0 < p ->
  fp2_canonical p (zfp2_sub p x y).
Proof.
  intros x y Hp. unfold zfp2_sub, fp2_canonical. cbn [fst snd].
  split; apply zfp_sub_canonical; exact Hp.
Qed.

(** The main deliverable: pointwise, canonicity-aware form of
    [zproj_initial_rel].  Directly witnesses the dehomogenisation
    invariant [Tx * TZ^2 = TX /\ Ty * TZ^3 = TY] for the loop's
    initial state [T = (Qx, Qy, 1)] when [Qx], [Qy] are canonical. *)
Lemma zproj_initial_rel_canonical :
  forall c (ml : Fp2_Z -> Fp2_Z -> Fp2_Z -> Z -> Z -> Fp12_Z)
         (Qx Qy : Fp2_Z),
    1 < prime_p c ->
    fp2_canonical (prime_p c) Qx ->
    fp2_canonical (prime_p c) Qy ->
    (* The body of [proj_affine_rel (zproj_ops c ml) Qx Qy Qx Qy (1, 0)]
       reduces via [cbn] to the two equalities below. *)
    zfp2_mul (prime_p c) Qx (zfp2_sqr (prime_p c) (1, 0)) = Qx
    /\ zfp2_mul (prime_p c) Qy
         (zfp2_mul (prime_p c) (zfp2_sqr (prime_p c) (1, 0)) (1, 0)) = Qy.
Proof.
  intros c ml Qx Qy Hp HcQx HcQy.
  split.
  - rewrite zfp2_sqr_one by exact Hp.
    apply zfp2_mul_one_r; assumption.
  - rewrite zfp2_mul_one_cube by exact Hp.
    apply zfp2_mul_one_r; assumption.
Qed.
