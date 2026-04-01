(** * Fp12 feval bridge lemmas for BLS12-377.
 *
 *  Identical structure to BLS12_Fp12Feval.v but parameterized for any
 *  beta/xi values (BLS12-377 uses beta=-5, xi=(0,1) vs BLS12-381's
 *  beta=-1, xi=(1,1)).
 *
 *  The key lemmas (fp12_mul_eq, fp12_sqr_eq, etc.) are proved inside
 *  a Section and compiled to .vo so downstream files get small constant
 *  references instead of inlined hypothesis terms.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.BLS12Pairing.Pairing.
Require Import Crypto.Spec.BLS12Pairing.Fp6.
Require Import Crypto.Spec.BLS12Pairing.Fp12.

Local Open Scope Z_scope.

Local Opaque Fp6.fp6_add Fp6.fp6_sub Fp6.fp6_neg Fp6.fp6_mul
  Fp6.fp6_sqr Fp6.fp6_mul_by_v Fp6.fp6_inv Fp6.fp6_mul_fp2
  Fp6.fp6_frobenius Fp6.fp6_frobenius_p2.
Local Opaque Pairing.fp6_add Pairing.fp6_sub Pairing.fp6_neg Pairing.fp6_mul
  Pairing.fp6_sqr Pairing.fp6_mul_by_v Pairing.fp6_inv Pairing.fp6_mul_fp2
  Pairing.fp6_frobenius Pairing.fp6_frobenius_p2.
(* NOTE: Fp12 operations are NOT opaque here — bridge proofs need to unfold them.
   Downstream files (BLS12_377_PairingFeval) make them opaque. *)
Local Opaque Pairing.bls_x_bits Pairing.bls_x.
Local Opaque Pairing.h3_exp Pairing.h3_width Pairing.Z_to_bits.
Local Opaque Pairing.fp12_pow_bits_aux Pairing.fp12_pow_bits Pairing.fp12_pow_Z.
Local Opaque Pairing.fp12_pow_bls_x Pairing.fp12_pow_bls_x_signed
  Pairing.fp12_pow_bls_x_half Pairing.fp12_pow_bls_x_half_signed.

Section Fp12Bridge377.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6' := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12' := (Fp6' * Fp6')%type.

  Variable beta : Fp.
  Variable xi_re xi_im : Fp.

  (* Frobenius constants *)
  Variable fg1 fg2 fg1_p2 fg2_p2 : Fp2.
  Variable w_frob_c1 w_frob_p2_c1 : Fp2.

  (* Fp6 bridge hypotheses *)
  Hypothesis fp6_add_hyp : forall a b : Fp6',
    Fp6.fp6_add p a b = Pairing.fp6_add p a b.
  Hypothesis fp6_sub_hyp : forall a b : Fp6',
    Fp6.fp6_sub p a b = Pairing.fp6_sub p a b.
  Hypothesis fp6_neg_hyp : forall a : Fp6',
    Fp6.fp6_neg p a = Pairing.fp6_neg p a.
  Hypothesis fp6_mul_hyp : forall a b : Fp6',
    Fp6.fp6_mul p beta xi_re xi_im a b = Pairing.fp6_mul p a b.
  Hypothesis fp6_mul_by_v_hyp : forall a : Fp6',
    Fp6.fp6_mul_by_v p beta xi_re xi_im a = Pairing.fp6_mul_by_v p a.
  Hypothesis fp6_sqr_hyp : forall a : Fp6',
    Fp6.fp6_sqr p beta xi_re xi_im a = Pairing.fp6_sqr p a.
  Hypothesis pairing_fp6_mul_self_eq_sqr : forall a : Fp6',
    Pairing.fp6_mul p a a = Pairing.fp6_sqr p a.
  Hypothesis fp6_karatsuba_cross_term : forall a b : Fp6',
    Pairing.fp6_sub p
      (Pairing.fp6_sub p
        (Pairing.fp6_mul p (Pairing.fp6_add p a b) (Pairing.fp6_add p a b))
        (Pairing.fp6_mul p a a))
      (Pairing.fp6_mul p b b) =
    Pairing.fp6_add p (Pairing.fp6_mul p a b) (Pairing.fp6_mul p a b).
  Hypothesis fp6_frobenius_p2_hyp : forall a : Fp6',
    Fp6.fp6_frobenius_p2 p beta fg1_p2 fg2_p2 a =
    Pairing.fp6_frobenius_p2 p fg1_p2 fg2_p2 a.
  Hypothesis fp6_mul_fp2_hyp : forall (a : Fp6') (s : Fp2),
    Fp6.fp6_mul_fp2 p beta a s = Pairing.fp6_mul_fp2 p a s.
  Hypothesis fp6_inv_hyp : forall a : Fp6',
    Fp6.fp6_inv p beta xi_re xi_im a = Pairing.fp6_inv p a.
  Hypothesis fp6_frobenius_hyp : forall a : Fp6',
    Fp6.fp6_frobenius p beta fg1 fg2 a =
    Pairing.fp6_frobenius p fg1 fg2 a.

  (* ---- Fp12 bridge lemmas ---- *)

  (* Helper: rewrite all Fp6 bridges that apply, skip identity ones *)
  Local Ltac fp6_bridge :=
    repeat first
      [ rewrite fp6_mul_hyp
      | rewrite fp6_sqr_hyp
      | rewrite fp6_mul_by_v_hyp
      | rewrite fp6_inv_hyp
      | rewrite fp6_frobenius_hyp
      | rewrite fp6_frobenius_p2_hyp
      | rewrite fp6_mul_fp2_hyp
      | rewrite fp6_add_hyp
      | rewrite fp6_sub_hyp
      | rewrite fp6_neg_hyp ].

  Lemma fp12_mul_eq : forall a b : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im a b = Pairing.fp12_mul p a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold Fp12.fp12_mul, Pairing.fp12_mul. fp6_bridge. reflexivity.
  Qed.

  Lemma fp12_sqr_eq : forall a : Fp12',
    Fp12.fp12_sqr p beta xi_re xi_im a = Pairing.fp12_sqr p a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_sqr, Pairing.fp12_sqr.
    fp6_bridge. rewrite !pairing_fp6_mul_self_eq_sqr. reflexivity.
  Qed.

  Lemma fp12_conjugate_eq : forall a : Fp12',
    Fp12.fp12_conjugate p a = Pairing.fp12_conjugate p a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_conjugate, Pairing.fp12_conjugate. fp6_bridge. reflexivity.
  Qed.

  Lemma fp12_inv_eq : forall a : Fp12',
    Fp12.fp12_inv p beta xi_re xi_im a = Pairing.fp12_inv p a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_inv, Pairing.fp12_inv,
           Fp12.fp12_c0, Fp12.fp12_c1, Fp12.mk_fp12,
           Pairing.fp12_c0, Pairing.fp12_c1, Pairing.fp12_build.
    simpl fst; simpl snd.
    fp6_bridge. rewrite !pairing_fp6_mul_self_eq_sqr. reflexivity.
  Qed.

  Lemma fp12_frobenius_eq : forall a : Fp12',
    Fp12.fp12_frobenius p beta fg1 fg2 w_frob_c1 a =
    Pairing.fp12_frobenius p fg1 fg2 w_frob_c1 a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_frobenius, Pairing.fp12_frobenius. fp6_bridge. reflexivity.
  Qed.

  Lemma fp12_frobenius_p2_eq : forall a : Fp12',
    Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1 a =
    Pairing.fp12_frobenius_p2 p fg1_p2 fg2_p2 w_frob_p2_c1 a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_frobenius_p2, Pairing.fp12_frobenius_p2. fp6_bridge. reflexivity.
  Qed.

  (* ---- Binary exponentiation ---- *)

  Fixpoint bedrock2_pow_bits_aux (base : Fp12') (bits : list bool)
    (acc : Fp12') (started : bool) : Fp12' :=
    match bits with
    | [] => acc
    | b :: rest =>
      let acc' := if started then Fp12.fp12_sqr p beta xi_re xi_im acc
                  else acc in
      if b then
        let acc'' := if started
                     then Fp12.fp12_mul p beta xi_re xi_im acc' base
                     else base in
        bedrock2_pow_bits_aux base rest acc'' true
      else
        bedrock2_pow_bits_aux base rest acc' started
    end.

  Lemma pow_bits_aux_feval : forall bits base acc started,
    bedrock2_pow_bits_aux base bits acc started =
    Pairing.fp12_pow_bits_aux p base bits acc started.
  Proof.
    induction bits as [|b bs IH]; intros base acc started.
    - abstract reflexivity.
    - simpl bedrock2_pow_bits_aux. simpl Pairing.fp12_pow_bits_aux.
      rewrite fp12_sqr_eq, fp12_mul_eq. destruct b; apply IH.
  Qed.

  Definition bedrock2_pow_Z (base : Fp12') (exp : Z) (width : nat) : Fp12' :=
    bedrock2_pow_bits_aux base (Pairing.Z_to_bits width exp)
      (Fp12.fp12_one p) false.

  Lemma pow_Z_feval : forall base exp width,
    bedrock2_pow_Z base exp width = Pairing.fp12_pow_Z p base exp width.
  Proof.
    intros.
    Transparent Pairing.fp12_pow_Z Pairing.fp12_pow_bits.
    unfold bedrock2_pow_Z, Pairing.fp12_pow_Z, Pairing.fp12_pow_bits.
    Opaque Pairing.fp12_pow_Z Pairing.fp12_pow_bits.
    f_equal. apply pow_bits_aux_feval.
  Qed.

  (* ---- Power-by-BLS-parameter ---- *)
  Definition bedrock2_pow_bls_x (f : Fp12') : Fp12' :=
    bedrock2_pow_Z f Pairing.bls_x 64.

  Lemma pow_bls_x_feval : forall f,
    bedrock2_pow_bls_x f = Pairing.fp12_pow_bls_x p f.
  Proof.
    Transparent Pairing.fp12_pow_bls_x.
    intro. unfold bedrock2_pow_bls_x, Pairing.fp12_pow_bls_x.
    Opaque Pairing.fp12_pow_bls_x.
    apply pow_Z_feval.
  Qed.

  Definition bedrock2_pow_bls_x_signed (f : Fp12') : Fp12' :=
    Fp12.fp12_conjugate p (bedrock2_pow_bls_x f).

  Lemma pow_bls_x_signed_feval : forall f,
    bedrock2_pow_bls_x_signed f = Pairing.fp12_pow_bls_x_signed p f.
  Proof.
    Transparent Pairing.fp12_pow_bls_x_signed.
    intro f. unfold bedrock2_pow_bls_x_signed, Pairing.fp12_pow_bls_x_signed.
    Opaque Pairing.fp12_pow_bls_x_signed.
    rewrite fp12_conjugate_eq, pow_bls_x_feval. reflexivity.
  Qed.

  Definition bedrock2_pow_bls_x_half (f : Fp12') : Fp12' :=
    bedrock2_pow_Z f (Pairing.bls_x / 2) 63.

  Lemma pow_bls_x_half_feval : forall f,
    bedrock2_pow_bls_x_half f = Pairing.fp12_pow_bls_x_half p f.
  Proof.
    Transparent Pairing.fp12_pow_bls_x_half.
    intro. unfold bedrock2_pow_bls_x_half, Pairing.fp12_pow_bls_x_half.
    Opaque Pairing.fp12_pow_bls_x_half.
    apply pow_Z_feval.
  Qed.

  Definition bedrock2_pow_bls_x_half_signed (f : Fp12') : Fp12' :=
    Fp12.fp12_conjugate p (bedrock2_pow_bls_x_half f).

  Lemma pow_bls_x_half_signed_feval : forall f,
    bedrock2_pow_bls_x_half_signed f = Pairing.fp12_pow_bls_x_half_signed p f.
  Proof.
    Transparent Pairing.fp12_pow_bls_x_half_signed.
    intro f.
    unfold bedrock2_pow_bls_x_half_signed, Pairing.fp12_pow_bls_x_half_signed.
    Opaque Pairing.fp12_pow_bls_x_half_signed.
    rewrite fp12_conjugate_eq, pow_bls_x_half_feval. reflexivity.
  Qed.

End Fp12Bridge377.
