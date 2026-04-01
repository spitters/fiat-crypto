(** * DSD pairing feval correctness for BLS12-377.
 *
 *  Imports pre-compiled bridge lemmas from BLS12_377_Fp12Feval.vo
 *  to avoid Section-hypothesis inlining OOM.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.BLS12Pairing.Pairing.
Require Import Crypto.Spec.BLS12Pairing.Fp6.
Require Import Crypto.Spec.BLS12Pairing.Fp12.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_377_Fp12Feval.

Local Open Scope Z_scope.

Local Opaque Fp6.fp6_add Fp6.fp6_sub Fp6.fp6_neg Fp6.fp6_mul
  Fp6.fp6_sqr Fp6.fp6_mul_by_v Fp6.fp6_inv Fp6.fp6_mul_fp2
  Fp6.fp6_frobenius Fp6.fp6_frobenius_p2.
Local Opaque Pairing.fp6_add Pairing.fp6_sub Pairing.fp6_neg Pairing.fp6_mul
  Pairing.fp6_sqr Pairing.fp6_mul_by_v Pairing.fp6_inv Pairing.fp6_mul_fp2
  Pairing.fp6_frobenius Pairing.fp6_frobenius_p2.
Local Opaque Fp12.fp12_mul Fp12.fp12_sqr Fp12.fp12_add Fp12.fp12_sub
  Fp12.fp12_neg Fp12.fp12_conjugate Fp12.fp12_inv
  Fp12.fp12_frobenius Fp12.fp12_frobenius_p2.
Local Opaque Pairing.fp12_mul Pairing.fp12_sqr Pairing.fp12_add
  Pairing.fp12_sub Pairing.fp12_neg Pairing.fp12_conjugate Pairing.fp12_inv
  Pairing.fp12_frobenius Pairing.fp12_frobenius_p2.
Local Opaque Pairing.bls_x_bits Pairing.bls_x.
Local Opaque Pairing.h3_exp Pairing.h3_width Pairing.Z_to_bits.
Local Opaque Pairing.fp12_pow_bits_aux Pairing.fp12_pow_bits Pairing.fp12_pow_Z.
Local Opaque Pairing.fp12_pow_bls_x Pairing.fp12_pow_bls_x_signed
  Pairing.fp12_pow_bls_x_half Pairing.fp12_pow_bls_x_half_signed.
Local Opaque Pairing.final_exp_hard_dsd Pairing.final_exponentiation_dsd.

Section DSDPairingFeval.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6' := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12' := (Fp6' * Fp6')%type.

  Variable beta : Fp.
  Variable xi_re xi_im : Fp.

  Variable fg1 fg2 fg1_p2 fg2_p2 : Fp2.
  Variable w_frob_c1 w_frob_p2_c1 : Fp2.

  (* Fp6 bridge hypotheses — needed to instantiate Fp12 bridge *)
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
  Hypothesis fp6_mul_self_sqr : forall a : Fp6',
    Pairing.fp6_mul p a a = Pairing.fp6_sqr p a.
  Hypothesis fp6_karatsuba : forall a b : Fp6',
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

  (* Pre-compiled Fp12 bridge lemmas from BLS12_377_Fp12Feval *)
  Local Lemma sqr_eq : forall a : Fp12',
    Fp12.fp12_sqr p beta xi_re xi_im a = Pairing.fp12_sqr p a.
  Proof. apply fp12_sqr_eq; assumption. Qed.

  Local Lemma mul_eq : forall a b : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im a b = Pairing.fp12_mul p a b.
  Proof. apply fp12_mul_eq; assumption. Qed.

  Local Lemma conjugate_eq' : forall a : Fp12',
    Fp12.fp12_conjugate p a = Pairing.fp12_conjugate p a.
  Proof. apply fp12_conjugate_eq; assumption. Qed.

  Local Lemma inv_eq' : forall a : Fp12',
    Fp12.fp12_inv p beta xi_re xi_im a = Pairing.fp12_inv p a.
  Proof. apply fp12_inv_eq; assumption. Qed.

  Local Lemma frobenius_eq' : forall a : Fp12',
    Fp12.fp12_frobenius p beta fg1 fg2 w_frob_c1 a =
    Pairing.fp12_frobenius p fg1 fg2 w_frob_c1 a.
  Proof. apply fp12_frobenius_eq; assumption. Qed.

  Local Lemma frobenius_p2_eq' : forall a : Fp12',
    Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1 a =
    Pairing.fp12_frobenius_p2 p fg1_p2 fg2_p2 w_frob_p2_c1 a.
  Proof. apply fp12_frobenius_p2_eq; assumption. Qed.

  (* ---- DSD hard part ---- *)
  Local Opaque BLS12_377_Fp12Feval.bedrock2_pow_bls_x
    BLS12_377_Fp12Feval.bedrock2_pow_bls_x_signed
    BLS12_377_Fp12Feval.bedrock2_pow_bls_x_half
    BLS12_377_Fp12Feval.bedrock2_pow_bls_x_half_signed
    BLS12_377_Fp12Feval.bedrock2_pow_Z
    BLS12_377_Fp12Feval.bedrock2_pow_bits_aux.

  Definition bedrock2_final_exp_hard_dsd (f : Fp12') : Fp12' :=
    let t0 := Fp12.fp12_sqr p beta xi_re xi_im f in
    let t1 := BLS12_377_Fp12Feval.bedrock2_pow_bls_x_half_signed p beta xi_re xi_im t0 in
    let t2 := Fp12.fp12_conjugate p f in
    let t1 := Fp12.fp12_mul p beta xi_re xi_im t1 t2 in
    let t2 := BLS12_377_Fp12Feval.bedrock2_pow_bls_x_signed p beta xi_re xi_im t1 in
    let t1 := Fp12.fp12_conjugate p t1 in
    let t1 := Fp12.fp12_mul p beta xi_re xi_im t1 t2 in
    let t2 := BLS12_377_Fp12Feval.bedrock2_pow_bls_x_signed p beta xi_re xi_im t1 in
    let t1 := Fp12.fp12_frobenius p beta fg1 fg2 w_frob_c1 t1 in
    let t1 := Fp12.fp12_mul p beta xi_re xi_im t1 t2 in
    let result := Fp12.fp12_mul p beta xi_re xi_im f t0 in
    let t0 := BLS12_377_Fp12Feval.bedrock2_pow_bls_x_signed p beta xi_re xi_im t1 in
    let t2 := BLS12_377_Fp12Feval.bedrock2_pow_bls_x_signed p beta xi_re xi_im t0 in
    let t0 := Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1 t1 in
    let t1 := Fp12.fp12_conjugate p t1 in
    let t1 := Fp12.fp12_mul p beta xi_re xi_im t1 t2 in
    let t1 := Fp12.fp12_mul p beta xi_re xi_im t1 t0 in
    Fp12.fp12_mul p beta xi_re xi_im result t1.

  Lemma final_exp_hard_dsd_feval : forall f : Fp12',
    bedrock2_final_exp_hard_dsd f =
    Pairing.final_exp_hard_dsd p fg1 fg2 fg1_p2 fg2_p2
      w_frob_c1 w_frob_p2_c1 f.
  Proof.
    intro f.
    Transparent Pairing.final_exp_hard_dsd.
    unfold bedrock2_final_exp_hard_dsd, Pairing.final_exp_hard_dsd.
    Opaque Pairing.final_exp_hard_dsd.
    repeat first
      [ rewrite sqr_eq
      | rewrite mul_eq
      | rewrite (pow_bls_x_half_signed_feval p beta xi_re xi_im);
        [ idtac | assumption .. ]
      | rewrite (pow_bls_x_signed_feval p beta xi_re xi_im);
        [ idtac | assumption .. ]
      | rewrite conjugate_eq'
      | rewrite frobenius_eq'
      | rewrite frobenius_p2_eq' ].
    reflexivity.
  Qed.

  (* ---- Full DSD final exponentiation ---- *)
  Local Opaque bedrock2_final_exp_hard_dsd.

  Definition bedrock2_final_exp_dsd (f : Fp12') : Fp12' :=
    let f_conj := Fp12.fp12_conjugate p f in
    let f_inv := Fp12.fp12_inv p beta xi_re xi_im f in
    let result := Fp12.fp12_mul p beta xi_re xi_im f_conj f_inv in
    let result_p2 := Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2
                       w_frob_p2_c1 result in
    let result' := Fp12.fp12_mul p beta xi_re xi_im result_p2 result in
    bedrock2_final_exp_hard_dsd result'.

  Theorem final_exp_dsd_feval_correct : forall f : Fp12',
    bedrock2_final_exp_dsd f =
    Pairing.final_exponentiation_dsd p fg1 fg2 fg1_p2 fg2_p2
      w_frob_c1 w_frob_p2_c1 f.
  Proof.
    intro f.
    Transparent Pairing.final_exponentiation_dsd.
    unfold bedrock2_final_exp_dsd, Pairing.final_exponentiation_dsd.
    Opaque Pairing.final_exponentiation_dsd.
    rewrite conjugate_eq', inv_eq', mul_eq, frobenius_p2_eq', mul_eq.
    apply final_exp_hard_dsd_feval.
  Qed.

  (* ---- Top-level pairing ---- *)
  Local Opaque bedrock2_final_exp_dsd.

  Variable bedrock2_miller : Pairing.G1Affine p -> Pairing.G2Affine p -> Fp12'.
  Hypothesis miller_feval :
    forall (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p),
      Pairing.g1_infinity p P = false ->
      Pairing.g2_infinity p Q = false ->
      bedrock2_miller P Q = Pairing.miller_loop p P Q.

  Definition bedrock2_pairing_dsd (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p)
    : Fp12' :=
    bedrock2_final_exp_dsd (bedrock2_miller P Q).

  Theorem pairing_dsd_feval_correct :
    forall (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p),
      Pairing.g1_infinity p P = false ->
      Pairing.g2_infinity p Q = false ->
      bedrock2_pairing_dsd P Q =
      Pairing.final_exponentiation_dsd p fg1 fg2 fg1_p2 fg2_p2
        w_frob_c1 w_frob_p2_c1 (Pairing.miller_loop p P Q).
  Proof.
    intros P Q Hp Hq.
    unfold bedrock2_pairing_dsd.
    rewrite final_exp_dsd_feval_correct.
    f_equal. apply miller_feval; assumption.
  Qed.

End DSDPairingFeval.
