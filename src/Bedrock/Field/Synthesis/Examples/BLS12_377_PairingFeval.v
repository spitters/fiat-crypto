(** * DSD final exponentiation and pairing feval correctness for BLS12-377.
 *
 *  Proves that the bedrock2 final exponentiation (using Fp12.v operations)
 *  equals the Pairing.v Gallina model with the DSD optimised hard part,
 *  and composes with the Miller loop bridge to get a top-level pairing
 *  correctness theorem.
 *
 *  Key differences from BLS12-381 (BLS12_PairingFeval.v):
 *    - Uses final_exponentiation_dsd instead of final_exponentiation
 *    - DSD hard part is a chain of fp12_pow_bls_x / fp12_pow_bls_x_half,
 *      fp12_conjugate, fp12_mul, fp12_sqr, fp12_frobenius, fp12_frobenius_p2
 *    - Needs fp12_frobenius bridge (not just frobenius_p2)
 *    - All Fp12 bridge lemmas stated as Hypotheses (no bedrock2 imports)
 *
 *  OOM avoidance:
 *    - Does NOT import BLS12_Fp12Feval or any bedrock2 file
 *    - Makes pow-by-x functions Opaque before unfolding the DSD hard part
 *    - Keeps Fp6/Fp12 operations Opaque throughout
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.BLS12Pairing.Pairing.
Require Import Crypto.Spec.BLS12Pairing.Fp6.
Require Import Crypto.Spec.BLS12Pairing.Fp12.

Local Open Scope Z_scope.

(* Prevent term explosion by making Fp6-level operations opaque. *)
Local Opaque Fp6.fp6_add Fp6.fp6_sub Fp6.fp6_neg Fp6.fp6_mul
  Fp6.fp6_sqr Fp6.fp6_mul_by_v Fp6.fp6_inv Fp6.fp6_mul_fp2
  Fp6.fp6_frobenius Fp6.fp6_frobenius_p2.
Local Opaque Pairing.fp6_add Pairing.fp6_sub Pairing.fp6_neg Pairing.fp6_mul
  Pairing.fp6_sqr Pairing.fp6_mul_by_v Pairing.fp6_inv Pairing.fp6_mul_fp2
  Pairing.fp6_frobenius Pairing.fp6_frobenius_p2.

(* Also make Fp12-level operations opaque to control rewriting. *)
Local Opaque Fp12.fp12_mul Fp12.fp12_sqr Fp12.fp12_add Fp12.fp12_sub
  Fp12.fp12_neg Fp12.fp12_conjugate Fp12.fp12_inv
  Fp12.fp12_frobenius Fp12.fp12_frobenius_p2.
Local Opaque Pairing.fp12_mul Pairing.fp12_sqr Pairing.fp12_add
  Pairing.fp12_sub Pairing.fp12_neg Pairing.fp12_conjugate Pairing.fp12_inv
  Pairing.fp12_frobenius Pairing.fp12_frobenius_p2.

(* ================================================================ *)
(** ** Part 1: DSD final exponentiation feval                       *)
(* ================================================================ *)

Section DSDFinalExpFeval.
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

  (* ---- Fp12 bridge hypotheses ---- *)
  Hypothesis sqr_eq : forall a : Fp12',
    Fp12.fp12_sqr p beta xi_re xi_im a = Pairing.fp12_sqr p a.
  Hypothesis mul_eq : forall a b : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im a b = Pairing.fp12_mul p a b.
  Hypothesis conjugate_eq : forall a : Fp12',
    Fp12.fp12_conjugate p a = Pairing.fp12_conjugate p a.
  Hypothesis inv_eq : forall a : Fp12',
    Fp12.fp12_inv p beta xi_re xi_im a = Pairing.fp12_inv p a.
  Hypothesis frobenius_eq : forall a : Fp12',
    Fp12.fp12_frobenius p beta fg1 fg2 w_frob_c1 a =
    Pairing.fp12_frobenius p fg1 fg2 w_frob_c1 a.
  Hypothesis frobenius_p2_eq : forall a : Fp12',
    Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1 a =
    Pairing.fp12_frobenius_p2 p fg1_p2 fg2_p2 w_frob_p2_c1 a.

  (* ---- Binary exponentiation bridge ---- *)
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
    - reflexivity.
    - simpl. rewrite sqr_eq, mul_eq. destruct b; apply IH.
  Qed.

  Definition bedrock2_pow_Z (base : Fp12') (exp : Z) (width : nat) : Fp12' :=
    bedrock2_pow_bits_aux base (Pairing.Z_to_bits width exp)
      (Fp12.fp12_one p) false.

  Lemma pow_Z_feval : forall base exp width,
    bedrock2_pow_Z base exp width = Pairing.fp12_pow_Z p base exp width.
  Proof.
    intros. unfold bedrock2_pow_Z, Pairing.fp12_pow_Z, Pairing.fp12_pow_bits.
    f_equal. apply pow_bits_aux_feval.
  Qed.

  (* ---- Power-by-BLS-parameter bridges ---- *)
  Definition bedrock2_pow_bls_x (f : Fp12') : Fp12' :=
    bedrock2_pow_Z f Pairing.bls_x 64.

  Lemma pow_bls_x_feval : forall f : Fp12',
    bedrock2_pow_bls_x f = Pairing.fp12_pow_bls_x p f.
  Proof. intro. apply pow_Z_feval. Qed.

  Definition bedrock2_pow_bls_x_signed (f : Fp12') : Fp12' :=
    Fp12.fp12_conjugate p (bedrock2_pow_bls_x f).

  Lemma pow_bls_x_signed_feval : forall f : Fp12',
    bedrock2_pow_bls_x_signed f = Pairing.fp12_pow_bls_x_signed p f.
  Proof.
    intro f. unfold bedrock2_pow_bls_x_signed, Pairing.fp12_pow_bls_x_signed.
    rewrite conjugate_eq, pow_bls_x_feval. reflexivity.
  Qed.

  Definition bedrock2_pow_bls_x_half (f : Fp12') : Fp12' :=
    bedrock2_pow_Z f (Pairing.bls_x / 2) 63.

  Lemma pow_bls_x_half_feval : forall f : Fp12',
    bedrock2_pow_bls_x_half f = Pairing.fp12_pow_bls_x_half p f.
  Proof. intro. apply pow_Z_feval. Qed.

  Definition bedrock2_pow_bls_x_half_signed (f : Fp12') : Fp12' :=
    Fp12.fp12_conjugate p (bedrock2_pow_bls_x_half f).

  Lemma pow_bls_x_half_signed_feval : forall f : Fp12',
    bedrock2_pow_bls_x_half_signed f = Pairing.fp12_pow_bls_x_half_signed p f.
  Proof.
    intro f.
    unfold bedrock2_pow_bls_x_half_signed, Pairing.fp12_pow_bls_x_half_signed.
    rewrite conjugate_eq, pow_bls_x_half_feval. reflexivity.
  Qed.

  (* ---- DSD hard part bridge ----
     CRITICAL: Make pow-by-x functions opaque BEFORE unfolding
     final_exp_hard_dsd to prevent term explosion from concrete bit lists. *)

  Local Opaque bedrock2_pow_bls_x bedrock2_pow_bls_x_signed
    bedrock2_pow_bls_x_half bedrock2_pow_bls_x_half_signed
    bedrock2_pow_Z bedrock2_pow_bits_aux.
  Local Opaque Pairing.fp12_pow_bls_x Pairing.fp12_pow_bls_x_signed
    Pairing.fp12_pow_bls_x_half Pairing.fp12_pow_bls_x_half_signed
    Pairing.fp12_pow_Z Pairing.fp12_pow_bits Pairing.fp12_pow_bits_aux.

  Definition bedrock2_final_exp_hard_dsd (f : Fp12') : Fp12' :=
    let t0 := Fp12.fp12_sqr p beta xi_re xi_im f in
    let t1 := bedrock2_pow_bls_x_half_signed t0 in
    let t2 := Fp12.fp12_conjugate p f in
    let t1 := Fp12.fp12_mul p beta xi_re xi_im t1 t2 in
    let t2 := bedrock2_pow_bls_x_signed t1 in
    let t1 := Fp12.fp12_conjugate p t1 in
    let t1 := Fp12.fp12_mul p beta xi_re xi_im t1 t2 in
    let t2 := bedrock2_pow_bls_x_signed t1 in
    let t1 := Fp12.fp12_frobenius p beta fg1 fg2 w_frob_c1 t1 in
    let t1 := Fp12.fp12_mul p beta xi_re xi_im t1 t2 in
    let result := Fp12.fp12_mul p beta xi_re xi_im f t0 in
    let t0 := bedrock2_pow_bls_x_signed t1 in
    let t2 := bedrock2_pow_bls_x_signed t0 in
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
    unfold bedrock2_final_exp_hard_dsd, Pairing.final_exp_hard_dsd.
    rewrite sqr_eq.
    rewrite pow_bls_x_half_signed_feval.
    rewrite conjugate_eq.
    rewrite mul_eq.
    rewrite pow_bls_x_signed_feval.
    rewrite conjugate_eq.
    rewrite mul_eq.
    rewrite pow_bls_x_signed_feval.
    rewrite frobenius_eq.
    rewrite mul_eq.
    rewrite mul_eq.
    rewrite pow_bls_x_signed_feval.
    rewrite pow_bls_x_signed_feval.
    rewrite frobenius_p2_eq.
    rewrite conjugate_eq.
    rewrite mul_eq.
    rewrite mul_eq.
    rewrite mul_eq.
    reflexivity.
  Qed.

  (* ---- Full DSD final exponentiation bridge ---- *)
  Local Opaque bedrock2_final_exp_hard_dsd.
  Local Opaque Pairing.final_exp_hard_dsd.

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
    unfold bedrock2_final_exp_dsd, Pairing.final_exponentiation_dsd.
    rewrite conjugate_eq, inv_eq, mul_eq.
    rewrite frobenius_p2_eq, mul_eq.
    apply final_exp_hard_dsd_feval.
  Qed.

End DSDFinalExpFeval.

(* ================================================================ *)
(** ** Part 2: Top-level DSD pairing composition                    *)
(*                                                                   *)
(* CRITICAL: Make final_exponentiation_dsd opaque to prevent term    *)
(* explosion from the DSD sub-expressions during f_equal.            *)
(* ================================================================ *)

Local Opaque Pairing.final_exponentiation_dsd.
Local Opaque bedrock2_final_exp_dsd bedrock2_final_exp_hard_dsd
  bedrock2_pow_Z bedrock2_pow_bits_aux
  bedrock2_pow_bls_x bedrock2_pow_bls_x_signed
  bedrock2_pow_bls_x_half bedrock2_pow_bls_x_half_signed.

Section DSDPairingFeval.
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

  (* ---- Fp12 bridge hypotheses ---- *)
  Hypothesis sqr_eq : forall a : Fp12',
    Fp12.fp12_sqr p beta xi_re xi_im a = Pairing.fp12_sqr p a.
  Hypothesis mul_eq : forall a b : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im a b = Pairing.fp12_mul p a b.
  Hypothesis conjugate_eq : forall a : Fp12',
    Fp12.fp12_conjugate p a = Pairing.fp12_conjugate p a.
  Hypothesis inv_eq : forall a : Fp12',
    Fp12.fp12_inv p beta xi_re xi_im a = Pairing.fp12_inv p a.
  Hypothesis frobenius_eq : forall a : Fp12',
    Fp12.fp12_frobenius p beta fg1 fg2 w_frob_c1 a =
    Pairing.fp12_frobenius p fg1 fg2 w_frob_c1 a.
  Hypothesis frobenius_p2_eq : forall a : Fp12',
    Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1 a =
    Pairing.fp12_frobenius_p2 p fg1_p2 fg2_p2 w_frob_p2_c1 a.

  (* ---- Miller loop bridge hypothesis ----
     Rather than importing BLS12_Fp12Feval (which pulls in heavy bedrock2
     dependencies and risks OOM), we state the Miller loop result as a
     hypothesis.  It can be discharged by miller_loop_feval_correct from
     BLS12_Fp12Feval at instantiation time. *)
  Variable bedrock2_miller : Pairing.G1Affine p -> Pairing.G2Affine p -> Fp12'.
  Hypothesis miller_feval :
    forall (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p),
      Pairing.g1_infinity p P = false ->
      Pairing.g2_infinity p Q = false ->
      bedrock2_miller P Q = Pairing.miller_loop p P Q.

  (** Bedrock2 DSD pairing: miller loop + DSD final exponentiation. *)
  Definition bedrock2_pairing_dsd (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p)
    : Fp12' :=
    bedrock2_final_exp_dsd p beta xi_re xi_im
      fg1 fg2 fg1_p2 fg2_p2 w_frob_c1 w_frob_p2_c1
      (bedrock2_miller P Q).

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
    rewrite (final_exp_dsd_feval_correct p beta xi_re xi_im
               fg1 fg2 fg1_p2 fg2_p2 w_frob_c1 w_frob_p2_c1);
      try assumption.
    rewrite (miller_feval P Q Hp Hq).
    reflexivity.
  Qed.

End DSDPairingFeval.
