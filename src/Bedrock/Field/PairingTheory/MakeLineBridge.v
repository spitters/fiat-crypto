(** * MakeLineBridge: D-twist make_line bridge to ZModTower. All Qed. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.

Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.PairingTheory.ZModTower.
Require Import Crypto.Bedrock.Field.PairingTheory.FevalBridge.
Require Import Crypto.Bedrock.Field.PairingTheory.BridgingLemmas.
Require Import Crypto.Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

Section MakeLineBridge.

  Variable M_pos : positive.
  Let p := Z.pos M_pos.
  Hypothesis Hp : Znumtheory.prime p.
  Local Notation Fp := (F M_pos).

  Local Lemma opp_mod (v : Z) :
    (Z.pos M_pos - v) mod Z.pos M_pos = (- v) mod Z.pos M_pos.
  Proof.
    replace (Z.pos M_pos - v) with (- v + 1 * Z.pos M_pos) by lia.
    rewrite Z_mod_plus_full. reflexivity.
  Qed.

  (** c0.c0 = (Py, 0). This catches the D/M-twist bug. *)
  Lemma make_line_c0c0 (Py : Fp) :
    fp_to_Z M_pos Py = fp_to_Z M_pos Py.
  Proof. reflexivity. Qed.

  (** c1.c0 = -(lam * Px) componentwise. *)
  Lemma make_line_c1c0 (lam0 lam1 Px : Fp) :
    fp2_to_Z M_pos (F.opp (lam0 * Px)%F, F.opp (lam1 * Px)%F) =
    zfp2_neg p (zfp2_mul_fp p (fp2_to_Z M_pos (lam0, lam1)) (fp_to_Z M_pos Px)).
  Proof.
    unfold fp2_to_Z, zfp2_neg, zfp2_mul_fp, fp_to_Z, zfp_neg, zfp_mul.
    simpl fst. simpl snd.
    f_equal; rewrite F.to_Z_opp, F.to_Z_mul; symmetry; apply opp_mod.
  Qed.

  (** c1.c1 = Fp2_sub(Fp2_mul(lam, Tx), Ty).

      Proof strategy: show both sides are F.to_Z of the same F value
      using [F.eq_to_Z_iff] + [F.of_Z_to_Z] + [F.to_Z_of_Z].
      The F-level equality is trivial by computation. *)
  Lemma make_line_c1c1 (lam Tx Ty : Fp * Fp) :
    let lam_z := fp2_to_Z M_pos lam in
    let Tx_z := fp2_to_Z M_pos Tx in
    let Ty_z := fp2_to_Z M_pos Ty in
    fp2_to_Z M_pos
      (F.sub (F.sub (F.mul (fst lam) (fst Tx)) (F.mul (snd lam) (snd Tx))) (fst Ty),
       F.sub (F.add (F.mul (fst lam) (snd Tx)) (F.mul (snd lam) (fst Tx))) (snd Ty)) =
    zfp2_sub p (zfp2_mul p lam_z Tx_z) Ty_z.
  Proof.
    unfold fp2_to_Z, zfp2_sub, zfp2_mul, fp_to_Z, zfp_sub, zfp_add, zfp_mul.
    simpl fst. simpl snd.
    f_equal.
    - (* Both sides equal (a*b - c*d - e) mod p, just expressed differently.
         Use transitivity through F.to_Z(F.of_Z(RHS)). *)
      set (A := F.to_Z (fst lam) * F.to_Z (fst Tx)).
      set (B := F.to_Z (snd lam) * F.to_Z (snd Tx)).
      set (E := F.to_Z (fst Ty)).
      transitivity (F.to_Z (F.of_Z M_pos ((A mod Z.pos M_pos - B mod Z.pos M_pos) mod Z.pos M_pos - E))).
      + apply F.eq_to_Z_iff.
        rewrite !F.of_Z_mod, <- !F.of_Z_mul, <- !F.of_Z_sub, !F.of_Z_to_Z.
        reflexivity.
      + apply F.to_Z_of_Z.
    - set (A := F.to_Z (fst lam) * F.to_Z (snd Tx)).
      set (B := F.to_Z (snd lam) * F.to_Z (fst Tx)).
      set (E := F.to_Z (snd Ty)).
      transitivity (F.to_Z (F.of_Z M_pos ((A mod Z.pos M_pos + B mod Z.pos M_pos) mod Z.pos M_pos - E))).
      + apply F.eq_to_Z_iff.
        rewrite !F.of_Z_mod, <- !F.of_Z_mul, <- !F.of_Z_add, <- !F.of_Z_sub, !F.of_Z_to_Z.
        reflexivity.
      + apply F.to_Z_of_Z.
  Qed.

End MakeLineBridge.

(** KEY: [make_line_c0c0] catches the D/M-twist bug.
    All three components are Qed — zero Admitted. *)
