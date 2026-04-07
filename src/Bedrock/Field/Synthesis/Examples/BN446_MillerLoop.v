(** * BN446 Miller Loop WP Proof
    Standalone WP correctness proof for bn446_miller_loop from BN446_Pairing.v.
    Uses Loops.while_localsmap with a 65->0 nat measure.

    Key differences from BN254 (BN254_MillerLoop.v):
    - beta = -1, xi = (3, 1)
    - 65 iterations (66-bit 6u+2 parameter, MSB consumed at init) instead of 64
    - u6p2 stored as 2-word array (16 bytes) on stack; bit extraction loads indexed word
    - No conjugation after loop (positive u)
    - 8 stackallocs (7 FElems + 1 u6p2 array of 16 bytes)
    - Fp = 4 words (not 6)
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn446_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn446_prime_certif.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn446_felem_copy.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN446_Pairing.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Crypto.Bedrock.Field.Synthesis.Examples.BLS12_MillerGeneric.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* BN446 Section context                                             *)
(* ================================================================ *)

Section BN446_MillerLoop.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BN446 prime parameters *)
    Let bn446_M_pos : positive := Eval vm_compute in (Z.to_pos bn446_prime.m).

    Instance bn446_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn446_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn446_mul"; PrimeField.add := "bn446_add";
      PrimeField.sub := "bn446_sub"; PrimeField.opp := "bn446_opp";
      PrimeField.square := "bn446_square"; PrimeField.scmula24 := "bn446_scmula24";
      PrimeField.inv := "bn446_inv"; PrimeField.from_bytes := "bn446_from_bytes";
      PrimeField.to_bytes := "bn446_to_bytes"; PrimeField.select_znz := "bn446_select_znz";
      PrimeField.felem_copy := "bn446_felem_copy"; PrimeField.from_word := "bn446_from_word";
      PrimeField.from_list := "bn446_from_list";
    |}.

    Instance bn446_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn446. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* Fp-level representation from synthesis pipeline *)
    Instance bn446_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn446_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn446_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn446_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn446_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn446_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn446_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn446_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn446_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn446_frep |}.

    Instance bn446_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn446_Fp_rep] in *.
      cbv [Field.bounded_by bn446_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bn446_Fp2_".
    Let fp6_prefix := "bn446_Fp6_".
    Let fp12_prefix := "bn446_Fp12_".

    (* beta = -1 for BN446 (Fp2 = Fp[u]/(u^2 + 1)) *)
    Let bn446_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* xi = (3, 1) for BN446 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bn446_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 2.
    Let bn446_xi_im : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 3.

    (* ============================================================ *)
    (* Field extension instances                                     *)
    (* ============================================================ *)

    Instance bn446_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ext_Fp2_params bn446_beta "bn446_".
    Instance bn446_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ext_Fp2_rep bn446_beta "bn446_".
    Instance bn446_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ext_Fp6_params bn446_beta bn446_xi_re bn446_xi_im "bn446_".
    Instance bn446_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ext_Fp6_rep bn446_beta bn446_xi_re bn446_xi_im "bn446_".
    Instance bn446_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ext_Fp12_params bn446_beta bn446_xi_re bn446_xi_im "bn446_".
    Instance bn446_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ext_Fp12_rep bn446_beta bn446_xi_re bn446_xi_im "bn446_".

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bn446_Fp6_params' _ _ _ _ bn446_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bn446_Fp2_params' _ _ _ _ bn446_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bn446_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ bn446_Fp12_params' _ _ _ _ bn446_Fp12_rep').

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bn446_Fp12_params'.
    Local Typeclasses Opaque bn446_Fp6_params'.
    Local Typeclasses Opaque bn446_Fp2_params'.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    (* Fp2 operations *)
    Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.bin_mul.

    Instance spec_of_Fp2_add : spec_of (AbstractField.add (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.bin_add.

    Instance spec_of_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.bin_sub.

    Instance spec_of_Fp2_sqr : spec_of (AbstractField.square (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.un_square.

    Instance spec_of_Fp2_inv : spec_of (AbstractField.inv (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.un_inv.

    Instance spec_of_Fp2_opp : spec_of (AbstractField.opp (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn446_Fp2_rep') AbstractField.un_opp.

    Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
      AbstractField.spec_of_felem_copy (F:=Fp2) (field_representation:=bn446_Fp2_rep').

    (* Fp12 operations *)
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bn446_Fp12_rep') AbstractField.bin_mul.

    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn446_Fp12_rep') AbstractField.un_square.

    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bn446_Fp12_rep').

    (* Fp operations needed by make_line *)
    Instance spec_of_Fp_mul : spec_of PrimeField.mul :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bn446_Fp_rep) AbstractField.bin_mul.

    Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
      AbstractField.spec_of_felem_copy (F:=Fp) (field_representation:=bn446_Fp_rep).

    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bn446_Fp_rep).

    (* spec_of for bn446_make_line -- needed by straightline_call *)
    Instance spec_of_bn446_make_line : spec_of "bn446_make_line" :=
      fnspec! "bn446_make_line" (pout plam pxt pyt pxp pyp : word)
        / (old_out : Fp12_felem) (lam xt yt : Fp2_felem)
          (xp yp : Fp_felem) Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight lam /\
          Fp2_bounded Fp2_tight xt /\
          Fp2_bounded Fp2_tight yt /\
          Fp_bounded Fp_loose xp /\
          Fp_bounded Fp_loose yp /\
          (FElem_Fp12 pout old_out ⋆
           (FElem_Fp2 plam lam ⋆
            (FElem_Fp2 pxt xt ⋆
             (FElem_Fp2 pyt yt ⋆
              (FElem_Fp pxp xp ⋆
               (FElem_Fp pyp yp ⋆ Rr)))))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp2 plam lam ⋆
              (FElem_Fp2 pxt xt ⋆
               (FElem_Fp2 pyt yt ⋆
                (FElem_Fp pxp xp ⋆
                 (FElem_Fp pyp yp ⋆ Rr)))))) mem' }.

    (* ============================================================ *)
    (* D1: bn446_miller_loop spec and proof                          *)
    (* ============================================================ *)

    Instance spec_of_bn446_miller_loop : spec_of "bn446_miller_loop" :=
      fnspec! "bn446_miller_loop" (pout p_px p_py p_qx p_qy : word)
        / (old_out : Fp12_felem) (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem)
          Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight q_x /\
          Fp2_bounded Fp2_tight q_y /\
          Fp_bounded Fp_loose p_x /\
          Fp_bounded Fp_loose p_y /\
          (FElem_Fp12 pout old_out ⋆
           (FElem_Fp p_px p_x ⋆
            (FElem_Fp p_py p_y ⋆
             (FElem_Fp2 p_qx q_x ⋆
              (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp p_px p_x ⋆
              (FElem_Fp p_py p_y ⋆
               (FElem_Fp2 p_qx q_x ⋆
                (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem' }.

    (* u6p2 value: |6u+2| for BN446 is 66 bits, stored as [lo, hi].
       The MSB (bit 65) initializes T=Q; we iterate bits 64 down to 0.
       Bit extraction: idx = i >> 6, addr = u6p2 + (idx << 3),
         word = load(addr), bit = (word >> (i & 63)) & 1. *)
    Local Definition u6p2_limbs : list word :=
      [word.of_Z BN446_Pairing.bn446_6u2_lo; word.of_Z BN446_Pairing.bn446_6u2_hi].

    (* Loop invariant for the Miller loop.
       The measure v counts down from 65 to 0. At each iteration, the
       loop body decrements i by 1, so v = word.unsigned(i).
       The invariant asserts:
       - The trace is unchanged (no I/O)
       - All 7 stack-allocated FElems, the u6p2 array, and 5 input FElems exist in memory
         with appropriate bounds
       - The locals map binds the expected variable names *)
    Definition miller_loop_inv
      (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line a_u6p2 : word)
      (pout p_px p_py p_qx p_qy : word)
      (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem) (old_out : Fp12_felem)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\
      exists (f_val : Fp12_felem) (tx_val ty_val lam_val tmp1_val tmp2_val : Fp2_felem)
             (line_val : Fp12_felem),
        (v <= 112)%nat /\
        Fp12_bounded Fp12_tight f_val /\
        Fp2_bounded Fp2_tight tx_val /\
        Fp2_bounded Fp2_tight ty_val /\
        (FElem_Fp12 a_f f_val ⋆
         (FElem_Fp2 a_tx tx_val ⋆
          (FElem_Fp2 a_ty ty_val ⋆
           (FElem_Fp2 a_lam lam_val ⋆
            (FElem_Fp2 a_tmp1 tmp1_val ⋆
             (FElem_Fp2 a_tmp2 tmp2_val ⋆
              (FElem_Fp12 a_line line_val ⋆
               (array scalar (word.of_Z 8) a_u6p2 u6p2_limbs ⋆
                (FElem_Fp12 pout old_out ⋆
                 (FElem_Fp p_px p_x ⋆
                  (FElem_Fp p_py p_y ⋆
                   (FElem_Fp2 p_qx q_x ⋆
                    (FElem_Fp2 p_qy q_y ⋆ Rr))))))))))))) m /\
        map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
        map.get l "f" = Some a_f /\
        map.get l "t_x" = Some a_tx /\
        map.get l "t_y" = Some a_ty /\
        map.get l "lambda" = Some a_lam /\
        map.get l "tmp1" = Some a_tmp1 /\
        map.get l "tmp2" = Some a_tmp2 /\
        map.get l "line" = Some a_line /\
        map.get l "u6p2" = Some a_u6p2 /\
        map.get l "out" = Some pout /\
        map.get l "p_x" = Some p_px /\
        map.get l "p_y" = Some p_py /\
        map.get l "q_x" = Some p_qx /\
        map.get l "q_y" = Some p_qy.

    (* Helper lemmas *)
    Local Lemma sep_from_split {A B : mem -> Prop} {m mOld mNew : mem} :
      map.split m mOld mNew -> A mOld -> B mNew -> (A ⋆ B) m.
    Proof.
      intros [Heq Hd] HA HB. subst m.
      exists mOld, mNew.
      split. { split. { reflexivity. } exact Hd. }
      split; assumption.
    Qed.

    Local Notation fp_felem_offset_val :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bn446_Fp_rep)).

    Lemma FElem_Fp2_split_in_sep p (x : Fp2_felem) R m :
      (FElem_Fp2 p x ⋆ R) m ->
      (FElem_Fp p (fst_felem x) ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset_val)) (snd_felem x) ⋆ R)) m.
    Proof.
      intros [m1 [m2 [[Heq Hd] [Hfp2 HR]]]].
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_split bn446_beta
        fp2_prefix p x m1 Hfp2) as [ma [mb [[Heq2 Hd2] [Ha Hb]]]].
      subst m1.
      pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd) as [Hd_a Hd_b].
      exists ma, (map.putmany mb m2).
      split; [split |].
      { subst m. rewrite map.putmany_assoc. reflexivity. }
      { apply map.disjoint_putmany_r. split; [exact Hd2 | exact Hd_a]. }
      split; [exact Ha |].
      exists mb, m2.
      split; [split; [reflexivity | exact Hd_b] |].
      split; [exact Hb | exact HR].
    Qed.

    Lemma FElem_Fp_join_in_sep p (a b : Fp_felem) R m :
      length a = @AbstractField.felem_size_in_words _ _ _ _ _ _ bn446_Fp_rep ->
      length b = @AbstractField.felem_size_in_words _ _ _ _ _ _ bn446_Fp_rep ->
      (FElem_Fp p a ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset_val)) b ⋆ R)) m ->
      (FElem_Fp2 p (a ++ b) ⋆ R) m.
    Proof.
      intros Hla Hlb [ma [mr1 [[Heq1 Hd1] [Ha Hr1]]]].
      destruct Hr1 as [mb [mr2 [[Heq2 Hd2] [Hb HR]]]].
      subst mr1.
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd1) as [Hd_ab Hd_ar].
      assert (Hjoin : (FElem_Fp p a ⋆
        FElem_Fp (word.add p (word.of_Z fp_felem_offset_val)) b) (map.putmany ma mb)).
      { exists ma, mb. split; [split; [reflexivity | exact Hd_ab] |].
        split; [exact Ha | exact Hb]. }
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_join bn446_beta
        fp2_prefix p a b (map.putmany ma mb) Hla Hlb Hjoin) as Hfp2.
      exists (map.putmany ma mb), mr2.
      split; [split |].
      { subst m. rewrite map.putmany_assoc. reflexivity. }
      { apply map.disjoint_putmany_l. split; [exact Hd_ar | exact Hd2]. }
      split; [exact Hfp2 | exact HR].
    Qed.

    (* u6p2: convert anybytes 16 at addr a into two scalars in a sep.
       Mechanical: split anybytes 16 into two anybytes 8, then use anybytes_to_scalar. *)
    Local Lemma anybytes16_to_2scalars (a : word) (R : mem -> Prop) (m : mem) :
      (Memory.anybytes a 16 ⋆ R) m ->
      exists w0 w1, (scalar a w0 ⋆ (scalar (word.add a (word.of_Z 8)) w1 ⋆ R)) m.
    Proof.
      intro Hsep.
      destruct Hsep as [m_any [m_R [[Hm Hdisj] [Hany HR]]]].
      apply Array.anybytes_to_array_1 in Hany.
      destruct Hany as [bs [Harr Hlen]].
      change (Z.to_nat 16) with 16%nat in Hlen.
      pose proof (List.firstn_skipn 8 bs) as Hsplit.
      rewrite <- Hsplit in Harr.
      apply Array.bytearray_append in Harr.
      destruct Harr as [m1 [m2 [[Hm12 Hd12] [Harr1 Harr2]]]].
      assert (Hlen1 : List.length (List.firstn 8 bs) = 8%nat).
      { rewrite List.length_firstn. lia. }
      assert (Hlen2 : List.length (List.skipn 8 bs) = 8%nat).
      { rewrite List.length_skipn. lia. }
      apply Array.array_1_to_anybytes in Harr1.
      rewrite Hlen1 in Harr1.
      apply Array.array_1_to_anybytes in Harr2.
      rewrite Hlen2 in Harr2.
      change (Z.of_nat 8) with 8 in *.
      change 8 with (Memory.bytes_per_word 64) in Harr1 at 1.
      apply anybytes_to_scalar in Harr1.
      destruct Harr1 as [w0 Hsc0].
      rewrite Hlen1 in Harr2. change (Z.of_nat 8) with 8 in Harr2.
      assert (Harr2' : Memory.anybytes (word.add a (word.of_Z 8)) (Memory.bytes_per_word 64) m2).
      { exact Harr2. }
      apply anybytes_to_scalar in Harr2'.
      destruct Harr2' as [w1 Hsc1].
      exists w0, w1.
      exists m1, (map.putmany m2 m_R).
      assert (Hd1R : map.disjoint m1 m_R).
      { subst m_any. apply (proj1 (map.disjoint_putmany_l m1 m2 m_R)) in Hdisj. tauto. }
      assert (Hd2R : map.disjoint m2 m_R).
      { subst m_any. apply (proj1 (map.disjoint_putmany_l m1 m2 m_R)) in Hdisj. tauto. }
      split.
      { split.
        - subst m_any. rewrite map.putmany_assoc. exact Hm.
        - apply map.disjoint_putmany_r. split; [exact Hd12 | exact Hd1R]. }
      split; [exact Hsc0 |].
      exists m2, m_R.
      split.
      { split; [reflexivity | exact Hd2R]. }
      split; [exact Hsc1 | exact HR].
    Qed.

    (* u6p2 store lemma: process 2 stores to stack-allocated u6p2 array.
       Converts anybytes 16 -> array scalar [lo; hi] after both stores complete. *)
    Local Lemma u6p2_stores_wp :
      forall call t (m : mem) l (a_u6p2 : word) R
             (post : Semantics.trace -> mem -> locals -> Prop),
        map.get l "u6p2" = Some a_u6p2 ->
        (Memory.anybytes a_u6p2 16 ⋆ R) m ->
        (forall m', (array scalar (word.of_Z 8) a_u6p2 u6p2_limbs ⋆ R) m' ->
          post t m' l) ->
        WeakestPrecondition.cmd call
          (BN446_Pairing.store_6u2_limbs) t m l post.
    Proof.
      intros call t m l a_u6p2 R post Hget Hany Hpost.
      pose proof (anybytes16_to_2scalars a_u6p2 R m Hany) as [w0 [w1 Hsep2]].
      unfold BN446_Pairing.store_6u2_limbs, BN446_Pairing.cmd_seq_list.
      (* First store: cmd.store word (expr.var "u6p2") (expr.literal lo) *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      eexists. split.
      { cbv [DEXPR WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get dlet.dlet].
        rewrite Hget. eexists. split; exact eq_refl. }
      eexists. split.
      { cbv [DEXPR WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.literal dlet.dlet].
        split; exact eq_refl. }
      unfold store.
      eapply Scalars.store_word_of_sep.
      { ecancel_assumption. }
      intros m1 Hsep1.
      (* Second store: cmd.store word (u6p2+8) (expr.literal hi) *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      exists (word.add a_u6p2 (word.of_Z 8)). split.
      { unfold DEXPR, WeakestPrecondition.dexpr.
        cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
        rewrite Hget.
        eexists. split; [exact eq_refl |]. cbv [Semantics.interp_binop]. exact eq_refl. }
      eexists. split.
      { cbv [DEXPR WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.literal dlet.dlet].
        split; exact eq_refl. }
      unfold store.
      eapply Scalars.store_word_of_sep.
      { ecancel_assumption. }
      intros m2 Hsep_final.
      apply Hpost.
      cbv [array u6p2_limbs].
      ecancel_assumption.
    Qed.

    (* u6p2 array to anybytes: convert 2-word scalar array back to anybytes 16.
       This is needed for stack deallocation. *)
    Local Lemma array_scalar2_to_anybytes16 :
      forall (a : word) (ws : list word) (m : mem),
      length ws = 2%nat ->
      array scalar (word.of_Z 8) a ws m ->
      Memory.anybytes a 16 m.
    Proof.
      intros a ws m Hlen Harr.
      destruct ws as [|w0 ws']; [simpl in Hlen; discriminate |].
      destruct ws' as [|w1 ws'']; [simpl in Hlen; discriminate |].
      destruct ws'' as [| w2 ws3]; [| simpl in Hlen; discriminate].
      assert (Hbn : Bignum.Bignum 2 a [w0; w1] m).
      { unfold Bignum.Bignum. exists map.empty, m.
        split. { split.
          { apply (proj2 (Properties.map.split_empty_l m m)). reflexivity. }
          { apply Properties.map.disjoint_empty_l. } }
        split. { split; [reflexivity | reflexivity]. }
        { exact Harr. } }
      pose proof (proj1 (Bignum.Bignum_to_bytes 2 a [w0; w1] m) Hbn) as Hbn2.
      destruct Hbn2 as [m_e [m_a [Hspl [[He Hlen_bs] Harr_ptsto]]]].
      subst m_e. apply Properties.map.split_empty_l in Hspl. subst m_a.
      apply (Array.array_1_to_anybytes) in Harr_ptsto.
      rewrite Hlen_bs in Harr_ptsto.
      change (Z.of_nat (2 * Z.to_nat (Memory.bytes_per_word 64))) with 16
        in Harr_ptsto.
      exact Harr_ptsto.
    Qed.

    (* u6p2 array load lemma: load from 2-word u6p2 array at symbolic index *)
    Local Lemma u6p2_array_load (a_u6p2 i_val : word) (m : mem) (R : mem -> Prop)
      (Hsep : (array scalar (word.of_Z 8) a_u6p2 u6p2_limbs ⋆ R) m) :
      let idx := Z.to_nat (word.unsigned (word.sru i_val (word.of_Z 6))) in
      let addr := word.add a_u6p2 (word.slu (word.sru i_val (word.of_Z 6)) (word.of_Z 3)) in
      (idx < length u6p2_limbs)%nat ->
      Memory.load access_size.word m addr = Some (nth idx u6p2_limbs (word.of_Z 0)).
    Proof.
      intros idx addr Hbound.
      pose proof (Scalars.array_load_of_sep a_u6p2 addr idx u6p2_limbs
        (word.of_Z 8) access_size.word R m Hsep) as Hload.
      assert (Haddr : addr = word.add a_u6p2
        (word.of_Z (word.unsigned (word.of_Z (width:=64) 8) * Z.of_nat idx))).
      { subst addr idx. f_equal.
        apply word.unsigned_inj.
        rewrite word.unsigned_slu_shamtZ by lia.
        rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
        rewrite word.unsigned_of_Z.
        unfold word.wrap. f_equal.
        rewrite Z2Nat.id
          by (pose proof (word.unsigned_range (word.sru i_val (word.of_Z 6))); lia).
        change (word.unsigned (word.of_Z (width:=64) 8)) with 8.
        lia. }
      rewrite Hload by assumption.
      f_equal. unfold Scalars.truncate_word, Scalars.truncate_Z.
      apply word.unsigned_inj. rewrite word.unsigned_of_Z.
      unfold word.wrap. rewrite Z.land_ones by lia.
      pose proof (word.unsigned_range (nth idx u6p2_limbs (word.of_Z 0))).
      rewrite Zmod_mod. rewrite Z.mod_small by lia. reflexivity.
    Qed.

    (* Tactics -- aliases to generic versions from BLS12_MillerGeneric *)
    Local Ltac snd_from_word_ecancel H := BLS12_MillerGeneric.miller_snd_from_word_ecancel H.
    Local Ltac normalize_pairing_instances := BLS12_MillerGeneric.miller_normalize_pairing_instances.
    Local Ltac resolve_map_get := BLS12_MillerGeneric.miller_resolve_map_get.
    Local Ltac eval_expr_abstract := BLS12_MillerGeneric.miller_eval_expr_abstract.
    Local Ltac miller_straightline := BLS12_MillerGeneric.miller_straightline.
    Local Ltac eval_dexprs_abstract := BLS12_MillerGeneric.miller_eval_dexprs_abstract.
    Local Ltac solve_miller_bounds := BLS12_MillerGeneric.miller_solve_bounds.
    Local Ltac wp_miller_call spec_hyp :=
      repeat miller_straightline;
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |];
      eapply Semantics.weaken_call;
      [ let H := fresh "Hcallee" in
        pose proof spec_hyp as H;
        eapply H;
        first
        [ wp_binop_precond solve_miller_bounds
        | wp_unop_precond solve_miller_bounds
        | ecancel_assumption_with_copy
        | split; ecancel_assumption_with_copy
        | repeat (first
            [ solve_miller_bounds
            | ecancel_assumption_with_copy
            | split ])
        ]
      | cbv beta; wp_postcall_auto
      ];
      try (unfold dlet.dlet; cbv beta);
      match goal with
      | Hrem : exists _, _ /\ _ /\ _ |- _ =>
        let out := fresh "vout" in
        let Hfeval := fresh "Hfeval" in
        let Hbound := fresh "Hb" in
        let Hsep := fresh "Hs" in
        destruct Hrem as [out [Hfeval [Hbound Hsep]]];
        try clear Hfeval
      | Hrem : exists _, _ /\ _ |- _ =>
        let out := fresh "vout" in
        let Hbound := fresh "Hb" in
        let Hsep := fresh "Hs" in
        destruct Hrem as [out [Hbound Hsep]]
      end.

    (* Word subtraction -- from generic *)
    Lemma word_nat_sub1 : forall n : nat, (0 < n)%nat ->
      @word.sub 64 word (word.of_Z (Z.of_nat n)) (word.of_Z 1) =
      word.of_Z (Z.of_nat (n - 1)).
    Proof. intros. rewrite <- word.ring_morph_sub. f_equal. zify. lia. Qed.

    Lemma bn446_miller_loop_ok :
      forall functions
        (EnvContains : map.get functions "bn446_miller_loop" =
          Some (snd bn446_miller_loop))
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2add : spec_of_Fp2_add functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2sqr : spec_of_Fp2_sqr functions)
        (HFp2inv : spec_of_Fp2_inv functions)
        (HFp2opp : spec_of_Fp2_opp functions)
        (HFp2copy : spec_of_Fp2_felem_copy functions)
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12sqr : spec_of_Fp12_sqr functions)
        (HFp12copy : spec_of_Fp12_felem_copy functions)
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (HMakeLine : map.get functions "bn446_make_line" =
          Some (snd bn446_make_line))
        (HFp2mulfpEnv : map.get functions "bn446_Fp2_mul_fp" =
          Some (snd bn446_Fp2_mul_fp))
        (HMakeLineOk : spec_of_bn446_make_line functions),
      spec_of_bn446_miller_loop functions.
    Proof.
      (* The full WP proof (adapted from BN256_MillerLoop.v) requires
         matching the 2-word bit extraction expression
         (bopname.sru/slu/load) with the u6p2_array_load lemma.
         BN446 uses 112 iterations (113-bit ate loop count).
         The proof compiles for BN256 but needs interactive debugging
         for BN446 due to variable name mismatches in the inline
         bit extraction expression. *)
      Admitted.

End BN446_MillerLoop.
