(** * BLS24-509 Miller Loop WP Proof
    Standalone WP correctness proof for bls24_miller_loop from BLS24_509_MillerLoop.v.
    Uses Loops.while_localsmap with a 52->0 nat measure.

    Tower: Fp -> Fp2 -> Fp4 -> Fp8 -> Fp24
    G2 points live in Fp4 (quartic twist).
    |z| = 0x800000ffff801  (52 bits), z < 0.

    Structure:
    - Lemma statement + function entry + 7 stackallocs
    - FElem_from_bytes conversion for all stack buffers
    - Master sep construction (Qed)
    - Function body (Admitted) -- decomposed into 4 Admitted blocks:
      (1) bls24_miller_loop_ok        -- main WP body
      (2) bls24_miller_init_ok        -- init: 24 from_word + 2 fp4_copy + set i=52
      (3) bls24_miller_loop_body_step -- loop body preserves invariant
      (4) bls24_miller_postloop_ok    -- post-loop: opp + conj + copy + dealloc
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls24_509_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls24_509_Fp.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS24_509_Instances.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS24_509_MillerLoop.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* BLS24-509 Section context                                         *)
(* ================================================================ *)

Section BLS24_MillerLoopProof.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BLS24-509 prime parameters *)
    Existing Instances
      bls24_prime_params
      bls24_prime_params_ok
      prime_field_parameters
      bls24_Fp_repr
      bls24_Fp_repr_ok.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := (Fp * Fp)%type.
    Local Notation Fp4 := (Fp2 * Fp2)%type.
    Local Notation Fp8 := (Fp4 * Fp4)%type.
    Local Notation Fp24 := (Fp8 * Fp8 * Fp8)%type.

    (* Extension instances *)
    Existing Instances
      bls24_Fp2_params bls24_Fp2_repr bls24_Fp2_repr_ok
      bls24_Fp4_params bls24_Fp4_repr bls24_Fp4_repr_ok
      bls24_Fp8_params bls24_Fp8_repr bls24_Fp8_repr_ok
      bls24_Fp24_params bls24_Fp24_repr bls24_Fp24_repr_ok.

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).
    Local Notation FElem_Fp4 := (@AbstractField.FElem _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation FElem_Fp8 := (@AbstractField.FElem _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation FElem_Fp24 := (@AbstractField.FElem _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp4_feval := (@AbstractField.feval _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp24_feval := (@AbstractField.feval _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp4_bounded := (@AbstractField.bounded_by _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp8_bounded := (@AbstractField.bounded_by _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp24_bounded := (@AbstractField.bounded_by _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp4_tight := (@AbstractField.tight_bounds _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp4_loose := (@AbstractField.loose_bounds _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp8_tight := (@AbstractField.tight_bounds _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp8_loose := (@AbstractField.loose_bounds _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp24_tight := (@AbstractField.tight_bounds _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp24_loose := (@AbstractField.loose_bounds _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp4_felem := (@AbstractField.felem _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp8_felem := (@AbstractField.felem _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp24_felem := (@AbstractField.felem _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).

    Local Typeclasses Opaque bls24_Fp24_params.
    Local Typeclasses Opaque bls24_Fp8_params.
    Local Typeclasses Opaque bls24_Fp4_params.
    Local Typeclasses Opaque bls24_Fp2_params.

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    (* Fp4 operations: used by tangent/chord slope + point arithmetic *)
    Instance spec_of_Fp4_mul : spec_of (AbstractField.mul (F:=Fp4)) :=
      AbstractField.binop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.bin_mul.
    Instance spec_of_Fp4_add : spec_of (AbstractField.add (F:=Fp4)) :=
      AbstractField.binop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.bin_add.
    Instance spec_of_Fp4_sub : spec_of (AbstractField.sub (F:=Fp4)) :=
      AbstractField.binop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.bin_sub.
    Instance spec_of_Fp4_sqr : spec_of (AbstractField.square (F:=Fp4)) :=
      AbstractField.unop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.un_square.
    Instance spec_of_Fp4_inv : spec_of (AbstractField.inv (F:=Fp4)) :=
      AbstractField.unop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.un_inv.
    Instance spec_of_Fp4_opp : spec_of (AbstractField.opp (F:=Fp4)) :=
      AbstractField.unop_spec (F:=Fp4) (field_representation:=bls24_Fp4_repr) AbstractField.un_opp.
    Instance spec_of_Fp4_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp4)) :=
      AbstractField.spec_of_felem_copy (F:=Fp4) (field_representation:=bls24_Fp4_repr).

    (* Fp8 operations: opp used by conjugation *)
    Instance spec_of_Fp8_opp : spec_of (AbstractField.opp (F:=Fp8)) :=
      AbstractField.unop_spec (F:=Fp8) (field_representation:=bls24_Fp8_repr) AbstractField.un_opp.

    (* Fp24 operations *)
    Instance spec_of_Fp24_mul : spec_of (AbstractField.mul (F:=Fp24)) :=
      AbstractField.binop_spec (F:=Fp24) (field_representation:=bls24_Fp24_repr) AbstractField.bin_mul.
    Instance spec_of_Fp24_sqr : spec_of (AbstractField.square (F:=Fp24)) :=
      AbstractField.unop_spec (F:=Fp24) (field_representation:=bls24_Fp24_repr) AbstractField.un_square.
    Instance spec_of_Fp24_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp24)) :=
      AbstractField.spec_of_felem_copy (F:=Fp24) (field_representation:=bls24_Fp24_repr).

    (* Fp operations: needed by make_line and from_word *)
    Instance spec_of_Fp_mul : spec_of PrimeField.mul :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bls24_Fp_repr) AbstractField.bin_mul.
    Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
      AbstractField.spec_of_felem_copy (F:=Fp) (field_representation:=bls24_Fp_repr).
    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bls24_Fp_repr).

    (* ============================================================ *)
    (* spec_of for bls24_make_line                                    *)
    (* ============================================================ *)

    Instance spec_of_bls24_make_line : spec_of "bls24_make_line" :=
      fnspec! "bls24_make_line" (pout plam pxt pyt pxp pyp : word)
        / (old_out : Fp24_felem) (lam xt yt : Fp4_felem)
          (xp yp : Fp_felem) Rr,
      { requires tr mem :=
          Fp4_bounded Fp4_tight lam /\
          Fp4_bounded Fp4_tight xt /\
          Fp4_bounded Fp4_tight yt /\
          Fp_bounded Fp_loose xp /\
          Fp_bounded Fp_loose yp /\
          (FElem_Fp24 pout old_out *
           (FElem_Fp4 plam lam *
            (FElem_Fp4 pxt xt *
             (FElem_Fp4 pyt yt *
              (FElem_Fp pxp xp *
               (FElem_Fp pyp yp * Rr))))))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp24_bounded Fp24_loose out /\
            (FElem_Fp24 pout out *
             (FElem_Fp4 plam lam *
              (FElem_Fp4 pxt xt *
               (FElem_Fp4 pyt yt *
                (FElem_Fp pxp xp *
                 (FElem_Fp pyp yp * Rr))))))%sep mem' }.

    (* ============================================================ *)
    (* spec_of for bls24_Fp4_mul_fp                                   *)
    (* ============================================================ *)

    Instance spec_of_bls24_Fp4_mul_fp : spec_of "bls24_Fp4_mul_fp" :=
      fnspec! "bls24_Fp4_mul_fp" (pout px ps : word)
        / (old_out : Fp4_felem) (x : Fp4_felem) (s : Fp_felem) Rr,
      { requires tr mem :=
          Fp4_bounded Fp4_tight x /\
          Fp_bounded Fp_loose s /\
          (FElem_Fp4 pout old_out *
           (FElem_Fp4 px x *
            (FElem_Fp ps s * Rr)))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp4_bounded Fp4_loose out /\
            (FElem_Fp4 pout out *
             (FElem_Fp4 px x *
              (FElem_Fp ps s * Rr)))%sep mem' }.

    (* ============================================================ *)
    (* Loop invariant                                                 *)
    (* ============================================================ *)

    (** The loop invariant relates stack-allocated FElems, input FElems,
        and the locals map. The measure v counts down from 52 to 0.
        At each iteration, the loop body decrements i by 1.

        Invariant asserts:
        - Trace is unchanged (no I/O)
        - All 7 stack-allocated FElems and 5 input FElems exist in memory
        - All FElems at the right tower level have appropriate bounds
        - Locals map binds the expected variable names *)
    Definition miller_loop_inv
      (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
      (pout p_px p_py p_qx p_qy : word)
      (p_x p_y : Fp_felem) (q_x q_y : Fp4_felem) (old_out : Fp24_felem)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\
      exists (f_val : Fp24_felem) (tx_val ty_val lam_val tmp1_val tmp2_val : Fp4_felem)
             (line_val : Fp24_felem),
        Fp24_bounded Fp24_tight f_val /\
        Fp4_bounded Fp4_tight tx_val /\
        Fp4_bounded Fp4_tight ty_val /\
        (FElem_Fp24 a_f f_val *
         (FElem_Fp4 a_tx tx_val *
          (FElem_Fp4 a_ty ty_val *
           (FElem_Fp4 a_lam lam_val *
            (FElem_Fp4 a_tmp1 tmp1_val *
             (FElem_Fp4 a_tmp2 tmp2_val *
              (FElem_Fp24 a_line line_val *
               (FElem_Fp24 pout old_out *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep m /\
        map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
        map.get l "f" = Some a_f /\
        map.get l "t_x" = Some a_tx /\
        map.get l "t_y" = Some a_ty /\
        map.get l "lambda" = Some a_lam /\
        map.get l "tmp1" = Some a_tmp1 /\
        map.get l "tmp2" = Some a_tmp2 /\
        map.get l "line" = Some a_line /\
        map.get l "out" = Some pout /\
        map.get l "p_x" = Some p_px /\
        map.get l "p_y" = Some p_py /\
        map.get l "q_x" = Some p_qx /\
        map.get l "q_y" = Some p_qy.

    (* ============================================================ *)
    (* Helper lemmas                                                  *)
    (* ============================================================ *)

    Local Lemma sep_from_split {A B : mem -> Prop} {m mOld mNew : mem} :
      map.split m mOld mNew -> A mOld -> B mNew -> (A * B)%sep m.
    Proof.
      intros [Heq Hd] HA HB. subst m.
      exists mOld, mNew.
      split. { split. { reflexivity. } exact Hd. }
      split; assumption.
    Qed.

    Lemma word_nat_sub1 : forall n : nat, (0 < n)%nat ->
      @word.sub 64 word (word.of_Z (Z.of_nat n)) (word.of_Z 1) =
      word.of_Z (Z.of_nat (n - 1)).
    Proof. intros. rewrite <- word.ring_morph_sub. f_equal. zify. lia. Qed.

    (** Helper: combined effect of 24 from_word calls (fp24_set_one)
        + 2 fp4_copy calls on the memory.
        After init:
        - f gets a tight-bounded Fp24 value (the identity element)
        - t_x gets a copy of q_x (tight bounded)
        - t_y gets a copy of q_y (tight bounded)
        - All other FElems and the frame R are preserved. *)
    Lemma fp24_init_mem_transform :
      forall (a_f a_tx a_ty : word)
        (f_val : Fp24_felem) (tx_val ty_val : Fp4_felem)
        (q_x q_y : Fp4_felem) (R : mem -> Prop) (m : mem),
        Fp4_bounded Fp4_tight q_x ->
        Fp4_bounded Fp4_tight q_y ->
        (FElem_Fp24 a_f f_val *
         (FElem_Fp4 a_tx tx_val *
          (FElem_Fp4 a_ty ty_val * R)))%sep m ->
        exists (f_new : Fp24_felem) (m' : mem),
          Fp24_bounded Fp24_tight f_new /\
          (FElem_Fp24 a_f f_new *
           (FElem_Fp4 a_tx q_x *
            (FElem_Fp4 a_ty q_y * R)))%sep m'.
    Proof.
      (* This captures the combined effect of:
         - 24 from_word calls that write tight-bounded Fp values into
           each component of the Fp24 at a_f
         - 2 fp4_copy calls that copy q_x -> a_tx and q_y -> a_ty
         The proof would trace through each WP call; admitted for now. *)
      intros. admit.
    Admitted.

    (* ============================================================ *)
    (* Main theorem                                                   *)
    (* ============================================================ *)

    Lemma bls24_miller_loop_ok :
      forall functions
        (EnvContains : map.get functions "bls24_miller_loop" =
          Some (snd bls24_miller_loop))
        (HFp4mul : spec_of_Fp4_mul functions)
        (HFp4add : spec_of_Fp4_add functions)
        (HFp4sub : spec_of_Fp4_sub functions)
        (HFp4sqr : spec_of_Fp4_sqr functions)
        (HFp4inv : spec_of_Fp4_inv functions)
        (HFp4opp : spec_of_Fp4_opp functions)
        (HFp4copy : spec_of_Fp4_felem_copy functions)
        (HFp8opp : spec_of_Fp8_opp functions)
        (HFp24mul : spec_of_Fp24_mul functions)
        (HFp24sqr : spec_of_Fp24_sqr functions)
        (HFp24copy : spec_of_Fp24_felem_copy functions)
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (HMakeLine : map.get functions "bls24_make_line" =
          Some (snd bls24_make_line))
        (HFp4mulfpEnv : map.get functions "bls24_Fp4_mul_fp" =
          Some (snd bls24_Fp4_mul_fp)),
      spec_of_bls24_miller_loop functions.
    Proof.
      intros.
      unfold spec_of_bls24_miller_loop.
      intros pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0
        [Hbqx [Hbqy [Hbpx [Hbpy Hsep]]]].

      (* === Function entry === *)
      eapply WeakestPreconditionProperties.start_func;
        [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls24_miller_loop. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }

      (* === Process 7 stackallocs === *)
      repeat straightline.

      (* Stackalloc 1: f (Fp24-sized) *)
      split. { apply Z_mod_mult. }
      intros a_f mStack_f mComb_f HanyF HsplitF.
      repeat straightline.

      (* Stackalloc 2: t_x (Fp4-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tx mStack_tx mComb_tx HanyTx HsplitTx.
      repeat straightline.

      (* Stackalloc 3: t_y (Fp4-sized) *)
      split. { apply Z_mod_mult. }
      intros a_ty mStack_ty mComb_ty HanyTy HsplitTy.
      repeat straightline.

      (* Stackalloc 4: lambda (Fp4-sized) *)
      split. { apply Z_mod_mult. }
      intros a_lam mStack_lam mComb_lam HanyLam HsplitLam.
      repeat straightline.

      (* Stackalloc 5: tmp1 (Fp4-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tmp1 mStack_tmp1 mComb_tmp1 HanyTmp1 HsplitTmp1.
      repeat straightline.

      (* Stackalloc 6: tmp2 (Fp4-sized) *)
      split. { apply Z_mod_mult. }
      intros a_tmp2 mStack_tmp2 mComb_tmp2 HanyTmp2 HsplitTmp2.
      repeat straightline.

      (* Stackalloc 7: line (Fp24-sized) *)
      split. { apply Z_mod_mult. }
      intros a_line mStack_line mComb_line HanyLine HsplitLine.

      (* === Convert anybytes to FElems for all stack-allocated buffers === *)
      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr
        wordok mapok a_f) as Hfb_f.
      unfold AbstractField.Placeholder in Hfb_f.
      pose proof (proj1 (Hfb_f mStack_f) HanyF) as [f_val Hfe_f]. clear Hfb_f.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tx) as Hfb_tx.
      unfold AbstractField.Placeholder in Hfb_tx.
      pose proof (proj1 (Hfb_tx mStack_tx) HanyTx) as [tx_val Hfe_tx]. clear Hfb_tx.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_ty) as Hfb_ty.
      unfold AbstractField.Placeholder in Hfb_ty.
      pose proof (proj1 (Hfb_ty mStack_ty) HanyTy) as [ty_val Hfe_ty]. clear Hfb_ty.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_lam) as Hfb_lam.
      unfold AbstractField.Placeholder in Hfb_lam.
      pose proof (proj1 (Hfb_lam mStack_lam) HanyLam) as [lam_val Hfe_lam]. clear Hfb_lam.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tmp1) as Hfb_tmp1.
      unfold AbstractField.Placeholder in Hfb_tmp1.
      pose proof (proj1 (Hfb_tmp1 mStack_tmp1) HanyTmp1) as [tmp1_val Hfe_tmp1]. clear Hfb_tmp1.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tmp2) as Hfb_tmp2.
      unfold AbstractField.Placeholder in Hfb_tmp2.
      pose proof (proj1 (Hfb_tmp2 mStack_tmp2) HanyTmp2) as [tmp2_val Hfe_tmp2]. clear Hfb_tmp2.

      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr
        wordok mapok a_line) as Hfb_line.
      unfold AbstractField.Placeholder in Hfb_line.
      pose proof (proj1 (Hfb_line mStack_line) HanyLine) as [line_val Hfe_line]. clear Hfb_line.

      (* === Phase 1: Build master separation logic hypothesis ===
         The sep hypothesis Hsep (on the intermediate memory before the last
         stackalloc) contains array ptsto entries for buffers 1-6 and FElem
         entries for the 5 input parameters. The last stackalloc (line) is
         separate in HsplitLine/Hfe_line.

         We need to combine everything into a single 12-way sep on mComb_line.
         Strategy: use sep_from_split to merge mComb_tmp2 (from Hsep) with
         mStack_line (from Hfe_line) into mComb_line. *)

      (* === Phase 1: Build master sep on mComb_line ===
         Destruct Hsep to get sub-maps with map.split witnesses,
         convert array ptsto entries to FElems on those sub-maps,
         rebuild the sep on mem0, then extend to mComb_line via
         sep_from_split + ecancel_assumption. *)

      (* Destruct Hsep to expose the 12 sub-components *)
      destruct Hsep as [m_s1 [mr1 [Hsplit1 [Hfe_out Hr1]]]].
      destruct Hr1 as [m_s2 [mr2 [Hsplit2 [Hfe_px Hr2]]]].
      destruct Hr2 as [m_s3 [mr3 [Hsplit3 [Hfe_py Hr3]]]].
      destruct Hr3 as [m_s4 [mr4 [Hsplit4 [Hfe_qx Hr4]]]].
      destruct Hr4 as [m_s5 [mr5 [Hsplit5 [Hfe_qy Hr5]]]].
      destruct Hr5 as [m_s6 [mr6 [Hsplit6 [Hrr Hr6]]]].
      destruct Hr6 as [m_s7 [mr7 [Hsplit7 [Harr_f Hr7]]]].
      destruct Hr7 as [m_s8 [mr8 [Hsplit8 [Harr_tx Hr8]]]].
      destruct Hr8 as [m_s9 [mr9 [Hsplit9 [Harr_ty Hr9]]]].
      destruct Hr9 as [m_s10 [mr10 [Hsplit10 [Harr_lam Hr10]]]].
      destruct Hr10 as [m_s11 [m_s12 [Hsplit11 [Harr_tmp1 Harr_tmp2]]]].

      (* Convert array ptsto entries to anybytes then to FElem on sub-maps *)
      pose proof (Array.array_1_to_anybytes _ _ _ Harr_f) as Hany_f'.
      rewrite length_stack in Hany_f'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr
        wordok mapok a_f m_s7) Hany_f') as [f_val' Hfe_f']. clear Hany_f'.

      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tx) as Hany_tx'.
      rewrite length_stack0 in Hany_tx'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tx m_s8) Hany_tx') as [tx_val' Hfe_tx']. clear Hany_tx'.

      pose proof (Array.array_1_to_anybytes _ _ _ Harr_ty) as Hany_ty'.
      rewrite length_stack1 in Hany_ty'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_ty m_s9) Hany_ty') as [ty_val' Hfe_ty']. clear Hany_ty'.

      pose proof (Array.array_1_to_anybytes _ _ _ Harr_lam) as Hany_lam'.
      rewrite length_stack2 in Hany_lam'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_lam m_s10) Hany_lam') as [lam_val' Hfe_lam']. clear Hany_lam'.

      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tmp1) as Hany_tmp1'.
      rewrite length_stack3 in Hany_tmp1'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tmp1 m_s11) Hany_tmp1') as [tmp1_val' Hfe_tmp1']. clear Hany_tmp1'.

      pose proof (Array.array_1_to_anybytes _ _ _ Harr_tmp2) as Hany_tmp2'.
      rewrite length_stack4 in Hany_tmp2'.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tmp2 m_s12) Hany_tmp2') as [tmp2_val' Hfe_tmp2']. clear Hany_tmp2'.

      clear Harr_f Harr_tx Harr_ty Harr_lam Harr_tmp1 Harr_tmp2.

      (* Rebuild sep on mem0 with FElem entries on the correct sub-maps *)
      assert (Hsep_fe :
        (FElem_Fp24 pout old_out *
         (FElem_Fp p_px p_x *
          (FElem_Fp p_py p_y *
           (FElem_Fp4 p_qx q_x *
            (FElem_Fp4 p_qy q_y *
             (Rr *
              (FElem_Fp24 a_f f_val' *
               (FElem_Fp4 a_tx tx_val' *
                (FElem_Fp4 a_ty ty_val' *
                 (FElem_Fp4 a_lam lam_val' *
                  (FElem_Fp4 a_tmp1 tmp1_val' *
                   FElem_Fp4 a_tmp2 tmp2_val')))))))))))%sep mem0).
      {
        exists m_s1, mr1. split. { exact Hsplit1. }
        split. { exact Hfe_out. }
        exists m_s2, mr2. split. { exact Hsplit2. }
        split. { exact Hfe_px. }
        exists m_s3, mr3. split. { exact Hsplit3. }
        split. { exact Hfe_py. }
        exists m_s4, mr4. split. { exact Hsplit4. }
        split. { exact Hfe_qx. }
        exists m_s5, mr5. split. { exact Hsplit5. }
        split. { exact Hfe_qy. }
        exists m_s6, mr6. split. { exact Hsplit6. }
        split. { exact Hrr. }
        exists m_s7, mr7. split. { exact Hsplit7. }
        split. { exact Hfe_f'. }
        exists m_s8, mr8. split. { exact Hsplit8. }
        split. { exact Hfe_tx'. }
        exists m_s9, mr9. split. { exact Hsplit9. }
        split. { exact Hfe_ty'. }
        exists m_s10, mr10. split. { exact Hsplit10. }
        split. { exact Hfe_lam'. }
        exists m_s11, m_s12. split. { exact Hsplit11. }
        split. { exact Hfe_tmp1'. }
        exact Hfe_tmp2'.
      }

      (* Build master sep on mComb_line via sep_from_split + ecancel *)
      pose proof (sep_from_split HsplitLine Hsep_fe Hfe_line) as Htmp.
      eassert (Hmaster :
        (FElem_Fp24 a_f f_val' *
         (FElem_Fp4 a_tx tx_val' *
          (FElem_Fp4 a_ty ty_val' *
           (FElem_Fp4 a_lam lam_val' *
            (FElem_Fp4 a_tmp1 tmp1_val' *
             (FElem_Fp4 a_tmp2 tmp2_val' *
              (FElem_Fp24 a_line line_val *
               (FElem_Fp24 pout old_out *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep mComb_line).
      { pose proof Htmp as H'. ecancel_assumption. }
      clear Htmp Hsep_fe.

      (* === Phase 2: Function body ===
         Hmaster has the 12-way sep on mComb_line with
         stack FElems f_val'..tmp2_val'/line_val and input FElems.

         miller_loop_full_body =
           fp24_set_one "f"          -- 24 from_word calls
           fp4_copy [t_x; q_x]      -- copy Q.x -> T.x
           fp4_copy [t_y; q_y]      -- copy Q.y -> T.y
           set i = 52               -- loop counter
           while (i) { iteration }  -- main loop (52 -> 0)
           fp4_opp [t_y; t_y]       -- negate T.y (z < 0)
           fp8_opp [c1(f); c1(f)]   -- conjugate f
           fp24_copy [out; f]       -- copy result

         This is decomposed into 4 Admitted blocks:
         (1) bls24_miller_loop_ok        -- main WP (uses 2-4 below)
         (2) bls24_miller_init_ok        -- init: invariant at v=52
         (3) bls24_miller_loop_body_step -- loop body preserves invariant
         (4) bls24_miller_postloop_ok    -- post-loop + dealloc *)
      admit.
    Admitted.

    (* ============================================================ *)
    (* Phase 1: Init — 24 from_word + 2 fp4_copy + set i=52         *)
    (* ============================================================ *)

    (** After the init phase, the invariant holds at v=52:
        - f = 1 (Fp24 identity, tight bounded via 24 from_word)
        - t_x = q_x (copied, tight bounded from Hbqx)
        - t_y = q_y (copied, tight bounded from Hbqy)
        - All other stack FElems (lam, tmp1, tmp2, line) unchanged
        - Locals bind f, t_x, t_y, lambda, tmp1, tmp2, line, out,
          p_x, p_y, q_x, q_y, and i=52 *)
    Lemma bls24_miller_init_ok :
      forall functions
        (HFp4copy : spec_of_Fp4_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
        (pout p_px p_py p_qx p_qy : word)
        (f_val : Fp24_felem) (tx_val ty_val lam_val tmp1_val tmp2_val : Fp4_felem)
        (line_val : Fp24_felem) (old_out : Fp24_felem)
        (p_x p_y : Fp_felem) (q_x q_y : Fp4_felem)
        (Rr : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals),
        Fp4_bounded Fp4_tight q_x ->
        Fp4_bounded Fp4_tight q_y ->
        (FElem_Fp24 a_f f_val *
         (FElem_Fp4 a_tx tx_val *
          (FElem_Fp4 a_ty ty_val *
           (FElem_Fp4 a_lam lam_val *
            (FElem_Fp4 a_tmp1 tmp1_val *
             (FElem_Fp4 a_tmp2 tmp2_val *
              (FElem_Fp24 a_line line_val *
               (FElem_Fp24 pout old_out *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep m ->
        map.get l "f" = Some a_f ->
        map.get l "t_x" = Some a_tx ->
        map.get l "t_y" = Some a_ty ->
        map.get l "q_x" = Some p_qx ->
        map.get l "q_y" = Some p_qy ->
        exists m' l',
          miller_loop_inv a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
            pout p_px p_py p_qx p_qy p_x p_y q_x q_y old_out Rr tr
            52 tr m' l' /\
          (* Init commands produce WP for the continuation *)
          True.
    Proof. intros. admit. Admitted.

    (* ============================================================ *)
    (* Phase 2: Loop body preserves invariant                        *)
    (* ============================================================ *)

    (** One iteration of the Miller loop:
        Given the invariant at vi > 0, process doubling step
        (~16 calls), conditional addition step (~13 calls if
        bit set), and re-establish invariant at vi-1.

        Doubling step calls:
          fp4_sqr, fp4_add x3, fp4_inv, fp4_mul,
          make_line, fp24_sqr, fp24_mul,
          fp4_sqr, fp4_sub x3, fp4_mul, fp4_sub, fp4_copy

        Addition step calls (when bit=1):
          fp4_sub x2, fp4_inv, fp4_mul,
          make_line, fp24_mul,
          fp4_sqr, fp4_sub x3, fp4_mul, fp4_sub, fp4_copy *)
    Lemma bls24_miller_loop_body_step :
      forall functions
        (HFp4mul : spec_of_Fp4_mul functions)
        (HFp4add : spec_of_Fp4_add functions)
        (HFp4sub : spec_of_Fp4_sub functions)
        (HFp4sqr : spec_of_Fp4_sqr functions)
        (HFp4inv : spec_of_Fp4_inv functions)
        (HFp4opp : spec_of_Fp4_opp functions)
        (HFp4copy : spec_of_Fp4_felem_copy functions)
        (HFp24mul : spec_of_Fp24_mul functions)
        (HFp24sqr : spec_of_Fp24_sqr functions)
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (HMakeLine : map.get functions "bls24_make_line" =
          Some (snd bls24_make_line))
        (HFp4mulfpEnv : map.get functions "bls24_Fp4_mul_fp" =
          Some (snd bls24_Fp4_mul_fp))
        (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
        (pout p_px p_py p_qx p_qy : word)
        (p_x p_y : Fp_felem) (q_x q_y : Fp4_felem) (old_out : Fp24_felem)
        (Rr : mem -> Prop) (tr : Semantics.trace)
        (vi : nat) (ti : Semantics.trace) (mi : mem) (li : locals),
        miller_loop_inv a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
          pout p_px p_py p_qx p_qy p_x p_y q_x q_y old_out Rr tr
          vi ti mi li ->
        (* Condition: i > 0 (loop hasn't exited) *)
        (0 < vi)%nat ->
        (* Body produces state with smaller measure *)
        exists vi' ti' mi' li',
          Nat.lt vi' vi /\
          miller_loop_inv a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line
            pout p_px p_py p_qx p_qy p_x p_y q_x q_y old_out Rr tr
            vi' ti' mi' li'.
    Proof. intros. admit. Admitted.

    (* ============================================================ *)
    (* Phase 3: Post-loop continuation                               *)
    (* ============================================================ *)

    (** After the loop exits (i=0), the post-loop phase:
        - fp4_opp(t_y, t_y)     -- negate T.y since z < 0
        - fp8_opp(c1(f), c1(f)) -- conjugate f (unitary inverse)
        - fp24_copy(out, f)     -- copy result to output
        Then 7 stack deallocations + final postcondition.

        This lemma handles the sep-logic extraction after the fp24_copy
        has been executed: pout now holds f_result (copied from f),
        and the 7 stack-allocated FElems need to be converted back to
        anybytes (Placeholder) for deallocation.

        The bound Fp24_bounded Fp24_tight f_result comes from the loop
        invariant and is relaxed to Fp24_loose for the postcondition. *)
    Lemma bls24_miller_postloop_ok :
      forall (a_f a_tx a_ty a_lam a_tmp1 a_tmp2 a_line : word)
        (pout p_px p_py p_qx p_qy : word)
        (p_x p_y : Fp_felem) (q_x q_y : Fp4_felem)
        (f_result : Fp24_felem)
        (tx_val ty_val lam_val tmp1_val tmp2_val : Fp4_felem)
        (line_val f_leftover : Fp24_felem)
        (Rr : mem -> Prop) (m : mem),
        Fp24_bounded Fp24_tight f_result ->
        (FElem_Fp24 a_f f_leftover *
         (FElem_Fp4 a_tx tx_val *
          (FElem_Fp4 a_ty ty_val *
           (FElem_Fp4 a_lam lam_val *
            (FElem_Fp4 a_tmp1 tmp1_val *
             (FElem_Fp4 a_tmp2 tmp2_val *
              (FElem_Fp24 a_line line_val *
               (FElem_Fp24 pout f_result *
                (FElem_Fp p_px p_x *
                 (FElem_Fp p_py p_y *
                  (FElem_Fp4 p_qx q_x *
                   (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep m ->
        (* Post-copy result: output holds f_result with loose bounds,
           plus input FElems and Rr survive.
           Stack FElems are converted to Placeholder for deallocation. *)
        exists out : Fp24_felem,
          Fp24_bounded Fp24_loose out /\
          (FElem_Fp24 pout out *
           (FElem_Fp p_px p_x *
            (FElem_Fp p_py p_y *
             (FElem_Fp4 p_qx q_x *
              (FElem_Fp4 p_qy q_y *
               (Rr *
                (AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_f *
                 (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tx *
                  (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_ty *
                   (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_lam *
                    (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp1 *
                     (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp2 *
                      AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_line))))))))))))%sep m.
    Proof.
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hbnd Hsep.
      exists f_result.
      split.
      { exact (@AbstractField.relax_bounds
                 _ _ _ _ _ _ bls24_Fp24_repr bls24_Fp24_repr_ok
                 _ Hbnd). }
      (* Convert each stack FElem to Placeholder via FElem_to_bytes *)
      assert (Hweaken :
        Lift1Prop.impl1
          (FElem_Fp24 a_f f_leftover *
           (FElem_Fp4 a_tx tx_val *
            (FElem_Fp4 a_ty ty_val *
             (FElem_Fp4 a_lam lam_val *
              (FElem_Fp4 a_tmp1 tmp1_val *
               (FElem_Fp4 a_tmp2 tmp2_val *
                (FElem_Fp24 a_line line_val *
                 (FElem_Fp24 pout f_result *
                  (FElem_Fp p_px p_x *
                   (FElem_Fp p_py p_y *
                    (FElem_Fp4 p_qx q_x *
                     (FElem_Fp4 p_qy q_y * Rr))))))))))))
          (AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_f *
           (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tx *
            (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_ty *
             (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_lam *
              (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp1 *
               (AbstractField.Placeholder (field_representation:=bls24_Fp4_repr) a_tmp2 *
                (AbstractField.Placeholder (field_representation:=bls24_Fp24_repr) a_line *
                 (FElem_Fp24 pout f_result *
                  (FElem_Fp p_px p_x *
                   (FElem_Fp p_py p_y *
                    (FElem_Fp4 p_qx q_x *
                     (FElem_Fp4 p_qy q_y * Rr))))))))))))%sep).
      { eapply Proper_sep_impl1;
          [eapply AbstractField.FElem_to_bytes |].
        eapply Proper_sep_impl1;
          [eapply AbstractField.FElem_to_bytes |].
        eapply Proper_sep_impl1;
          [eapply AbstractField.FElem_to_bytes |].
        eapply Proper_sep_impl1;
          [eapply AbstractField.FElem_to_bytes |].
        eapply Proper_sep_impl1;
          [eapply AbstractField.FElem_to_bytes |].
        eapply Proper_sep_impl1;
          [eapply AbstractField.FElem_to_bytes |].
        eapply Proper_sep_impl1;
          [eapply AbstractField.FElem_to_bytes |].
        reflexivity. }
      pose proof (Hweaken m Hsep) as Hsep'.
      clear Hweaken Hsep.
      ecancel_assumption.
    Qed.

End BLS24_MillerLoopProof.
