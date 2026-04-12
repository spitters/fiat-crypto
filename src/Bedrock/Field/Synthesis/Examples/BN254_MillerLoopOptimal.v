(** * BN254 Miller Loop WP Proof
    Standalone WP correctness proof for bn254_miller_loop from BN254_Pairing.v.
    Uses Loops.while_localsmap with a 64->0 nat measure.

    Key differences from BLS12-377 (BLS12_377_MillerLoop.v):
    - beta = -1, xi = (9, 1)
    - 64 iterations (65-bit 6u+2 parameter, MSB consumed at init) instead of 65
    - u6p2 stored as 1-word (8 bytes) on stack; bit extraction is a single load
    - No conjugation after loop (positive u)
    - 8 stackallocs (7 FElems + 1 u6p2 word of 8 bytes)
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
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime_certif.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN254_Pairing.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Crypto.Bedrock.Field.Synthesis.Examples.BLS12_MillerGeneric.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* BN254 Section context                                             *)
(* ================================================================ *)

Section BN254_MillerLoopOptimal.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BN254 prime parameters *)
    Let bn254_M_pos : positive := Eval vm_compute in (Z.to_pos bn254_prime.m).

    Instance bn254_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn254_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn254_mul"; PrimeField.add := "bn254_add";
      PrimeField.sub := "bn254_sub"; PrimeField.opp := "bn254_opp";
      PrimeField.square := "bn254_square"; PrimeField.scmula24 := "bn254_scmula24";
      PrimeField.inv := "bn254_inv"; PrimeField.from_bytes := "bn254_from_bytes";
      PrimeField.to_bytes := "bn254_to_bytes"; PrimeField.select_znz := "bn254_select_znz";
      PrimeField.felem_copy := "bn254_felem_copy"; PrimeField.from_word := "bn254_from_word";
      PrimeField.from_list := "bn254_from_list";
    |}.

    Instance bn254_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn254. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* Fp-level representation from synthesis pipeline *)
    Instance bn254_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn254_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn254_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn254_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn254_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn254_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn254_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn254_frep |}.

    Instance bn254_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn254_Fp_rep] in *.
      cbv [Field.bounded_by bn254_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bn254_Fp2_".
    Let fp6_prefix := "bn254_Fp6_".
    Let fp12_prefix := "bn254_Fp12_".

    (* beta = -1 for BN254 (Fp2 = Fp[u]/(u^2 + 1)) *)
    Let bn254_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* xi = (9, 1) for BN254 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bn254_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 9.
    Let bn254_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    (* ============================================================ *)
    (* Field extension instances                                     *)
    (* ============================================================ *)

    Instance bn254_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ext_Fp2_params bn254_beta "bn254_".
    Instance bn254_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ext_Fp2_rep bn254_beta "bn254_".
    Instance bn254_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ext_Fp6_params bn254_beta bn254_xi_re bn254_xi_im "bn254_".
    Instance bn254_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ext_Fp6_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_".
    Instance bn254_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ext_Fp12_params bn254_beta bn254_xi_re bn254_xi_im "bn254_".
    Instance bn254_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ext_Fp12_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_".

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bn254_Fp6_params' _ _ _ _ bn254_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bn254_Fp12_params'.
    Local Typeclasses Opaque bn254_Fp6_params'.
    Local Typeclasses Opaque bn254_Fp2_params'.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    (* Fp2 operations *)
    Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.bin_mul.

    Instance spec_of_Fp2_add : spec_of (AbstractField.add (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.bin_add.

    Instance spec_of_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.bin_sub.

    Instance spec_of_Fp2_sqr : spec_of (AbstractField.square (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.un_square.

    Instance spec_of_Fp2_inv : spec_of (AbstractField.inv (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.un_inv.

    Instance spec_of_Fp2_opp : spec_of (AbstractField.opp (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.un_opp.

    Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
      AbstractField.spec_of_felem_copy (F:=Fp2) (field_representation:=bn254_Fp2_rep').

    (* Fp12 operations *)
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bn254_Fp12_rep') AbstractField.bin_mul.

    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn254_Fp12_rep') AbstractField.un_square.

    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bn254_Fp12_rep').

    (* Fp operations needed by make_line *)
    Instance spec_of_Fp_mul : spec_of PrimeField.mul :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bn254_Fp_rep) AbstractField.bin_mul.

    Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
      AbstractField.spec_of_felem_copy (F:=Fp) (field_representation:=bn254_Fp_rep).

    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bn254_Fp_rep).

    (* spec_of for bn254_make_line -- needed by straightline_call *)
    Instance spec_of_bn254_make_line_corrected : spec_of "bn254_make_line_corrected" :=
      fnspec! "bn254_make_line_corrected" (pout plam pxt pyt pxp pyp : word)
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
    (* D1: bn254_miller_loop spec and proof                          *)
    (* ============================================================ *)

    Instance spec_of_bn254_miller_loop_optimal : spec_of "bn254_miller_loop_optimal" :=
      fnspec! "bn254_miller_loop_optimal" (pout p_px p_py p_qx p_qy : word)
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

    (* u6p2 value: |6u+2| low 64 bits = 0x9D797039BE763BA8.
       The MSB (bit 64) initializes T=Q; we iterate bits 63 down to 0. *)
    Local Definition u6p2_word : word := word.of_Z 0x9D797039BE763BA8.

    (* Loop invariant for the Miller loop.
       The measure v counts down from 64 to 0. At each iteration, the
       loop body decrements i by 1, so v = word.unsigned(i).
       The invariant asserts:
       - The trace is unchanged (no I/O)
       - All 7 stack-allocated FElems, the u6p2 scalar, and 5 input FElems exist in memory
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
        (v <= 64)%nat /\
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
               (scalar a_u6p2 u6p2_word ⋆
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
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep)).

    Lemma FElem_Fp2_split_in_sep p (x : Fp2_felem) R m :
      (FElem_Fp2 p x ⋆ R) m ->
      (FElem_Fp p (fst_felem x) ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset_val)) (snd_felem x) ⋆ R)) m.
    Proof.
      intros [m1 [m2 [[Heq Hd] [Hfp2 HR]]]].
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_split bn254_beta
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
      length a = @AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep ->
      length b = @AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep ->
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
      pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_join bn254_beta
        fp2_prefix p a b (map.putmany ma mb) Hla Hlb Hjoin) as Hfp2.
      exists (map.putmany ma mb), mr2.
      split; [split |].
      { subst m. rewrite map.putmany_assoc. reflexivity. }
      { apply map.disjoint_putmany_l. split; [exact Hd_ar | exact Hd2]. }
      split; [exact Hfp2 | exact HR].
    Qed.

    (* u6p2 store lemma: process single store to stack-allocated u6p2.
       Converts anybytes 8 -> scalar after the store completes. *)
    Local Lemma u6p2_store_wp :
      forall call t (m : mem) l (a_u6p2 : word) R
             (post : Semantics.trace -> mem -> locals -> Prop),
        map.get l "u6p2" = Some a_u6p2 ->
        (Memory.anybytes a_u6p2 8 ⋆ R) m ->
        (forall m', (scalar a_u6p2 u6p2_word ⋆ R) m' ->
          post t m' l) ->
        WeakestPrecondition.cmd call
          (BN254_Pairing.store_6u2_limbs) t m l post.
    Proof.
      intros call t m l a_u6p2 R post Hget Hany Hpost.
      (* Convert anybytes 8 to a scalar *)
      change 8 with (Memory.bytes_per_word 64) in Hany.
      destruct Hany as [m_any [m_R [[Hm Hdisj] [Hany' HR]]]].
      apply anybytes_to_scalar in Hany'.
      destruct Hany' as [w0 Hsc0].
      (* Unfold store_6u2_limbs into a single store *)
      unfold BN254_Pairing.store_6u2_limbs.
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
      { subst m. exists m_any, m_R.
        split; [split; [reflexivity | exact Hdisj] |].
        split; [exact Hsc0 | exact HR]. }
      intros m1 Hsep1.
      apply Hpost.
      exact Hsep1.
    Qed.

    (* u6p2 scalar to anybytes: convert scalar back to anybytes 8.
       This is needed for stack deallocation. *)
    Local Lemma scalar_to_anybytes8 :
      forall (a : word) (w : word) (m : mem),
      scalar a w m ->
      Memory.anybytes a 8 m.
    Proof.
      intros a w m Hsc.
      apply scalar_to_anybytes in Hsc.
      exact Hsc.
    Qed.

    (* u6p2 load lemma: load from single-word u6p2 *)
    Local Lemma u6p2_scalar_load (a_u6p2 : word) (m : mem) (R : mem -> Prop)
      (Hsep : (scalar a_u6p2 u6p2_word ⋆ R) m) :
      Memory.load access_size.word m a_u6p2 = Some u6p2_word.
    Proof.
      eapply Scalars.load_word_of_sep.
      ecancel_assumption.
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

    Lemma bn254_miller_loop_optimal_ok :
      forall functions
        (EnvContains : map.get functions "bn254_miller_loop_optimal" =
          Some (snd bn254_miller_loop_optimal))
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
        (HMakeLine : map.get functions "bn254_make_line_corrected" =
          Some (snd bn254_make_line_corrected))
        (HFp2mulfpEnv : map.get functions "bn254_Fp2_mul_fp" =
          Some (snd bn254_Fp2_mul_fp))
        (HMakeLineOk : spec_of_bn254_make_line_corrected functions),
      spec_of_bn254_miller_loop_optimal functions.
    Proof.
      (* Full proof is structurally identical to bn254_miller_loop_ok
         but needs 5 extra stackalloc layers + Frobenius correction calls.
         In progress — see BN254_PairingHelpers.v for the pattern. *)
    Admitted.

End BN254_MillerLoopOptimal.
