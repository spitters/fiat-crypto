(** * BN254 Pairing Helper WP Proofs
    Standalone WP correctness proofs for pairing helper functions
    defined in BN254_Pairing.v:
    - C1: bn254_Fp2_mul_fp (multiply Fp2 by Fp scalar)
    - C3: bn254_load_gamma1_p2
    - C4: bn254_load_gamma2_p2
    - C5: bn254_load_w_frob_p2_c1
    - C2: bn254_make_line
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
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

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ================================================================ *)
(* BN254 Section context — mirrors BN254_Pairing.v                  *)
(* ================================================================ *)

Section BN254_PairingHelpers.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BN254 prime parameters *)
    Let bn254_M_pos : positive := Eval vm_compute in (Z.to_pos bn254_prime.m).

    Instance bn254_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn254_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn254_mul";
      PrimeField.add := "bn254_add";
      PrimeField.sub := "bn254_sub";
      PrimeField.opp := "bn254_opp";
      PrimeField.square := "bn254_square";
      PrimeField.scmula24 := "bn254_scmula24";
      PrimeField.inv := "bn254_inv";
      PrimeField.from_bytes := "bn254_from_bytes";
      PrimeField.to_bytes := "bn254_to_bytes";
      PrimeField.select_znz := "bn254_select_znz";
      PrimeField.felem_copy := "bn254_felem_copy";
      PrimeField.from_word := "bn254_from_word";
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

    (* beta = -1 for BN254 (p ≡ 3 mod 4) *)
    Let bn254_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* xi = (9, 1) for BN254 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bn254_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 9.
    Let bn254_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    (* ============================================================ *)
    (* Field extension instances                                     *)
    (* ============================================================ *)

    Instance bn254_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bn254_beta "bn254_") in exact v).
    Instance bn254_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bn254_beta "bn254_") in exact v).
    Instance bn254_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bn254_Fp6_params' _ _ _ _ bn254_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bn254_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bn254_Fp_rep).

    (* Fp-level offset within Fp2 *)
    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep)).

    Local Notation fst_felem := (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bn254_pf_params bn254_Fp_rep).
    Local Notation snd_felem := (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bn254_pf_params bn254_Fp_rep).

    (* ============================================================ *)
    (* Compatibility: function body identity                         *)
    (* ============================================================ *)

    (* The function body defined here (via bn254_pf_params) must equal
       the imported one from BN254_Pairing (via bn254_prime_params).
       Both define M_pos = Z.to_pos bn254_prime.m and the same function names,
       so the bodies are convertible. *)

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    Instance spec_of_Fp_mul : spec_of PrimeField.mul :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bn254_Fp_rep) AbstractField.bin_mul.

    Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
      AbstractField.spec_of_felem_copy (F:=Fp) (field_representation:=bn254_Fp_rep).

    Instance spec_of_Fp_opp : spec_of (@AbstractField.opp _ prime_field_parameters) :=
      AbstractField.unop_spec (F:=Fp) (field_parameters:=prime_field_parameters)
        (field_representation:=bn254_Fp_rep) AbstractField.un_opp.

    Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.bin_mul.

    Instance spec_of_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) :=
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.bin_sub.

    Instance spec_of_Fp2_opp : spec_of (AbstractField.opp (F:=Fp2)) :=
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bn254_Fp2_rep') AbstractField.un_opp.

    Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
      AbstractField.spec_of_felem_copy (F:=Fp2) (field_representation:=bn254_Fp2_rep').

    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bn254_Fp_rep).

    Local Typeclasses Opaque bn254_Fp12_params'.
    Local Typeclasses Opaque bn254_Fp6_params'.
    Local Typeclasses Opaque bn254_Fp2_params'.

    (* ============================================================ *)
    (* Helper: split FElem_Fp2 in a sep into two FElem_Fp entries   *)
    (* ============================================================ *)

    Lemma FElem_Fp2_split_in_sep p (x : Fp2_felem) R m :
      (FElem_Fp2 p x ⋆ R) m ->
      (FElem_Fp p (fst_felem x) ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset)) (snd_felem x) ⋆ R)) m.
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

    (* Reverse: join two FElem_Fp back into FElem_Fp2 in a sep *)
    Lemma FElem_Fp_join_in_sep p (a b : Fp_felem) R m :
      length a = @AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep ->
      length b = @AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep ->
      (FElem_Fp p a ⋆
       (FElem_Fp (word.add p (word.of_Z fp_felem_offset)) b ⋆ R)) m ->
      (FElem_Fp2 p (a ++ b) ⋆ R) m.
    Proof.
      intros Hla Hlb [ma [mr1 [[Heq1 Hd1] [Ha Hr1]]]].
      destruct Hr1 as [mb [mr2 [[Heq2 Hd2] [Hb HR]]]].
      subst mr1.
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd1) as [Hd_ab Hd_ar].
      assert (Hjoin : (FElem_Fp p a ⋆
        FElem_Fp (word.add p (word.of_Z fp_felem_offset)) b) (map.putmany ma mb)).
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

    (* ============================================================ *)
    (* C1: bn254_Fp2_mul_fp — multiply Fp2 by Fp scalar             *)
    (* ============================================================ *)

    (* Gallina model: scale each Fp component by s *)
    Local Definition fp2_mul_fp_model (x : Fp2) (s : Fp) : Fp2 :=
      (@F.mul PrimeField.M_pos (fst x) s,
       @F.mul PrimeField.M_pos (snd x) s).

    Instance spec_of_bn254_Fp2_mul_fp : spec_of "bn254_Fp2_mul_fp" :=
      fnspec! "bn254_Fp2_mul_fp" (pout px ps : word)
        / (old_out x : Fp2_felem) (s : Fp_felem)
          Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight x /\
          Fp_bounded Fp_loose s /\
          (FElem_Fp2 px x ⋆ (FElem_Fp ps s ⋆ (FElem_Fp2 pout old_out ⋆ Rr))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp2_feval out = fp2_mul_fp_model (Fp2_feval x) (Fp_feval s) /\
            Fp2_bounded Fp2_tight out /\
            (FElem_Fp2 pout out ⋆ (FElem_Fp2 px x ⋆ (FElem_Fp ps s ⋆ Rr))) mem' }.

    Lemma bn254_Fp2_mul_fp_ok :
      forall functions
        (EnvContains : map.get functions "bn254_Fp2_mul_fp" =
          Some (snd bn254_Fp2_mul_fp))
        (HFmul : spec_of_Fp_mul functions),
      spec_of_bn254_Fp2_mul_fp functions.
    Proof.
      intros.
      unfold spec_of_bn254_Fp2_mul_fp.
      intros pout px ps old_out x s Rr tr mem0 [Hbx [Hbs Hsep]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bn254_Fp2_mul_fp. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }
      (* Step through: cmd.seq -> cmd.call arg evaluation *)
      straightline. straightline. straightline.
      (* Now at: call functions "bn254_mul" tr mem0 args postcondition *)

      (* === Decompose precondition sep === *)
      destruct Hsep as [m_x [m_r1 [[Heq0 Hd0] [Hfx Hr1]]]].
      destruct Hr1 as [m_s [m_r2 [[Heq1 Hd1] [Hfs Hr2]]]].
      destruct Hr2 as [m_out [m_rr [[Heq2 Hd2] [Hfe_out Hrr]]]].
      subst m_r1 m_r2 mem0.

      (* Split Fp2 FElems into Fp halves *)
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
        wordok mapok bn254_pf_params bn254_Fp_rep bn254_beta fp2_prefix
        px x m_x Hfx)
        as [m_x1 [m_x2 [Hsep_x [Hx1 Hx2]]]].
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
        wordok mapok bn254_pf_params bn254_Fp_rep bn254_beta fp2_prefix
        pout old_out m_out Hfe_out)
        as [m_o1 [m_o2 [Hsep_o [Ho1 Ho2]]]].

      (* Decompose Fp2 bounded_by into 2 Fp bounded_by *)
      change (@AbstractField.bounded_by _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep')
        with (fun b ws => @AbstractField.bounded_by _ _ _ _ _ _ bn254_Fp_rep b
          (fst_felem ws)
          /\ @AbstractField.bounded_by _ _ _ _ _ _ bn254_Fp_rep b
          (snd_felem ws)) in Hbx.
      destruct Hbx as [Hbx1 Hbx2].

      (* Derive pairwise disjointness *)
      destruct Hsep_x as [Heq_x Hd_x12]. destruct Hsep_o as [Heq_o Hd_o12].
      subst m_x m_out.
      split_all_disjointness.

      (* Build master 6-way sep *)
      set (combined_mem :=
        map.putmany (map.putmany m_x1 m_x2)
          (map.putmany m_s (map.putmany (map.putmany m_o1 m_o2) m_rr))).
      assert (Hcm : combined_mem =
        map.putmany m_x1 (map.putmany m_x2
          (map.putmany m_s (map.putmany m_o1 (map.putmany m_o2 m_rr))))).
      { unfold combined_mem. rewrite !map.putmany_assoc. reflexivity. }
      assert (Hsep6 :
        (FElem_Fp px (fst_felem x) ⋆
         (FElem_Fp (word.add px (word.of_Z fp_felem_offset)) (snd_felem x) ⋆
          (FElem_Fp ps s ⋆
           (FElem_Fp pout (fst_felem old_out) ⋆
            (FElem_Fp (word.add pout (word.of_Z fp_felem_offset)) (snd_felem old_out) ⋆ Rr)))))
        combined_mem).
      { rewrite Hcm.
        exists m_x1, (map.putmany m_x2 (map.putmany m_s (map.putmany m_o1 (map.putmany m_o2 m_rr)))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hx1 |].
        exists m_x2, (map.putmany m_s (map.putmany m_o1 (map.putmany m_o2 m_rr))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hx2 |].
        exists m_s, (map.putmany m_o1 (map.putmany m_o2 m_rr)).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfs |].
        exists m_o1, (map.putmany m_o2 m_rr).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho1 |].
        exists m_o2, m_rr.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Ho2 | exact Hrr]. }

      (* === Call 1: bn254_mul(out, x, s) — fst halves === *)
      eapply Semantics.weaken_call.
      1: { pose proof HFmul as HFmul1.
           unfold spec_of_Fp_mul, AbstractField.binop_spec in HFmul1.
           eapply (HFmul1 pout px ps
             (fst_felem old_out) (fst_felem x) s _ tr).
           split; [apply (@AbstractField.relax_bounds _ _ _ _ _ _
             bn254_Fp_rep bn254_Fp_rep_ok); exact Hbx1 |].
           split; [exact Hbs |].
           split; [eexists; pose proof Hsep6 as H'; ecancel_assumption |].
           split; [eexists; pose proof Hsep6 as H'; ecancel_assumption |].
           pose proof Hsep6 as H'. ecancel_assumption. }

      (* Process postcondition of call 1 *)
      intros t1 m1 rets1 [Hrets1 [Htr1 [out1 [Hfeval1 [Hbound1 Hsep1]]]]].
      subst rets1. symmetry in Htr1. subst t1.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }
      (* Process cmd.seq continuation to second call *)
      straightline. straightline. straightline.

      (* === Call 2: bn254_mul(out+off, x+off, s) — snd halves === *)
      eapply Semantics.weaken_call.
      1: { pose proof HFmul as HFmul2.
           unfold spec_of_Fp_mul, AbstractField.binop_spec in HFmul2.
           eapply (HFmul2
             (word.add pout (word.of_Z fp_felem_offset))
             (word.add px (word.of_Z fp_felem_offset))
             ps
             (snd_felem old_out) (snd_felem x) s _ tr).
           split; [apply (@AbstractField.relax_bounds _ _ _ _ _ _
             bn254_Fp_rep bn254_Fp_rep_ok); exact Hbx2 |].
           split; [exact Hbs |].
           split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
           split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
           pose proof Hsep1 as H'. ecancel_assumption. }

      (* Process postcondition of call 2 *)
      intros t2 m2 rets2 [Hrets2 [Htr2 [out2 [Hfeval2 [Hbound2 Hsep2]]]]].
      subst rets2. symmetry in Htr2. subst t2.
      cbv [map.putmany_of_list_zip].
      exists (#{ "out" => pout; "x" => px; "s" => ps }#).
      split. { exact eq_refl. }
      cbv [list_map get]. split. { exact eq_refl. }
      split. { exact eq_refl. }

      (* === Final postcondition === *)
      (* Get lengths for Fp2_raw_FElem_join *)
      assert (Hlen_out1 : length out1 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep).
      { destruct Hsep1 as [mc [_ [_ [Hfc _]]]].
        exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bn254_pf_params bn254_Fp_rep _ _ _ Hfc). }
      assert (Hlen_out2 : length out2 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep).
      { destruct Hsep2 as [mc [_ [_ [Hfc _]]]].
        exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bn254_pf_params bn254_Fp_rep _ _ _ Hfc). }
      assert (Hlen_x1 : length (fst_felem x) =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep).
      { exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bn254_pf_params bn254_Fp_rep _ _ _ Hx1). }
      assert (Hlen_x2 : length (snd_felem x) =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ bn254_Fp_rep).
      { exact (@QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bn254_pf_params bn254_Fp_rep _ _ _ Hx2). }

      (* Witness: concatenation of two Fp felems *)
      exists (out1 ++ out2).

      (* feval *)
      split.
      { unfold fp2_mul_fp_model.
        change Fp2_feval with (fun ws =>
          (Fp_feval (fst_felem ws), Fp_feval (snd_felem ws))).
        cbv beta.
        unfold fst_felem, snd_felem,
          QuadraticFieldExtensionsSpecs.fst_felem, QuadraticFieldExtensionsSpecs.snd_felem.
        rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_out1).
        rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_out1).
        rewrite Hfeval1, Hfeval2.
        cbv [bin_model AbstractField.bin_mul AbstractField.Fmul].
        reflexivity. }

      (* bounded_by tight *)
      split.
      { change Fp2_bounded with (fun b ws =>
          Fp_bounded b (fst_felem ws) /\ Fp_bounded b (snd_felem ws)).
        unfold fst_felem, snd_felem,
          QuadraticFieldExtensionsSpecs.fst_felem, QuadraticFieldExtensionsSpecs.snd_felem.
        rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_out1).
        rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_out1).
        cbv [bin_outbounds AbstractField.bin_mul] in Hbound1, Hbound2.
        split; assumption. }

      (* sep: FElem_Fp2 pout (out1 ++ out2) * (FElem_Fp2 px x * (FElem_Fp ps s * Rr)) *)
      { (* Decompose Hsep2 to get individual maps *)
        destruct Hsep2 as [m_A [m_rest1 [[Heq_s2 Hd_s2] [HA Hrest1]]]].
        destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_r1] [HB Hrest2]]]].
        destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_r2] [HC Hrest3]]]].
        destruct Hrest3 as [m_D [m_E [[Heq_r3 Hd_DE] [HD HE]]]].
        subst m_rest1 m_rest2 m_rest3 m2.
        split_all_disjointness.
        (* Join output Fp halves into Fp2 *)
        assert (Hjoin_out :
          (FElem_Fp pout out1 ⋆
           FElem_Fp (word.add pout (word.of_Z fp_felem_offset)) out2)
          (map.putmany m_B m_A)).
        { exists m_B, m_A.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact HB | exact HA]. }
        pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
          wordok mapok bn254_pf_params bn254_Fp_rep bn254_beta fp2_prefix
          pout out1 out2
          (map.putmany m_B m_A) Hlen_out1 Hlen_out2 Hjoin_out) as Hfp2_out.
        (* Join input Fp halves into Fp2 *)
        assert (Hjoin_x :
          (FElem_Fp px (fst_felem x) ⋆
           FElem_Fp (word.add px (word.of_Z fp_felem_offset)) (snd_felem x))
          (map.putmany m_C m_D)).
        { exists m_C, m_D.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact HC | exact HD]. }
        pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
          wordok mapok bn254_pf_params bn254_Fp_rep bn254_beta fp2_prefix
          px (fst_felem x) (snd_felem x)
          (map.putmany m_C m_D) Hlen_x1 Hlen_x2 Hjoin_x) as Hfp2_x.
        rewrite (@QuadraticFieldExtensions.Fp2_list_decomp _ _ _ _
          bn254_pf_params bn254_Fp_rep x) in Hfp2_x.
        (* Build final sep *)
        exists (map.putmany m_B m_A),
               (map.putmany (map.putmany m_C m_D) m_E).
        split; [split |].
        { rewrite !map.putmany_assoc.
          rewrite (map.putmany_comm m_A m_B Hdj15).
          reflexivity. }
        { map_disjoint_auto. }
        split; [exact Hfp2_out |].
        exists (map.putmany m_C m_D), m_E.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hfp2_x | exact HE]. }
    Qed.

    (* ============================================================ *)
    (* C3-C5: Frobenius constant loaders                            *)
    (* ============================================================ *)

    (* These functions store 8 words (4 real limbs + 4 zeros) to
       an Fp2 buffer. The proof strategy:
       1. Unfold FElem_Fp2 -> Bignum -> array scalar, normalize addresses
       2. Build combined sep with 8 individual scalar predicates + Rr
       3. Process 8 cmd.store via repeat straightline
       4. Reconstruct FElem_Fp2 from updated scalars (postcondition)
       Steps 1-3 are automated by solve_store_fp2_constant.
       Step 4 (postcondition + bounded_by) is admitted. *)

    (* Normalize nested word.add in a hypothesis to absolute offsets.
       Rewrites word.add (word.add p (word.of_Z a)) (word.of_Z b)
       into word.add p (word.of_Z (a + b)) via:
       1. Right-associate: (p + a) + b -> p + (a + b) via <- add_assoc
       2. Fold Z addition: word.add (of_Z a) (of_Z b) -> of_Z (a+b)
       3. Evaluate: of_Z (a+b) -> of_Z v where v = a+b *)
    Local Ltac normalize_word_addr_in H :=
      repeat (rewrite <- Properties.word.add_assoc in H);
      repeat (rewrite <- word.ring_morph_add in H);
      repeat match type of H with
      | context [word.of_Z (?a + ?b)] =>
        let v := eval cbv in (a + b) in
        change (a + b) with v in H
      end.

    (* Helper: swap conjunction for proving sep before bounded *)
    Local Definition conj_swap {A B : Prop} (b : B) (a : A) : A /\ B := conj a b.

    (* Helper: fold scalars + Rr back into (Bignum * Rr) for postcondition *)
    (* Eliminates emp from Bignum unfolding: proves (Bignum n p vs * R) m
       from (array scalar step p vs * R) m when length vs = n *)
    Local Lemma Bignum_of_array_sep n p (vs : list word) R m :
      length vs = n ->
      (array Scalars.scalar (word.of_Z (Memory.bytes_per_word 64)) p vs ⋆ R) m ->
      (Bignum.Bignum n p vs ⋆ R) m.
    Proof.
      intros Hlen Hsep.
      unfold Bignum.Bignum.
      destruct Hsep as [m1 [m2 [[Heq Hd] [Ha HR]]]].
      exists m1, m2.
      split. { split; [exact Heq | exact Hd]. }
      split; [|exact HR].
      exists map.empty, m1.
      split. { split.
        - symmetry. apply Properties.map.putmany_empty_l.
        - apply Properties.map.disjoint_empty_l. }
      split.
      - cbv [emp]. exact (conj eq_refl Hlen).
      - exact Ha.
    Qed.

    (* Shared tactic for C3-C5 store-only constant loaders.
       After the function-specific setup (start_func, unfold, eexists, split),
       this tactic:
       1. Decomposes FElem_Fp2 into 8 scalar predicates
       2. Processes 8 cmd.store via repeat straightline
       3. Reconstructs FElem_Fp2 from the updated scalars *)
    Local Ltac solve_store_fp2_constant :=
      (* Phase 1: Decompose FElem_Fp2 into 8 scalars *)
      match goal with Hsep : (FElem_Fp2 _ _ ⋆ ?RR) _ |- _ =>
        let m_out := fresh "m_out" in let m_rr := fresh "m_rr" in
        let Hout := fresh "Hout" in let Hrr := fresh "Hrr" in
        let Hd := fresh "Hd" in
        destruct Hsep as [m_out [m_rr [[?Heq Hd] [Hout Hrr]]]]; subst;
        unfold FElem_Fp2, AbstractField.FElem, Bignum.Bignum in Hout;
        let me := fresh in let ma := fresh in let Hms := fresh in
        let Hlen := fresh "Hlen" in let Ha := fresh "Ha" in
        destruct Hout as [me [ma [Hms [[?Hme Hlen] Ha]]]];
        subst me; apply Properties.map.split_empty_l in Hms; subst ma;
        (* Destruct old_out into 8 elements *)
        match type of Hlen with length ?x = _ =>
          let do_dest y := (let w := fresh "w" in
            destruct y as [|w y]; [simpl in Hlen; discriminate | ]) in
          do_dest x; do_dest x; do_dest x; do_dest x;
          do_dest x; do_dest x; do_dest x; do_dest x;
          (destruct x; [| simpl in Hlen; discriminate]); clear Hlen
        end;
        (* Unfold array, normalize addresses *)
        cbn [Array.array Scalars.scalar] in Ha;
        change (Memory.bytes_per_word 64) with 8 in Ha;
        normalize_word_addr_in Ha;
        (* Build combined sep *)
        let P := type of Ha in
        let Pcurried := match P with ?PP m_out => PP end in
        let Hcomb := fresh "Hcomb" in
        assert (Hcomb : (Pcurried ⋆ RR) (map.putmany m_out m_rr)) by
          (exists m_out, m_rr;
           split; [split; [reflexivity | exact Hd] |];
           split; [exact Ha | exact Hrr]);
        clear Ha Hrr Hd
      end;
      (* Phase 2: Process 8 stores *)
      repeat straightline;
      (* Phase 3: Close postcondition *)
      eexists (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: []);
      apply conj_swap;
      [ (* Sep: prove via Bignum_of_array_sep to avoid emp issues *)
        unfold AbstractField.FElem;
        apply Bignum_of_array_sep;
        [ cbn [length]; exact eq_refl | ];
        change (@AbstractField.felem_size_in_words
          _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep') with 8%nat;
        change (Memory.bytes_per_word 64) with 8;
        cbn [Array.array Scalars.scalar];
        repeat rewrite <- Properties.word.add_assoc;
        repeat rewrite <- word.ring_morph_add;
        repeat match goal with
        | |- context [word.of_Z (?a + ?b)] =>
          let v := eval cbv in (a + b) in change (a + b) with v
        end;
        repeat match goal with x := _ |- _ => subst x end;
        ecancel_assumption
      | (* Bounded: concrete values, vm_compute + split *)
        vm_compute; repeat split;
        first [exact eq_refl | discriminate | exact I]
      ].

    Lemma bn254_load_gamma1_p2_ok :
      forall functions
        (EnvContains : map.get functions "bn254_load_gamma1_p2" =
          Some (snd bn254_load_gamma1_p2)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bn254_load_gamma1_p2" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bn254_load_gamma1_p2. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant.
    Qed.

    Lemma bn254_load_gamma2_p2_ok :
      forall functions
        (EnvContains : map.get functions "bn254_load_gamma2_p2" =
          Some (snd bn254_load_gamma2_p2)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bn254_load_gamma2_p2" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bn254_load_gamma2_p2. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant.
    Qed.

    Lemma bn254_load_w_frob_p2_c1_ok :
      forall functions
        (EnvContains : map.get functions "bn254_load_w_frob_p2_c1" =
          Some (snd bn254_load_w_frob_p2_c1)),
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bn254_load_w_frob_p2_c1" tr mem [pout]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp2_bounded Fp2_tight out /\
              (FElem_Fp2 pout out ⋆ Rr) mem').
    Proof.
      intros functions EnvContains pout old_out Rr tr mem0 Hsep.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bn254_load_w_frob_p2_c1. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }
      solve_store_fp2_constant.
    Qed.

    (* ============================================================ *)
    (* C2: bn254_make_line                                          *)
    (* ============================================================ *)

    (* Fp6-level offset notations (from CubicFieldExtensions) *)
    Local Notation fp2_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep')).
    Local Notation Fp6_felem_size := (@AbstractField.felem_size_in_words _ bn254_Fp6_params' _ _ _ _ bn254_Fp6_rep').
    Local Notation fp6_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat Fp6_felem_size).

    (* Fp6 sub-component access *)
    Local Notation c0_felem := (@CubicFieldExtensionsSpecs.c0_felem _ _ _ _ bn254_pf_params bn254_Fp_rep).
    Local Notation c1_felem := (@CubicFieldExtensionsSpecs.c1_felem _ _ _ _ bn254_pf_params bn254_Fp_rep).
    Local Notation c2_felem := (@CubicFieldExtensionsSpecs.c2_felem _ _ _ _ bn254_pf_params bn254_Fp_rep).
    (* Fp12 sub-component access *)
    Local Notation d0_felem := (@DodecicFieldExtensionsSpecs.d0_felem _ _ _ _ bn254_pf_params bn254_Fp_rep).
    Local Notation d1_felem := (@DodecicFieldExtensionsSpecs.d1_felem _ _ _ _ bn254_pf_params bn254_Fp_rep).
    (* Fp6_c1/c2 offsets computed with the correct (Fp-level) representation *)
    Local Notation fp6_c1_off :=
      (@CubicFieldExtensions.fp6_c1_offset _ _ _ _ bn254_pf_params bn254_beta bn254_Fp_rep fp2_prefix).
    Local Notation fp6_c2_off :=
      (@CubicFieldExtensions.fp6_c2_offset _ _ _ _ bn254_pf_params bn254_beta bn254_Fp_rep fp2_prefix).

    Lemma bn254_make_line_ok :
      forall functions
        (EnvContains : map.get functions "bn254_make_line" =
          Some (snd bn254_make_line))
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2opp : spec_of_Fp2_opp functions)
        (HFp2mulfp : spec_of_bn254_Fp2_mul_fp functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions),
      forall pout plam pxt pyt pxp pyp
        (old_out : @AbstractField.felem _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep')
        (lam xt yt : Fp2_felem) (xp yp : Fp_felem) Rr tr mem,
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
             (FElem_Fp pyp yp ⋆ Rr)))))) mem ->
        WeakestPrecondition.call functions "bn254_make_line" tr mem
          [pout; plam; pxt; pyt; pxp; pyp]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              @AbstractField.bounded_by _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep'
                (@AbstractField.loose_bounds _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep') out /\
              (FElem_Fp12 pout out ⋆
               (FElem_Fp2 plam lam ⋆
                (FElem_Fp2 pxt xt ⋆
                 (FElem_Fp2 pyt yt ⋆
                  (FElem_Fp pxp xp ⋆
                   (FElem_Fp pyp yp ⋆ Rr)))))) mem').
    Proof.
      (* TODO: this proof walked the OLD make_line body in source order
         ("repeat straightline"). The body was corrected 2026-04-11
         to use the BN254 sparse-line layout (see BN254_Pairing.v
         [make_line] comment). Rewriting this 800-line proof to match
         the new call sequence is tracked by PLAN_PAIRING_SPECS.md
         Phase 4 (L4 equivalence theorem). *)
    Admitted.

End BN254_PairingHelpers.
