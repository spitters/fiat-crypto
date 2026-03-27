(** * BLS12-377 Power-by-u WP Proof
    Computes f^{u} where u = 0x8508c00000000001 (64 bits)
    using square-and-multiply. Core building block for DSD final exp.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_377_Pairing.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS12_377_PowU.

    (* === BLS12-377 Instance Boilerplate === *)
    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bls377_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_377_prime.m).

    Instance bls377_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls377_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls377_mul"; PrimeField.add := "bls377_add";
      PrimeField.sub := "bls377_sub"; PrimeField.opp := "bls377_opp";
      PrimeField.square := "bls377_square"; PrimeField.scmula24 := "bls377_scmula24";
      PrimeField.inv := "bls377_inv"; PrimeField.from_bytes := "bls377_from_bytes";
      PrimeField.to_bytes := "bls377_to_bytes"; PrimeField.select_znz := "bls377_select_znz";
      PrimeField.felem_copy := "bls377_felem_copy"; PrimeField.from_word := "bls377_from_word";
      PrimeField.from_list := "bls377_from_list";
    |}.

    Instance bls377_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_377. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Instance bls377_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls377_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls377_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls377_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls377_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls377_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls377_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls377_frep |}.

    Instance bls377_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls377_Fp_rep] in *.
      cbv [Field.bounded_by bls377_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bls377_Fp2_".
    Let fp6_prefix := "bls377_Fp6_".
    Let fp12_prefix := "bls377_Fp12_".

    Let bls377_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-5).
    Let bls377_xi_re : F PrimeField.M_pos := @F.zero PrimeField.M_pos.
    Let bls377_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Instance bls377_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      Fp2_field_parameters bls377_beta fp2_prefix.
    Instance bls377_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      Fp2_field_representation bls377_beta fp2_prefix.
    Instance bls377_Fp2_names' : FieldNames (F:=Fp2) :=
      field_names_prefixed fp2_prefix.
    Instance bls377_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      Fp6_field_parameters bls377_beta bls377_xi_re bls377_xi_im (fp6_prefix:=fp6_prefix).
    Instance bls377_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      Fp6_field_representation bls377_beta bls377_xi_re bls377_xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
    Instance bls377_Fp6_names' : FieldNames (F:=Fp6) :=
      field_names_prefixed fp6_prefix.
    Instance bls377_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      Fp12_field_parameters bls377_beta bls377_xi_re bls377_xi_im (fp12_prefix:=fp12_prefix).
    Instance bls377_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      Fp12_field_representation bls377_beta bls377_xi_re bls377_xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
    Instance bls377_Fp12_names' : FieldNames (F:=Fp12) :=
      field_names_prefixed fp12_prefix.

    Instance bls377_Fp_names' : FieldNames (F:=Fp) :=
      field_names_prefixed "bls377_".

    (* === Abbreviations (matching BLS12_377_Pairing.v) === *)
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').

    Local Typeclasses Opaque bls377_Fp12_params'.
    Local Typeclasses Opaque bls377_Fp6_params'.
    Local Typeclasses Opaque bls377_Fp2_params'.

    (* === Operation specs (needed for weaken_call) === *)
    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bls377_Fp12_rep') AbstractField.un_square.
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bls377_Fp12_rep') AbstractField.bin_mul.
    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bls377_Fp12_rep').

    (* BLS parameter u *)
    Local Definition bls_u : Z := 0x8508c00000000001.

    (* ==================================================================== *)
    (* Loop invariant for pow_u                                             *)
    (* ==================================================================== *)

    Definition pow_u_inv
      (a_result a_base a_out : word)
      (base_val : Fp12_felem)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\ (v <= 63)%nat /\
      exists (result_val : Fp12_felem),
        Fp12_bounded Fp12_tight result_val /\
        (FElem_Fp12 a_result result_val ⋆
         (FElem_Fp12 a_base base_val ⋆ Rr)) m /\
        map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
        map.get l "result" = Some a_result /\
        map.get l "base" = Some a_base /\
        map.get l "out" = Some a_out.

    (* ==================================================================== *)
    (* Main WP theorem                                                      *)
    (* ==================================================================== *)

    (* Spec for bls377_Fp12_pow_u: computes base^{u} *)
    Instance spec_of_pow_u : spec_of "bls377_Fp12_pow_u" :=
      fnspec! "bls377_Fp12_pow_u" (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆
           (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    Local Instance bls377_Fp12_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep' :=
      DodecicFieldExtensionsSpecs.Fp12_field_representation_ok bls377_beta bls377_xi_re bls377_xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

    Lemma bls377_Fp12_pow_u_ok :
      forall functions
        (EnvContains : map.get functions "bls377_Fp12_pow_u" =
          Some (snd BLS12_377_Pairing.bls377_Fp12_pow_u))
        (HFsqr : spec_of_Fp12_sqr functions)
        (HFmul : spec_of_Fp12_mul functions)
        (HFcopy : spec_of_Fp12_felem_copy functions),
      spec_of_pow_u functions.
    Proof.
      intros functions EnvContains HFsqr HFmul HFcopy.
      unfold spec_of_pow_u.
      intros pout pbase tr mem0 old_out base_val Rr [Hbbase Hsep].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv match beta delta [WeakestPrecondition.func BLS12_377_Pairing.bls377_Fp12_pow_u].
      eexists. split. { exact eq_refl. }
      (* Process stackalloc manually *)
      straightline. split. { apply Z_mod_mult. }
      intros a_result mSr mCr HaSr HmSr.
      (* Convert anybytes to FElem *)
      assert (Hri_ex : exists ri, FElem_Fp12 a_result ri mSr).
      { pose proof (@AbstractField.FElem_from_bytes _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep') as Hconv.
        cbv [Lift1Prop.iff1 Placeholder] in Hconv.
        apply Hconv; [typeclasses eauto | typeclasses eauto | exact HaSr]. }
      destruct Hri_ex as [ri Hri].
      assert (Hsep_all : ((FElem_Fp12 pbase mem0 ⋆ (FElem_Fp12 pout tr ⋆ old_out)) ⋆ FElem_Fp12 a_result ri) mCr).
      { exists Rr, mSr. exact (conj HmSr (conj Hsep Hri)). }
      clear Hsep HaSr HmSr Hri.
      repeat straightline.
      (* First call: Fp12_copy(result, base) *)
      eapply Semantics.weaken_call.
      1: { eapply HFcopy. split. { ecancel_assumption. } ecancel_assumption. }
      intros ? ? ? [? [? Hsep_copy]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
      repeat straightline.
      (* Now at while loop. Apply Loops.while_localsmap *)
      eapply Loops.while_localsmap
        with (v0 := 63%nat) (lt := Nat.lt)
             (invariant := fun v t m l =>
                pow_u_inv a_result pbase pout mem0 (FElem_Fp12 pout tr ⋆ old_out) t' v t m l).
      { exact lt_wf. }
      { (* Initial invariant *)
        unfold pow_u_inv. split. { reflexivity. } split. { lia. }
        exists mem0. split. { exact Hbbase. }
        split. { exact Hsep_copy. }
        subst l0 l i. solve_mapgets_n. }
      { (* Loop body + exit *)
        intros v t_v m_v l_v Hinv.
        unfold pow_u_inv in Hinv.
        destruct Hinv as [Ht [Hv_le [result_v [Hbr [Hsep_v [Hget_i [Hget_result [Hget_base Hget_out]]]]]]]].
        subst.
        exists (word.of_Z (Z.of_nat v)). cbv [Markers.split].
        split. { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
                 eexists. split; [exact Hget_i | reflexivity]. }
        split.
        { (* TRUE branch: v ≠ 0, process loop body *)
          intro Hne.
          unfold BLS12_377_Pairing.pow_u_loop_body, BLS12_377_Pairing.cmd_seq_list.
          (* i = i - 1 *)
          eexists. split.
          { unfold DEXPR. repeat (first [ solve [eval_dexprs_fast] | straightline ]). }
          (* sqr(result, result) *)
          eexists. split. { solve [eval_dexprs_fast]. }
          unfold spec_of_Fp12_sqr, AbstractField.unop_spec in HFsqr.
          eapply Semantics.weaken_call.
          1: { eapply (HFsqr a_result a_result result_v result_v
                 (FElem_Fp12 pbase mem0 ⋆ (FElem_Fp12 pout tr ⋆ old_out))).
               split. { exact Hbr. }
               split. { eexists. ecancel_assumption. }
               ecancel_assumption. }
          cbv beta.
          intros ? ? ? [? [? [sqr_out [Hfeval_sqr [Hb_sqr Hsep_sqr]]]]]. subst.
          cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
          (* bit = (0x8508c00000000001 >> i) & 1 *)
          repeat straightline.
          (* Bit extraction DEXPR *)
          eexists. split.
          { unfold DEXPR. repeat (first [ solve [eval_dexprs_fast] | straightline ]). }
          cbv beta delta [dlet.dlet Semantics.interp_binop].
          cbv beta iota delta [Semantics.interp_binop].
          set (bit_val := word.and (word.sru (word.of_Z 9586122913090633729)
            (word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1))) (word.of_Z 1)).
          set (new_i := word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1)).
          set (l_new := map.put (map.put l_v "i" new_i) "bit" bit_val).
          repeat straightline.
          (* Conditional: if bit { mul } else { skip } *)
          unfold1_cmd_goal. cbv beta match delta [cmd_body].
          exists bit_val. split.
          { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
            eexists. split. { subst l_new. rewrite map.get_put_same. reflexivity. }
            reflexivity. }
          split.
          { (* bit ≠ 0: mul(result, result, base) *)
            intro Hbit_ne.
            repeat straightline.
            unfold spec_of_Fp12_mul, AbstractField.binop_spec in HFmul.
            eexists. split.
            { unfold dexprs, list_map, list_map_body.
              cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
              repeat (eexists; split; [| try reflexivity]).
              all: subst l_new.
              all: repeat (first [rewrite map.get_put_same; reflexivity
                                 | rewrite map.get_put_diff by congruence]).
              all: exact Hget_result || exact Hget_base. }
            eapply Semantics.weaken_call.
            1: { eapply (HFmul a_result a_result pbase sqr_out sqr_out mem0
                   (FElem_Fp12 pbase mem0 ⋆ (FElem_Fp12 pout tr ⋆ old_out))).
                 split. { exact Hb_sqr. }
                 split. { exact Hbbase. }
                 split. { exists (FElem_Fp12 pbase mem0 ⋆ (FElem_Fp12 pout tr ⋆ old_out)).
                          exact Hsep_sqr. }
                 split. { exists (FElem_Fp12 a_result sqr_out ⋆ (FElem_Fp12 pout tr ⋆ old_out)).
                          ecancel_assumption. }
                 ecancel_assumption. }
            cbv beta. intros ? ? ? [? [? [mul_out [Hfeval_mul [Hb_mul Hsep_mul]]]]]. subst.
            cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
            exists (v - 1)%nat. split.
            { unfold pow_u_inv. split. { reflexivity. } split. { lia. }
              exists mul_out. split. { exact Hb_mul. }
              split. { exact Hsep_mul. }
              subst l_new new_i bit_val.
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_same. f_equal. ZnWords. }
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_diff by congruence. exact Hget_result. }
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_diff by congruence. exact Hget_base. }
              rewrite map.get_put_diff by congruence.
              rewrite map.get_put_diff by congruence. exact Hget_out. }
            assert (Hv_pos : (0 < v)%nat) by
              (destruct v; [exfalso; apply Hne; vm_compute; reflexivity | lia]).
            lia. }
          { (* bit = 0: skip, re-establish invariant with sqr_out *)
            intro Hbit_zero. repeat straightline.
            exists (v - 1)%nat. split.
            { unfold pow_u_inv. split. { reflexivity. } split. { lia. }
              exists sqr_out. split. { exact Hb_sqr. }
              split. { exact Hsep_sqr. }
              subst l_new new_i bit_val.
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_same. f_equal. ZnWords. }
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_diff by congruence. exact Hget_result. }
              split. { rewrite map.get_put_diff by congruence.
                       rewrite map.get_put_diff by congruence. exact Hget_base. }
              rewrite map.get_put_diff by congruence.
              rewrite map.get_put_diff by congruence. exact Hget_out. }
            assert (Hv_pos : (0 < v)%nat) by
              (destruct v; [exfalso; apply Hne; vm_compute; reflexivity | lia]).
            lia. } }
        { (* FALSE branch: v = 0, exit loop *)
          intro Heq.
          unfold BLS12_377_Pairing.cmd_seq_list. repeat straightline.
          exists [pout; a_result]. split.
          { unfold dexprs, list_map, list_map_body.
            cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
            repeat (eexists; split; [| try reflexivity]).
            all: first [exact Hget_out | exact Hget_result]. }
          eapply Semantics.weaken_call.
          1: { eapply HFcopy. split. { ecancel_assumption. } ecancel_assumption. }
          cbv beta. intros ? ? ? [Hrets [Htr_eq Hsep_out]]. symmetry in Htr_eq. subst.
          cbv [map.putmany_of_list_zip]. eexists. split. { reflexivity. }
          destruct Hsep_out as [m_out [m_rest [Hsp_out [Hf_out Hrest]]]].
          destruct Hrest as [m_ares [m_frame [Hsp_rest [Hf_ares Hf_frame]]]].
          assert (Hanybytes : Memory.anybytes a_result felem_size_in_bytes m_ares).
          { pose proof (@AbstractField.FElem_from_bytes _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep') as Hconv.
            apply Hconv; [typeclasses eauto | typeclasses eauto |].
            exists result_v. exact Hf_ares. }
          exists (map.putmany m_out m_frame), m_ares.
          split. { exact Hanybytes. }
          split. { (* map.split *)
            unfold map.split in *.
            destruct Hsp_out as [He_out Hd_out]. destruct Hsp_rest as [He_rest Hd_rest]. subst.
            assert (Hd_oa : map.disjoint m_out m_ares) by
              (eapply (proj1 (@map.disjoint_putmany_r _ _ _ ltac:(typeclasses eauto) _ ltac:(typeclasses eauto) _ _ _) Hd_out)).
            assert (Hd_fa : map.disjoint m_frame m_ares) by
              (apply map.disjoint_comm; exact Hd_rest).
            split.
            { rewrite (@map.putmany_comm _ _ _ ltac:(typeclasses eauto) _ ltac:(typeclasses eauto) m_ares m_frame Hd_rest).
              rewrite <- (@map.putmany_assoc _ _ _ ltac:(typeclasses eauto) _ ltac:(typeclasses eauto) m_out m_frame m_ares).
              reflexivity. }
            eapply (proj2 (@map.disjoint_putmany_l _ _ _ ltac:(typeclasses eauto) _ ltac:(typeclasses eauto) m_out m_frame m_ares)).
            exact (conj Hd_oa Hd_fa). }
          cbv [list_map list_map_body get].
          refine (conj eq_refl (conj eq_refl (ex_intro _ result_v (conj Hbr _)))).
          exists m_out, m_frame.
          unfold map.split in *.
          destruct Hsp_out as [He_out Hd_out]. destruct Hsp_rest as [He_rest Hd_rest]. subst.
          refine (conj (conj eq_refl _) (conj Hf_out Hf_frame)).
          eapply (proj1 (@map.disjoint_putmany_r _ _ _ ltac:(typeclasses eauto) _ ltac:(typeclasses eauto) m_out m_ares m_frame) Hd_out). } }
    Qed.

End BLS12_377_PowU.
