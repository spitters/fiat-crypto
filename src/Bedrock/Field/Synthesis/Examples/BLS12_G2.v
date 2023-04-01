Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_Fp2.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAdd.
Require Import Coq.Strings.String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Spec.ModularArithmetic.

Section bls12_G2.

    Existing Instances
        Defaults64.default_parameters
        Defaults64.default_parameters_ok
        bls12_prime_parameters
        (* bls12_field_parameters *)
        bls12_field_names
        bls12_field_representation
        bls12_Fp2_field_names
        bls12_Fp2_field_parameters
        bls12_Fp2_field_representation.

    Local Notation F := (F M_pos).
    Local Notation Fp2 := (F * F)%type.

    (* Instance F_names : FieldNames := field_names. *)
    (* Instance F_parameters : FieldParameters F := field_parameters. *)
    (* Instance F_representation : FieldRepresentation F := field_representation M. *)
    (* Instance Fp2_names : FieldNames := Fp2_names. *)
    (* Instance Fp2_parameters : FieldParameters Fp2 := Fp2_parameters. *)
    (* Instance Fp2_representation : FieldRepresentation Fp2 := Fp2_representation. *)

    (* Instance prime_field_parameters : Field.FieldParameters. *)
    (* Proof. *)
    (*     exact bls12_prime.field_parameters. *)
    (* Defined. *)

    (* Instance prime_field_representation : (@FieldRepresentation Field.prime_field_parameters 64 Bitwidth64.BW64 BasicC64Semantics.word BasicC64Semantics.mem). *)
    (* Proof. *)
    (*     exact (field_representation M). *)
    (* Defined. *)

    (* Instance field_parameters : Field.FieldParameters. *)
    (* Proof. *)
    (*     exact Fp2_parameters. *)
    (* Defined. *)

    (* Instance field_representation : @Field.FieldRepresentation field_parameters _ _ _ _. *)
    (* Proof. *)
    (*     exact (@Fp2_representation _ _ _ _ prime_field_parameters prime_field_representation). *)
    (* Defined. *)

    (* Check @ladderstep_body. (*Give Proper Name!!!!!!!!*) *)
    (* Check ladderstep_body. *)

    Definition bls12_G2_add := ladderstep_body (F:=Fp2).
    (*make Field.field_representation from rep in WordByWordMontgomery.*)

    Definition mpos : positive.
    Proof.
        exact M_pos.
    Defined.

    (*hard-code curve-defining parameter b*)
    Definition br := 4.
    Definition bi := 4.
    Definition three_br := 12.
    Definition three_bi := 12.
    Definition uw := (uweight 64).
    Definition n := felem_size_in_words.
    Definition three_br_list := Partition.partition uw 6 three_br.
    Definition three_bi_list := Partition.partition uw 6 three_bi.

    Definition word := BasicC64Semantics.word.
    Definition three_br_mont := @WordByWordMontgomery.to_montgomerymod 64 6 M (@m' _ 64) three_br_list.
    Definition three_bi_mont := @WordByWordMontgomery.to_montgomerymod 64 6 M (@m' _ 64) three_bi_list.
    Definition three_br_words := List.map (@word.of_Z 64 word) three_br_mont.
    Definition three_bi_words := List.map (@word.of_Z 64 word) three_bi_mont.

    Existing Instance spec_of_bls12_Fp2_add.
    Existing Instance spec_of_bls12_Fp2_sub.
    Existing Instance spec_of_bls12_Fp2_mul.

    (* Instance spec_of_bls12_Fp2_add : spec_of (fst bls12_Fp2_add). *)
    (* Proof. exact spec_of_bls12_Fp2_add. Defined. *)
        (* exact (@spec_of_add _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    (* Compute fst bls12_Fp2_sub. *)

    (* Instance spec_of_bls12_Fp2_sub : spec_of (fst bls12_Fp2_sub). *)
    (* Proof. exact spec_of_bls12_Fp2_sub. Defined. *)
        (* exact (@spec_of_sub _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    (* Instance spec_of_bls12_Fp2_mul : spec_of (fst bls12_Fp2_mul). *)
    (* Proof. exact spec_of_bls12_Fp2_mul. Defined. *)
        (* exact (@spec_of_mul _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    (* Instance spec_of_bls12_square : spec_of (fst bls12_square).
    Proof. exact spec_of_square. Defined. *)

    Instance spec_of_G2_add : spec_of "ladderstep" := (spec_of_ladderstep (three_br_words ++ three_bi_words)).
    (* Proof. *)
    (*     exact (spec_of_ladderstep (three_br_words ++ three_bi_words)). *)
    (* Defined. *)

    Definition three_b_F : Fp2.
    Proof.
        exact (ModularArithmetic.F.of_Z M_pos three_br, ModularArithmetic.F.of_Z M_pos three_bi).
    Defined.

    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_Fp2.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.

    (* Let prefix := "bls12_Fp2". *)
    (* Instance Fp2_names : FieldNames := field_names_prefixed prefix. *)

    (* Locate spec_of_from_list. *)

    (* Existing Instance spec_of_bls12_mul. *)
    (* Existing Instance spec_of_bls12_add. *)
    (* Existing Instance spec_of_bls12_sub. *)
    (* Existing Instance bls12_from_list_F.spec_of_from_list. *)
    (* Proof. *)
    (*     exact (@Field.spec_of_from_list _ _ _ _ _ _ F F_parameters F_names F_representation _) . *)
    (* Defined. *)

    Existing Instance spec_of_bls12_Fp2_from_list.

    (* Instance spec_of_from_list_Fp2 : spec_of (@from_list Fp2_names) := bls12_from_list_Fp2.spec_of_from_list. *)
    (* Proof. *)
    (*     exact (@Field.spec_of_from_list _ _ _ _ _ _ Fp2 Fp2_parameters Fp2_names Fp2_representation three_b_Fp2) . *)
    (* Defined. *)

    (* Instance spec_of_from_list : spec_of "Fp2_from_list". *)
    (* Proof. *)
    (*     exact (spec_of_from_list). *)
    (* Defined. *)

    Check spec_of_from_list.

    Lemma bls12_G2_ok : program_logic_goal_for_function! bls12_G2_add. (*Why does this take 7 minutes??!?!?*)
    pose proof ladderstep_correct. cbv [spec_of_G2_add].
    Check spec_of_ladderstep.
    cbv [bls12_G2_add].
    cbv [program_logic_goal_for]. intros.
    apply H.
        1: simpl; auto.
        3: apply H1.
        3: cbv [spec_of_bls12_add] in H4; apply H4.
        3: cbv [spec_of_bls12_sub] in H13; apply H13.
        2: {
            cbv [__rupicola_program_marker]. auto.
        }
        2: {
            cbv [CurveAdd.spec_of_from_list]. cbv [spec_of_from_list] in H0.
            pose proof H0. cbv [spec_of_bls12_Fp2_from_list] in H34.
            cbv [three_b_Fp2] in H34.
            
            assert (three_b_Fp2 = feval (bls12_G2.three_br_words ++ bls12_G2.three_bi_words)).
            {
                cbv [three_b_Fp2]. cbv [F].
                unfold feval.
                cbv [bls12_Fp2_field_representation].
                cbv [Fp2_field_representation].

                Lemma three_br_list_valid : WordByWordMontgomery.valid 64 6 M bls12_G2.three_br_list.
                Proof.
                    cbv [bls12_G2.three_br_list].
                    eapply WordByWordMontgomeryUtil.valid_partition_small.
                    7: {
                        erewrite Zmod_small; try lia. cbv [bls12_G2.three_br M]. simpl. lia.
                    }
                    all: try lia.
                    4: cbv [M]; simpl; lia.
                    3: cbv [M]; simpl; lia.
                    2: eapply m'_correct.
                    eapply r'_correct.
                Qed.

                Lemma three_br_mont_valid : WordByWordMontgomery.valid 64 6 M bls12_G2.three_br_mont.
                Proof.
                    cbv [bls12_G2.three_br_mont].
                    eapply WordByWordMontgomeryUtil.valid_to_mont.
                    7: apply three_br_list_valid.
                    all: try lia.
                    4: cbv [M]; simpl; lia.
                    3: cbv [M WordByWordMontgomeryUtil.r]; try lia.
                    2: eapply m'_correct.
                    apply r'_correct.
                    simpl; lia.
                Qed.

                Lemma fst_felem_three_b : fst_felem (bls12_G2.three_br_words ++ bls12_G2.three_bi_words) = bls12_G2.three_br_words.
                Proof.
                    cbv [fst_felem].
                    assert (length (bls12_G2.three_br_words) = 6)%nat.
                    {
                        cbv [bls12_G2.three_br_words].
                        rewrite map_length.
                        eapply WordByWordMontgomery.length_small. eapply three_br_mont_valid.
                    }
                    erewrite QuadraticFieldExtensions.firstn_app'; [reflexivity| ]. rewrite H. simpl. cbv [WordByWordMontgomery.n].
                    cbv [WordByWordMontgomery.s]. simpl. clear H. auto.
                Qed.

                Lemma three_bi_list_valid : WordByWordMontgomery.valid 64 6 M bls12_G2.three_bi_list.
                Proof.
                    cbv [bls12_G2.three_bi_list].
                    eapply WordByWordMontgomeryUtil.valid_partition_small.
                    7: {
                        erewrite Zmod_small; try lia. cbv [bls12_G2.three_bi M]. simpl. lia.
                    }
                    all: try lia.
                    4: cbv [M]; simpl; lia.
                    3: cbv [M]; simpl; lia.
                    2: eapply m'_correct.
                    eapply r'_correct.
                Qed.

                Lemma three_bi_mont_valid : WordByWordMontgomery.valid 64 6 M bls12_G2.three_bi_mont.
                Proof.
                    cbv [bls12_G2.three_bi_mont].
                    eapply WordByWordMontgomeryUtil.valid_to_mont.
                    7: apply three_bi_list_valid.
                    all: try lia.
                    4: cbv [M]; simpl; lia.
                    3: cbv [M WordByWordMontgomeryUtil.r]; try lia.
                    2: eapply m'_correct.
                    apply r'_correct.
                    simpl; lia.
                Qed.

                Lemma snd_felem_three_b : snd_felem (bls12_G2.three_br_words ++ bls12_G2.three_bi_words) = bls12_G2.three_bi_words.
                Proof.
                    cbv [snd_felem].
                    assert (length (bls12_G2.three_br_words) = 6)%nat.
                    {
                        cbv [bls12_G2.three_br_words].
                        rewrite map_length.
                        eapply WordByWordMontgomery.length_small. eapply three_br_mont_valid.
                    }
                    rewrite QuadraticFieldExtensions.skipn_app; [reflexivity| ].
                    rewrite H. simpl. cbv [WordByWordMontgomery.n].
                    cbv [WordByWordMontgomery.s]. simpl. clear H. auto.
                Qed.

                pose proof fst_felem_three_b. cbv [bls12_G2.word] in *. rewrite H35.
                pose proof snd_felem_three_b. cbv [bls12_G2.word] in *. rewrite H36.
                clear H35 H36.

                eapply Prod.path_pair.
                1: {
                cbv [feval bls12_field_representation field_representation Signature.field_representation Representation.frep Representation.eval_words prime_field_parameters FofZ].
                eapply f_equal.
                    (* bls12_G2.three_br_words. *)
                    cbv [bls12_G2.three_br_words eval_trans bls12_G2.three_br_mont Representation.eval_words].
                    (* apply f_equal. *)
                    rewrite unsigned_of_Z_valid.
                    2: {
                        eapply WordByWordMontgomeryUtil.valid_to_mont.
                        7: eapply three_br_list_valid.
                        all: try lia.
                        4: cbv [M]; simpl; lia.
                        3: cbv [M WordByWordMontgomeryUtil.r]; simpl; lia.
                        2: apply m'_correct.
                        apply r'_correct.
                        }
                    erewrite WordByWordMontgomeryUtil.from_to_mont_inv; try lia.
                    6: apply three_br_list_valid.
                    5: cbv [M]; simpl; lia.
                    4: cbv [M WordByWordMontgomeryUtil.r]; simpl; lia.
                    3: apply m'_correct.
                    2: apply r'_correct.
                    cbv [bls12_G2.three_br_list].
                    rewrite eval_partition; auto.
                    apply uwprops. lia.
                }
                cbv [feval bls12_field_representation field_representation Signature.field_representation Representation.frep Representation.eval_words prime_field_parameters FofZ].
                cbv [feval bls12_G2.three_bi_words eval_trans bls12_G2.three_bi_mont Representation.eval_words].
                eapply f_equal.
                rewrite unsigned_of_Z_valid.
                2: {
                    eapply WordByWordMontgomeryUtil.valid_to_mont.
                    7: eapply three_bi_list_valid.
                    all: try lia.
                    4: cbv [M]; simpl; lia.
                    3: cbv [M WordByWordMontgomeryUtil.r]; simpl; lia.
                    2: apply m'_correct.
                    apply r'_correct.
                    }
                erewrite WordByWordMontgomeryUtil.from_to_mont_inv; try lia.
                6: apply three_bi_list_valid.
                5: cbv [M]; simpl; lia.
                4: cbv [M WordByWordMontgomeryUtil.r]; simpl; lia.
                3: apply m'_correct.
                2: apply r'_correct.
                cbv [bls12_G2.three_bi_list].
                rewrite eval_partition; auto.
                apply uwprops. lia.
            }
            cbv [three_b_Fp2] in H35.
            rewrite H35 in H34.
            apply H34.
        }

        cbv [CompilationAbstract.maybe_bounded]. split.
        1: {
            pose proof fst_felem_three_b.
            cbv [bounded_by loose_bounds bls12_field_representation WordByWordMontgomery.field_representation Signature.field_representation Representation.frep].
            cbv [bls12_Fp2_field_representation Fp2_field_representation].
            cbv [bounded_by loose_bounds bls12_field_representation WordByWordMontgomery.field_representation Signature.field_representation Representation.frep].
            (* cbv [loose_bounds prime_field_representation WordByWordMontgomery.field_representation Signature.field_representation Representation.frep]. *)
            cbv [list_in_bounds].
            cbv [bls12_G2.word] in *.
            cbv [fst_felem felem_size_in_words] in *.
            cbv [bls12_field_representation WordByWordMontgomery.field_representation Signature.field_representation Representation.frep] in *.
            rewrite H34.
            cbv [bls12_G2.three_br_words].
            rewrite unsigned_of_Z_valid; apply three_br_mont_valid.
        }
        pose proof snd_felem_three_b.
        cbv [bounded_by loose_bounds bls12_field_representation WordByWordMontgomery.field_representation Signature.field_representation Representation.frep].
        cbv [bls12_Fp2_field_representation Fp2_field_representation].
        cbv [loose_bounds bls12_field_representation WordByWordMontgomery.field_representation Signature.field_representation Representation.frep].
        cbv [list_in_bounds].
        cbv [bls12_G2.word] in *.
        cbv [snd_felem felem_size_in_words] in *.
        cbv [bls12_field_representation WordByWordMontgomery.field_representation Signature.field_representation Representation.frep] in H34.
        rewrite H34.
        cbv [bls12_G2.three_bi_words].
        rewrite unsigned_of_Z_valid; apply three_bi_mont_valid.
Qed.

End bls12_G2.
    From bedrock2 Require Import ToCString Bytedump.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
    Definition c_mod := (c_module (bls12_G2_add :: nil)).

    Eval compute in c_mod.
