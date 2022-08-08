Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAddAlt.
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
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_G1.

Section bls12_Fp2.

    Existing Instances Defaults64.default_parameters Defaults64.default_parameters_ok.

    Instance prime_field_parameters : PrimeField.PrimeFieldParameters.
    Proof.
        exact bls12_prime.field_parameters.
    Defined.

    Instance field_parameters : AbstractField.FieldParameters.
    Proof.
        exact (@PrimeField.prime_field_parameters prime_field_parameters).
    Defined.

    Instance field_representation : @AbstractField.FieldRepresentation field_parameters _ _ _ _.
    Proof.
        exact (WordByWordMontgomery.field_representation m).
    Defined.

    Check @ladderstep_body. (*Give Proper Name!!!!!!!!*)

    Definition bls12_G1_add := ladderstep_body.
    (*make AbstractField.field_representation from rep in WordByWordMontgomery.*)

    Definition mpos : positive.
    Proof.
        destruct bls12_Fp2.prime_field_parameters. eapply M_pos.
    Defined.

    (*hard-code curve-defining parameter b*)
    Definition b := 4.
    Definition three_b := 12.
    Definition uw := (uweight 64).
    Definition n := felem_size_in_words.
    Definition three_b_list := Partition.partition uw n three_b.
    Definition word := BasicC64Semantics.word.
    Definition three_b_mont := @WordByWordMontgomery.to_montgomerymod 64 n m (@m' prime_field_parameters 64) three_b_list.
    Definition three_b_words := List.map (@word.of_Z 64 word) three_b_mont.

    Instance spec_of_bls12_add : spec_of (fst bls12_add).
    Proof. exact spec_of_add. Defined.
        (* exact (@spec_of_add _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    Instance spec_of_bls12_sub : spec_of (fst bls12_sub).
    Proof. exact spec_of_sub. Defined.
        (* exact (@spec_of_sub _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    Instance spec_of_bls12_mul : spec_of (fst bls12_mul).
    Proof. exact spec_of_mul. Defined.
        (* exact (@spec_of_mul _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    (* Instance spec_of_bls12_square : spec_of (fst bls12_square).
    Proof. exact spec_of_square. Defined. *)

    Instance spec_of_G1_add : spec_of "ladderstep".
    Proof.
        exact (spec_of_ladderstep three_b_words).
    Defined.

    Definition three_b_F : (@F field_parameters).
    Proof.
        exact (ModularArithmetic.F.of_Z M_pos three_b).
    Defined.

    Instance spec_of_from_list : spec_of from_list.
    Proof.
        exact (spec_of_from_list).
    Defined.

    Instance spec_of_bls12_felem_copy : spec_of ((@felem_copy bls12_prime.field_parameters)).
    Proof.
        exact (@spec_of_felem_copy _ _ _ _ _ _ field_parameters (field_representation )).
    Defined.

    Instance spec_of_G1_add_alt : spec_of "G1_add_alt".
    Proof.
        epose proof spec_of_curve_add_alt. eapply X. exact three_b_words.
    Defined.

    Require Import bedrock2.NotationsCustomEntry.
    Require Import bedrock2.WeakestPrecondition.
    Import Syntax BinInt String List.ListNotations.
    Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

    Local Notation felem_offset := 48.

    Definition expr_2nd_felem (x : Syntax.expr) := expr.op bopname.add x (expr.literal felem_offset).
    
    Definition G1_add_alt : bedrock2.Syntax.func :=
        ("G1_add_alt", (["x1"; "x2"; "y1"; "y2"; "z1"; "z2"; "outx"; "outy"; "outz"], []:list String.string, bedrock_func_body:(
            stackalloc felem_size_in_bytes as allocx1;
            stackalloc felem_size_in_bytes as allocx2;
            stackalloc felem_size_in_bytes as allocy1;
            stackalloc felem_size_in_bytes as allocy2;
            stackalloc felem_size_in_bytes as allocz1;
            stackalloc felem_size_in_bytes as allocz2;
            coq:(cmd.call [] ((@felem_copy bls12_prime.field_parameters)) [expr.var ("allocx1"); expr.var ("x1")]);
            coq:(cmd.call [] ((@felem_copy bls12_prime.field_parameters)) [expr.var ("allocx2"); expr.var ("x2")]);
            coq:(cmd.call [] ((@felem_copy bls12_prime.field_parameters)) [expr.var ("allocy1"); expr.var ("y1")]);
            coq:(cmd.call [] ((@felem_copy bls12_prime.field_parameters)) [expr.var ("allocy2"); expr.var ("y2")]);
            coq:(cmd.call [] ((@felem_copy bls12_prime.field_parameters)) [expr.var ("allocz1"); expr.var ("z1")]);
            coq:(cmd.call [] ((@felem_copy bls12_prime.field_parameters)) [expr.var ("allocz2"); expr.var ("z2")]);
            
            coq:(cmd.call [] ("ladderstep") [expr.var ("allocx1"); expr.var ("allocx2"); expr.var ("allocy1"); expr.var("allocy2"); expr.var ("allocz1"); expr.var ("allocz2"); expr.var ("outx"); expr.var ("outy"); expr.var ("outz")])
        ))).

        (*Proof alternate version*)

        (*need some tactics/lemmas from this file*)
    Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.

    Ltac bind_body_of_function' f := (*using alternative bind_body that does not normalize body of funcction, as it is horribly slow.*)
    let fname := open_constr:(_) in
    let fargs := open_constr:(_) in
    let frets := open_constr:(_) in
    let fbody := open_constr:(_) in
    let funif := open_constr:((fname, (fargs, frets, fbody))) in
    unify f funif;
    let G := lazymatch goal with |- ?G => G end in
    let P := lazymatch eval pattern f in G with ?P _ => P end in
    change (bindcmd fbody (fun c : Syntax.cmd => P (fname, (fargs, frets, c))));
    cbv beta iota delta [bindcmd]; intros.


    Ltac enter' f :=
        cbv beta delta [program_logic_goal_for]; intros;
        bind_body_of_function' f;
        lazymatch goal with |- ?s _ => cbv beta delta [s] end.

    Ltac collect H1 H2 := let Hnew := (fresh "Hnew") in
    eassert (Hnew : id (fun m => (_ m) /\ (_ m)) _) by (cbv [id]; split; [eapply H1| eapply H2]); clear H1 H2.

    Ltac solve_locals7 l1 l2 l3 l4 l5 l6 l7 :=
        repeat (repeat straightline; eexists; split; [
            subst l1 l2 l3 l4 l5 l6 l7;
            repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same|
        ]); repeat straightline.

    Lemma alloc_to_FElem' : forall R m a l, Datatypes.length l = 48%nat -> (R * (array ptsto (word.of_Z 1) a l))%sep m -> exists f, (R * AbstractField.FElem a f)%sep m.
    Proof.
        intros. destruct H0, H0, H0, H1.
        do 3 eexists. split; eauto; split; eauto.
        cbv [AbstractField.FElem].
        eapply Bignum.Bignum_of_bytes in H2.
            - simpl in H2. eapply H2.
            - auto.
    Qed.




    Lemma bls12_G1_alt_ok : program_logic_goal_for_function! G1_add_alt. (*Why does this take 17 minutes??!?!?*)
   
    pose proof ladderstep_correct.
    enter' G1_add_alt. clear H0 H1 H2 H3 H4. cbv [binop_spec spec_of_curve_add_alt] in *.
    intros.
    do 9 (
        let bounds := (fresh "Hbounds") in
         destruct H0 as [bounds H0]
    ).    
    
    unfold1_call_goal. cbv match beta delta [call_body].
    assert (("G1_add_alt" =? "G1_add_alt")%string = true) by auto.
    rewrite H1.
    cbv match beta delta [func].
    repeat straightline.
    
    (*Preparing hyps for stack allocation*)
    collect H0 H2.
    collect H3 Hnew.
    assert (Hmod : felem_size_in_bytes mod Memory.bytes_per_word 64 = 0).
    {
        simpl. cbv [felem_size_in_bytes Memory.bytes_per_word]. simpl.
        assert (Htemp : 71 / 8 = 8) by lia. rewrite Htemp; clear Htemp.
        lia.
    }

    (*first alloc*)
    split; [apply Hmod| ]. repeat straightline. clear Hnew1. eapply alloc_to_FElem' in Hnew0.
    split; [apply Hmod| ]. repeat straightline. clear H9. eapply alloc_to_FElem' in H8.
    split; [apply Hmod| ]. repeat straightline. clear H12. eapply alloc_to_FElem' in H8.
    split; [apply Hmod| ]. repeat straightline. clear H15. eapply alloc_to_FElem' in H8.
    split; [apply Hmod| ]. repeat straightline. clear H18. eapply alloc_to_FElem' in H8.
    split; [apply Hmod| ]. repeat straightline. clear H21. eapply alloc_to_FElem' in H8.


    
    cbv [CurveAddAlt.my_field_representation] in *.
    destruct H8.

    straightline_call.
    1: {
        remember ((AbstractField.FElem a x)) as P.
        remember (AbstractField.FElem a0 x0) as P0.
        remember (AbstractField.FElem a1 x1) as P1.
        remember (AbstractField.FElem a2 x2) as P2.
        remember (AbstractField.FElem a3 x3) as P3.
        remember (AbstractField.FElem a4 x4) as P4.

    
        eassert ((_ * (P * P0 * P1 * P2 * P3 * P4))%sep mem) by ecancel_assumption.
        remember ((P * P0 * P1 * P2 * P3 * P4))%sep as P5. clear H8.
        split; [| subst; ecancel_assumption].
        rename H21 into H8.
        eapply sep_and_l_fwd in H8; destruct H8 as [? H8]; eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?]; subst; ecancel_assumption.        
      }

    repeat straightline.


    straightline_call.
    1: {
        remember ((AbstractField.FElem a X1)) as P.
        remember (AbstractField.FElem a0 x0) as P0.
        remember (AbstractField.FElem a1 x1) as P1.
        remember (AbstractField.FElem a2 x2) as P2.
        remember (AbstractField.FElem a3 x3) as P3.
        remember (AbstractField.FElem a4 x4) as P4.

    
        eassert ((_ * (P * P0 * P1 * P2 * P3 * P4))%sep a6) by ecancel_assumption.
        remember ((P * P0 * P1 * P2 * P3 * P4))%sep as P5. clear H24. clear H8.
        split; [| subst; ecancel_assumption].
        rename H21 into H8.
        eapply sep_and_l_fwd in H8; destruct H8 as [? H8]; eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?]; subst; ecancel_assumption.        
      }
    repeat straightline.

    straightline_call.
    1: {
        remember ((AbstractField.FElem a X1)) as P.
        remember (AbstractField.FElem a0 X2) as P0.
        remember (AbstractField.FElem a1 x1) as P1.
        remember (AbstractField.FElem a2 x2) as P2.
        remember (AbstractField.FElem a3 x3) as P3.
        remember (AbstractField.FElem a4 x4) as P4.

    
        eassert ((_ * (P * P0 * P1 * P2 * P3 * P4))%sep a8) by ecancel_assumption.
        remember ((P * P0 * P1 * P2 * P3 * P4))%sep as P5. clear H24 H25 H8.
        split; [| subst; ecancel_assumption].
        rename H21 into H8.
        eapply sep_and_l_fwd in H8; destruct H8 as [? H8]; eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?]; subst; ecancel_assumption.        
      }
    repeat straightline.

    straightline_call.
    1: {
        remember ((AbstractField.FElem a X1)) as P.
        remember (AbstractField.FElem a0 X2) as P0.
        remember (AbstractField.FElem a1 Y1) as P1.
        remember (AbstractField.FElem a2 x2) as P2.
        remember (AbstractField.FElem a3 x3) as P3.
        remember (AbstractField.FElem a4 x4) as P4.

    
        eassert ((_ * (P * P0 * P1 * P2 * P3 * P4))%sep a9) by ecancel_assumption.
        remember ((P * P0 * P1 * P2 * P3 * P4))%sep as P5. clear H24 H25 H8 H26.
        split; [| subst; ecancel_assumption].
        rename H21 into H8.
        eapply sep_and_l_fwd in H8; destruct H8 as [? H8]; eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?]; subst; ecancel_assumption.        
      }
    repeat straightline.

    straightline_call.
    1: {
        remember ((AbstractField.FElem a X1)) as P.
        remember (AbstractField.FElem a0 X2) as P0.
        remember (AbstractField.FElem a1 Y1) as P1.
        remember (AbstractField.FElem a2 Y2) as P2.
        remember (AbstractField.FElem a3 x3) as P3.
        remember (AbstractField.FElem a4 x4) as P4.

    
        eassert ((_ * (P * P0 * P1 * P2 * P3 * P4))%sep a10) by ecancel_assumption.
        remember ((P * P0 * P1 * P2 * P3 * P4))%sep as P5. clear H24 H25 H8 H26 H27.
        split; [| subst; ecancel_assumption].
        rename H21 into H8.
        eapply sep_and_l_fwd in H8; destruct H8 as [? H8]; eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?]; subst; ecancel_assumption.        
      }
    repeat straightline.

    straightline_call.
    1: {
        remember ((AbstractField.FElem a X1)) as P.
        remember (AbstractField.FElem a0 X2) as P0.
        remember (AbstractField.FElem a1 Y1) as P1.
        remember (AbstractField.FElem a2 Y2) as P2.
        remember (AbstractField.FElem a3 Z1) as P3.
        remember (AbstractField.FElem a4 x4) as P4.

    
        eassert ((_ * (P * P0 * P1 * P2 * P3 * P4))%sep a11) by ecancel_assumption.
        remember ((P * P0 * P1 * P2 * P3 * P4))%sep as P5. clear H24 H25 H8 H26 H27 H28.
        split; [| subst; ecancel_assumption].
        rename H21 into H8.
        eapply sep_and_l_fwd in H8; destruct H8 as [? H8]; eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?]; subst; ecancel_assumption.        
      }
    repeat straightline.

    straightline_call.
    1: {
        remember ((AbstractField.FElem a X1)) as P.
        remember (AbstractField.FElem a0 X2) as P0.
        remember (AbstractField.FElem a1 Y1) as P1.
        remember (AbstractField.FElem a2 Y2) as P2.
        remember (AbstractField.FElem a3 Z1) as P3.
        remember (AbstractField.FElem a4 Z2) as P4.

    
        eassert ((_ * (P * P0 * P1 * P2 * P3 * P4))%sep a12) by ecancel_assumption.
        remember ((P * P0 * P1 * P2 * P3 * P4))%sep as P5. clear H24 H25 H8 H26 H27 H28 H29.
        rename H21 into H8.
        eapply sep_and_l_fwd in H8; destruct H8 as [? H8]; eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?].
        subst.


        Lemma FElem_to_FElem' : forall a m l, bounded_by tight_bounds l -> AbstractField.FElem a l m -> CompilationAbstract.FElem (Some tight_bounds) a (feval l) m.
        Proof.
            intros. cbv [CompilationAbstract.FElem]. cbv [Lift1Prop.ex1]. eexists. sepsimpl.
                3: ecancel_assumption.
                all: auto.
        Qed.

        Lemma FElem_to_FElem'_R : forall a m l R, bounded_by tight_bounds l -> (AbstractField.FElem a l * R)%sep m -> (R * CompilationAbstract.FElem (Some tight_bounds) a (feval l))%sep m.
        Proof.
            intros. destruct H0, H0, H0, H1. eapply map.split_comm in H0.
            eexists; eexists; split; eauto. split; eauto.
            eapply FElem_to_FElem'; eauto.
        Qed.

        Lemma FElem_to_FElem'_R' : forall a m l R1 R2, bounded_by tight_bounds l -> (R1 * AbstractField.FElem a l * R2)%sep m -> (R1 * R2 * CompilationAbstract.FElem (Some tight_bounds) a (feval l))%sep m.
        Proof.
            intros.
            eapply sep_comm in H0. eapply sep_assoc in H0.
            destruct H0, H0, H0, H1.
            eexists; eexists; split; eauto. split; [eapply sep_comm| ]; eauto.
            eapply FElem_to_FElem'; eauto.
        Qed.

        eassert ((Rout * _)%sep a12) by ecancel_assumption. clear H21.
        destruct H24, H21, H21, H24.
        eexists; eexists; split.
        1: eapply map.split_comm; eapply H21.
        split; [| eapply H24].

        eapply FElem_to_FElem'_R; cycle -1.
        1: eapply (sep_assoc (AbstractField.FElem _ _)); eapply FElem_to_FElem'_R; cycle -1.
        1:  eapply (sep_assoc (AbstractField.FElem _ _));
            eapply (sep_assoc (AbstractField.FElem _ _ * AbstractField.FElem _ _)%sep);
            eapply FElem_to_FElem'_R; cycle -1.

        1:  eapply (sep_assoc (AbstractField.FElem _ _));
            eapply (sep_assoc (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * AbstractField.FElem _ _))%sep);
            eapply FElem_to_FElem'_R; cycle -1.

        1:  eapply (sep_assoc (AbstractField.FElem _ _)).
            eapply (sep_assoc (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * AbstractField.FElem _ _)))%sep);
            eapply FElem_to_FElem'_R; cycle -1.

        1:  eapply (sep_assoc (AbstractField.FElem _ _)).
            eapply (sep_assoc (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * AbstractField.FElem _ _))))%sep);
            eapply FElem_to_FElem'_R; cycle -1.

        1:  eapply (sep_assoc (AbstractField.FElem _ _)).
            eapply (sep_assoc (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * AbstractField.FElem _ _)))))%sep);
            eapply FElem_to_FElem'_R; cycle -1.

        1:  eapply (sep_assoc (AbstractField.FElem _ _)).
            eapply (sep_assoc (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * (AbstractField.FElem _ _ * AbstractField.FElem _ _))))))%sep);
            eapply FElem_to_FElem'_R; cycle -1.

        1:  eapply (sep_assoc (AbstractField.FElem _ _)).
        1:  eapply FElem_to_FElem'_R.

        2: ecancel_assumption.

        all: eassumption.
    }

    repeat straightline.
    clear H29 H28 H27 H26 H25 H24 H8.
    {
        cbv [my_field_representation bls12_Fp2.word] in *.
        eassert (Htemp : (CompilationAbstract.FElem (Some tight_bounds) a4 (feval Z2) * _)%sep a13) by ecancel_assumption. clear H31. rename Htemp into H31.
        do 4 destruct H31 as [? H31].
    }
    eexists. eexists. split; [eauto| split].
    
    2: {

    }
    
    [eauto| ]. repeat straightline.
    split; [eauto| ].




        cbv [CompilationAbstract.FElem]. sepsimpl.
        Search (Lift1Prop.ex1).
        
        ecancel_assumption.
        subst; ecancel_assumption.        
      }
    repeat straightline.
    


    eapply Proper_call.
    {
        cbv [pointwise_relation]. repeat straightline. cbv [Basics.impl]. repeat straightline.
        eexists. split.
        1: solve_locals7 l5 l4 l3 l2 l1 l0 l.
        {
            subst l5 l4 l3 l2 l1 l0 l. simpl.
        }
        subst l5. subst l4. subst l3. subst l2. subst l1.
    }





    eexists.
    
    {

    }
    
    cbv [spec_of_G1_add].
    cbv [G1_add_alt].
    cbv [program_logic_goal_for]. intros.
    cbv [spec_of_G1_add_alt].
    cbv [spec_of_curve_add_alt].
    repeat straightline.
    eapply Proper_call.
    {
        cbv [pointwise_relation]. repeat straightline. cbv [Basics.impl]. intros. split.
        simpl.
    }
    straightline_call.
    eapply H.
        1: simpl; auto.
        3: auto.
        3: cbv [spec_of_bls12_add] in H4; apply H4.
        3: cbv [spec_of_bls12_sub] in H13; apply H13.
        2: {
            cbv [__rupicola_program_marker]. auto.
        }
        2: {
            cbv [CurveAdd.spec_of_from_list]. cbv [spec_of_from_list] in H0.
            assert (three_b_F = feval three_b_words).
            {
                simpl. cbv [Representation.eval_words eval_trans three_b_F].
                Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
                pose proof (three_b_mont_mod).
                assert (three_b_words = bls12_Fp2.three_b_words).
                {
                    cbv [bls12_Fp2.three_b_words three_b_words]. eapply f_equal.
                    cbv [bls12_Fp2.three_b_mont three_b_mont bls12_Fp2.three_b_list].
                    cbv. reflexivity.
                }
                rewrite <- H35.
                apply f_equal.
                cbv [word] in H34.
                assert (@M bls12_prime.field_parameters = m).
                {
                    simpl. cbv [M]. cbv [m]. cbv [M_pos]. simpl. reflexivity.
                }
                rewrite H36 in H34.
                rewrite H34.
                cbv [three_b_list]. rewrite eval_partition; [| eapply uwprops].
                2 : {
                    clear H H1 H2 H4 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33.
                    clear H34 H35 H36. lia.
                }
                clear H H1 H2 H4 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33.
                cbv [three_b bls12_Fp2.three_b]. erewrite Zmod_small; try lia.
                cbv [n felem_size_in_words]. simpl. cbv [WordByWordMontgomery.n]. simpl.
                cbv [uw uweight ModOps.weight]. simpl. lia.
            }
            rewrite H34 in H0.
            eapply H0.
        }
        clear H H1 H2 H4 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33.
        cbv [CompilationAbstract.maybe_bounded bounded_by loose_bounds bls12_Fp2.three_b_words].
        eassert (my_field_representation = _).
        {
            cbv [my_field_representation]. eauto. 
        }
        rewrite H.
        eassert (bls12_Fp2.field_representation = _).
        {
            cbv [bls12_Fp2.field_representation]. auto.
        }
        cbv [bls12_Fp2.field_representation]. remember (List.map word.of_Z bls12_Fp2.three_b_mont) as eyy.
        simpl. subst eyy.


        assert (three_b_mont = bls12_Fp2.three_b_mont).
        {
            pose proof (three_b_mont_eq). rewrite H2.
            cbv [bls12_Fp2.three_b_mont bls12_Fp2.three_b_list bls12_Fp2.three_b].
            cbv [three_b_list three_b].
            assert (n = bls12_Fp2.n).
            {
                cbv [bls12_Fp2.n]. cbv [n]. reflexivity.
            }
            rewrite <- H4.
            assert (bls12_Fp2.uw = uw).
            {
                cbv [bls12_Fp2.uw]. cbv [uw]. reflexivity.
            }
            rewrite H6. reflexivity.
        }
        rewrite <- H2.
        rewrite unsigned_of_Z_valid.

        2: cbv [n felem_size_in_words]; simpl.
        all: eapply three_b_mont_valid.
Qed. *)

End bls12_Fp2.
    (* From bedrock2 Require Import ToCString Bytedump.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
    Definition c_mod := (c_module (bls12_mul :: nil)).

    Redirect "blstest.c" Eval compute in c_mod. *)
