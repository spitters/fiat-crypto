Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.ArrayUtil.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.ScalarsUtil.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.

Import Syntax BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope sep_scope.

Section FelemCopy.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Local Notation F := (F M_pos).

    Existing Instance bls12_prime_parameters.
    Existing Instance bls12_field_names.

    Existing Instance bls12_field_parameters. (* : FieldParameters F := prime_field_parameters. *)
    Existing Instance bls12_field_representation. (* : FieldRepresentation F := field_representation M. *)

    Definition felem_copy_func : Syntax.func := (felem_copy, (["out"; "in"], (nil : list string), bedrock_func_body:(
      coq:(cmd.store access_size.word (expr.var "out") (expr.load access_size.word (expr.var "in")));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (8)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (16)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (24)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (32)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (40)))))
    ))).

    From bedrock2 Require Import ToCString Bytedump.
    Definition c_mod := (c_module (felem_copy_func :: nil)).
    Eval compute in c_mod.

    Ltac collect H1 H2 := let Hnew := (fresh "Hnew") in
    eassert (Hnew : id (fun m => (_ m) /\ (_ m)) _) by (cbv [id]; split; [eapply H1| eapply H2]); clear H1 H2.

        (* Lemma Naive_rep_eq : forall x y, x mod (Z.pow_pos 2 64) = y mod (Z.pow_pos 2 64) -> @Naive.wrap 64 y = Naive.wrap x.
      Proof.
        intros. eapply Naive.eq_unsigned. simpl. auto.
      Qed.

    (*færdiggør lemmaet og brug det til at justere hypotesen inden copy. Brug eventuelt en variant af store_word_of_sep, som kan håndtere flere (2  dette tilfælde) hyps*)
    Lemma array_append'_R : forall (T : Type) (element : BasicC64Semantics.word -> T -> BasicC64Semantics.mem -> Prop) (size : BasicC64Semantics.word) (xs ys : list T) (start : BasicC64Semantics.word) R mem,
      ((@array 64 BasicC64Semantics.word _ _ _ element size start (xs ++ ys) * R)%sep mem <-> (array element size start xs * ((@array 64 BasicC64Semantics.word _ _ _ element size (word.add start (word.mul size (word.of_Z (Z.of_nat (Datatypes.length xs))))) ys) * R))%sep mem).
    Proof.
      About array_append'.
      intros. split; intros.
        - generalize dependent mem. generalize dependent ys; generalize dependent R. generalize dependent start. induction xs; intros.
          + simpl.  rewrite Zmod_small; [| rewrite Zmod_small; lia].
            rewrite Zmod_small; try lia. rewrite Z.mul_0_r. rewrite Z.add_0_r. rewrite Naive.of_Z_unsigned.
            eexists; eexists; split; [| split]; eauto.
            1: eapply map.split_empty_l; auto.
            split; auto. Show Existentials.
          + simpl in H. eapply sep_assoc in H. destruct H, H, H, H0.
            specialize (IHxs _ _ _ _ H1).
            simpl. eapply sep_assoc. do 2 eexists; split; [| split]; eauto.

            destruct IHxs, H2, H2, H3.

            do 2 eexists; split; [| split]; eauto.
            simpl in H4.

            pose proof H4.
            assert ((@Naive.wrap 64
            ((Naive.unsigned start + Naive.unsigned size) mod Z.pow_pos 2 64 +
             (Naive.unsigned size *
              (Z.of_nat (Datatypes.length xs) mod Z.pow_pos 2 64))
             mod Z.pow_pos 2 64)) = (Naive.wrap
            (Naive.unsigned start +
             (Naive.unsigned size *
              (Z.pos (Pos.of_succ_nat (Datatypes.length xs)) mod Z.pow_pos 2 64))
             mod Z.pow_pos 2 64)))%Z.
             {
               eapply Naive_rep_eq.
               remember (Naive.unsigned start) as q. remember (Naive.unsigned size) as p.
                assert (forall x, Z.pos (Pos.of_succ_nat x) = ((Z.of_nat x) + 1)%Z) by lia.
                rewrite H6.
                remember (Z.of_nat (Datatypes.length xs)) as r.
                remember (Z.pow_pos 2 64) as mmod.
                rewrite Z.mul_mod; [| lia].
                rewrite Z.mod_mod; [| lia].
                rewrite <- Z.mul_mod; [| lia].
                rewrite (Z.add_mod q); [| lia].
                rewrite Z.mod_mod; [| lia].
                rewrite <- Z.add_mod; [| lia].
                rewrite (Z.mul_mod p); [| lia].
                rewrite Z.mod_mod; [| lia].
                rewrite <- Z.mul_mod; [| lia].
                rewrite <- Z.add_mod; [| lia].
                f_equal. lia.
             }
             rewrite <- H6. auto.
        - generalize dependent ys. generalize dependent R. generalize dependent mem. generalize dependent start.
          induction xs; intros.
            + simpl. simpl in H. sepsimpl_hyps. destruct H. rewrite Zmod_small in H0; [| rewrite Zmod_small; lia].
              rewrite Zmod_small in H0; try lia.
              rewrite Z.mul_0_r in H0. rewrite Z.add_0_r in H0. rewrite Naive.of_Z_unsigned in H0; auto.
            + simpl. simpl in H. simpl in IHxs.
              eassert ((element start a * _)%sep _) by ecancel_assumption. clear H. rename H0 into H.
            destruct H, H, H, H0.
            eapply sep_assoc.
            eexists; eexists; split; [| split]; eauto.
            eapply IHxs.
            destruct H1, H1, H1, H2.
            eexists; eexists; split; [| split]; eauto.
            assert ((@Naive.wrap 64
            ((Naive.unsigned start + Naive.unsigned size) mod Z.pow_pos 2 64 +
             (Naive.unsigned size *
              (Z.of_nat (Datatypes.length xs) mod Z.pow_pos 2 64))
             mod Z.pow_pos 2 64)) = (Naive.wrap
            (Naive.unsigned start +
             (Naive.unsigned size *
              (Z.pos (Pos.of_succ_nat (Datatypes.length xs)) mod Z.pow_pos 2 64))
             mod Z.pow_pos 2 64)))%Z.
             {
               eapply Naive_rep_eq.
               remember (Naive.unsigned start) as q. remember (Naive.unsigned size) as p.
                assert (forall x, Z.pos (Pos.of_succ_nat x) = ((Z.of_nat x) + 1)%Z) by lia.
                rewrite H4.
                remember (Z.of_nat (Datatypes.length xs)) as r.
                remember (Z.pow_pos 2 64) as mmod.
                rewrite Z.mul_mod; [| lia].
                rewrite Z.mod_mod; [| lia].
                rewrite <- Z.mul_mod; [| lia].
                rewrite (Z.add_mod q); [| lia].
                rewrite Z.mod_mod; [| lia].
                rewrite <- Z.add_mod; [| lia].
                rewrite (Z.mul_mod p); [| lia].
                rewrite Z.mod_mod; [| lia].
                rewrite <- Z.mul_mod; [| lia].
                rewrite <- Z.add_mod; [| lia].
                f_equal. lia.
             } simpl.
             rewrite H4.
             auto.
    Qed. *)

    Local Infix "+w" := word.add (at level 80).
    Local Infix "*w" := word.mul (at level 70).

    (* Existing Instance spec_of_felem_copy. *)
    (* Print Instances spec_of. *)

    (* Proof. *)
    (*     pose (@spec_of_felem_copy _ _ _ _ _ _ F bls12_field_parameters _ field_representation). *)
    (*     simpl in s.  cbv [spec_of_felem_copy] in s. exact s. *)
    (* Defined. *)

    (* Set Typeclasses Debug. *)
    (* Set Typeclasses Debug Verbosity 2. *)
    (* Compute felem_copy. *)


  (* Local Hint Extern 1 (spec_of _) => (unfold felem_copy; eapply spec_of_felem_copy) : typeclass_instances. *)
  (* Local Hint Extern 1 (spec_of felem_copy) => exact spec_of_felem_copy : typeclass_instances. *)
  (* Local Hint Extern 2 (spec_of felem_copy) => simple eapply spec_of_felem_copy : typeclass_instances. *)

    (* Declare Reduction red_name := cbv match beta delta [fst]. *)
    (* Ltac normalize_name_of_function proc ::= match proc with pair a _ => a end. *)
    (* Eval let fname _ := felem_copy_func in idtac fname. *)

    (* Goal (spec_of "bls12_felem_copy"). *)
        (* simple eapply spec_of_felem_copy. *)
        (* simple refine spec_of_felem_copy. *)
    (*     exact _. *)
    (*     simple eapply spec_of_felem_copy. *)
    (*     reflexivity. *)

    (* Ltac normalize_name_of_function proc ::= eval cbv delta [fst proc] beta iota in (fst proc). *)
    (* Existing Instance spec_of_flem_copy. *)
    (* Goal FieldRepresentation F. *)
        (* exact _. *)
    Instance bls12_felem_copy : spec_of felem_copy := spec_of_felem_copy.

    (* Local Hint Extern 1 (spec_of ?a) => (cbv [a]; exact _) : typeclass_instances. *)
    (* Check felem_copy_func. *)

    Lemma felem_copy_ok : program_logic_goal_for_function! felem_copy_func. (*Why does this take 5 minutes???!???*)
    Proof.
        cbv [bls12_felem_copy Field.spec_of_felem_copy]. cbv [program_logic_goal_for].
        intros.
        simpl.
        cbv [felem_copy_func]. simpl.
        repeat straightline.

        cbv [FElem Bignum.Bignum] in H0.
        sepsimpl.

        assert (felem_size_in_words= 6)%nat by auto.
        rewrite H2 in H0; clear H2.
        do 7 (destruct out; try discriminate). clear H0.
        assert (Hlist : forall {A : Type} (l : list A) a, a :: l = [a] ++ l) by auto.
        rewrite Hlist in H1.

        (*modifying H1*)
        eapply array_append_R' in H1.
        remember (word.of_Z (Memory.bytes_per_word 64)) as w1. eassert (forall l, Datatypes.length [l] = 1%nat) by auto.
        rewrite H0 in H1.
        remember (word.of_Z (Z.of_nat 1)) as w2.
        rewrite Hlist in H1; eapply array_append_R' in H1. rewrite H0 in H1. rewrite <- Heqw2 in H1.
        rewrite Hlist in H1; eapply array_append_R' in H1. rewrite H0 in H1. rewrite <- Heqw2 in H1.
        rewrite Hlist in H1; eapply array_append_R' in H1. rewrite H0 in H1. rewrite <- Heqw2 in H1.
        rewrite Hlist in H1; eapply array_append_R' in H1. rewrite H0 in H1. rewrite <- Heqw2 in H1.

        (*modifying H*)
        eapply sep_assoc in H. eapply sep_comm in H. eapply (sep_assoc _ R _) in H.
        cbv [FElem Bignum.Bignum] in H. sepsimpl. clear H. eapply sep_assoc in H2. sepsimpl_hyps.
        eapply sep_comm in H2.
        eapply sep_assoc in H2.
        rewrite Hlist in H2. eapply array_append_R' in H2. rewrite H0 in H2. rewrite <- Heqw2 in H2.
        rewrite <- Heqw1 in H2.
        rewrite Hlist in H2. eapply array_append_R' in H2. rewrite H0 in H2. rewrite <- Heqw2 in H2.
        rewrite Hlist in H2. eapply array_append_R' in H2. rewrite H0 in H2. rewrite <- Heqw2 in H2.
        rewrite Hlist in H2. eapply array_append_R' in H2. rewrite H0 in H2. rewrite <- Heqw2 in H2.
        rewrite Hlist in H2. eapply array_append_R' in H2. rewrite H0 in H2. rewrite <- Heqw2 in H2.
        remember (array scalar w1 px x) as Fx.

        cbv [array] in H1, H2. sepsimpl.
        subst Fx.
        eassert ((array scalar w1 px x * _)%sep mem) by ecancel_assumption. clear H2. rename H3 into H2.

        do 7 (destruct x; try discriminate).
        rewrite Hlist in H2. eapply array_append_R' in H2. rewrite H0 in H2. rewrite <- Heqw2 in H2.
        rewrite Hlist in H2. eapply array_append_R' in H2. rewrite H0 in H2. rewrite <- Heqw2 in H2.
        rewrite Hlist in H2. eapply array_append_R' in H2. rewrite H0 in H2. rewrite <- Heqw2 in H2.
        rewrite Hlist in H2. eapply array_append_R' in H2. rewrite H0 in H2. rewrite <- Heqw2 in H2.
        rewrite Hlist in H2. eapply array_append_R' in H2. rewrite H0 in H2. rewrite <- Heqw2 in H2.
        cbv [array] in H2. sepsimpl.

        Ltac straightline' :=
          match goal with
            | |- store Syntax.access_size.word _ _ _ _ =>
              eapply store_word_of_sep_2
            | _ => straightline
          end.


        do 4 straightline'.
        1: clear H1; ecancel_assumption.
        1: clear H2; ecancel_assumption.
        do 4 straightline'.

        Lemma word_add_assoc : forall (w1 : BasicC64Semantics.word) z1 z2, ((w1 +w (word.of_Z z1)) +w (word.of_Z z2)) = (w1 +w (word.of_Z (z1 + z2))).
        Proof.
          intros. rewrite <- word.add_assoc.
          rewrite word.ring_morph_add. auto.
        Qed.

        eassert (Hword : w1 *w w2 = word.of_Z 8) by auto.
        repeat rewrite Hword in *.
        do 4 straightline'.
        1: clear H3; ecancel_assumption.
        1: clear H4; ecancel_assumption.

        assert (Htemp : 8 + 8 = 16) by auto.
        repeat rewrite word_add_assoc in H5. rewrite Htemp in H5.
        repeat rewrite word_add_assoc in H6. rewrite Htemp in H6. clear Htemp.
        assert (Htemp : 8 + 16 = 24) by auto.
        repeat rewrite word_add_assoc in H5. rewrite Htemp in H5.
        repeat rewrite word_add_assoc in H6. rewrite Htemp in H6. clear Htemp.
        assert (Htemp : 8 + 24 = 32) by auto.
        repeat rewrite word_add_assoc in H5. rewrite Htemp in H5.
        repeat rewrite word_add_assoc in H6. rewrite Htemp in H6. clear Htemp.
        assert (Htemp : 8 + 32 = 40) by auto.
        repeat rewrite word_add_assoc in H5. rewrite Htemp in H5.
        repeat rewrite word_add_assoc in H6. rewrite Htemp in H6. clear Htemp.
        do 4 straightline'.
        1: {
          clear H5; ecancel_assumption.
        }
        1: {
          clear H6; ecancel_assumption.
        }

        do 6 straightline'.
        1: {
          clear H7; ecancel_assumption.
        }
        1: {
          clear H8; ecancel_assumption.
        }

        do 6 straightline'.
        1: {
          clear H9; ecancel_assumption.
        }
        1: {
          clear H10; ecancel_assumption.
        }

        do 6 straightline'.
        1: {
          clear H11; ecancel_assumption.
        }
        1: {
          clear H12; ecancel_assumption.
        }
        do 2 straightline'.

        split; auto. split; auto.

        cbv [FElem Bignum.Bignum].
        sepsimpl; eauto.
        eapply (sep_assoc _ _ Rout).
        eexists map.empty. eexists; split; [eapply map.split_empty_l; reflexivity| ]. split; [split; eauto| ].
        rewrite Hlist. epose proof array_append_R'.
        eapply H15. subst w1. subst w2. rewrite H0.
        remember ((word.of_Z (Memory.bytes_per_word 64))) as w1.
        remember (word.of_Z (Z.of_nat 1)) as w2.
        rewrite Hlist. eapply H15. rewrite H0. rewrite <- Heqw2.
        rewrite Hlist. eapply H15. rewrite H0. rewrite <- Heqw2.
        rewrite Hlist. eapply H15. rewrite H0. rewrite <- Heqw2.
        rewrite Hlist. eapply H15. rewrite H0. rewrite <- Heqw2.
        cbv [array].
        sepsimpl.

        repeat rewrite Hword.
        repeat rewrite word_add_assoc.
        assert (Htemp : 8 + 8 = 16) by auto. rewrite Htemp. clear Htemp.
        assert (Htemp : 8 + 16 = 24) by auto. rewrite Htemp. clear Htemp.
        assert (Htemp : 8 + 24 = 32) by auto. rewrite Htemp. clear Htemp.
        assert (Htemp : 8 + 32 = 40) by auto. rewrite Htemp. clear Htemp.

        subst v. subst a3 a2 a1 a0 a.
        - ecancel_assumption.
    Qed.

End FelemCopy.
