Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.

Import Syntax BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type} {field_parameters : FieldParameters F}
          {field_parameters_ok : Field.FieldParameters_ok F}.
  Context {field_names : FieldNames F}.
  Context {field_representation : FieldRepresentation F}
    {field_representation_ok : FieldRepresentation_ok F}
    {group_cmov : string}.

  Notation F_cmov := select_znz.

  Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

  Instance spec_of_group_cmov : spec_of group_cmov :=
    fnspec! group_cmov
      (pXout pYout pZout pX1 pY1 pZ1 pX2 pY2 pZ2 pc : word)
      / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) c R,
      { requires tr mem :=
          (FElem (Some tight_bounds) pX1 X1
           * FElem (Some tight_bounds) pX2 X2
           * FElem (Some tight_bounds) pY1 Y1
           * FElem (Some tight_bounds) pY2 Y2
           * FElem (Some tight_bounds) pZ1 Z1
           * FElem (Some tight_bounds) pZ2 Z2
           * FElem (Some tight_bounds) pXout Xoutold
           * FElem (Some tight_bounds) pYout Youtold
           * FElem (Some tight_bounds) pZout Zoutold
           * Bignum.Bignum 1 pc [c]
           * R)%sep mem /\
            ZRange.is_bounded_by_bool (word.unsigned c) bit_range = true;
        ensures tr' mem' :=
          exists Xout Yout Zout (* output values *)
            : F , exists cout,
            (
              (if ((word.unsigned c) =? 1)
               then (Xout = X2)
               else (Xout = X1))
              /\
                (if ((word.unsigned c) =? 1)
                 then (Yout = Y2)
                 else (Yout = Y1))
              /\
                (if ((word.unsigned c) =? 1)
                 then (Zout = Z2)
                 else (Zout = Z1))
            )
            /\ (FElem (Some tight_bounds) pX1 X1
               * FElem (Some tight_bounds) pX2 X2
               * FElem (Some tight_bounds) pY1 Y1
               * FElem (Some tight_bounds) pY2 Y2
               * FElem (Some tight_bounds) pZ1 Z1
               * FElem (Some tight_bounds) pZ2 Z2
               * FElem (Some tight_bounds) pXout Xout
               * FElem (Some tight_bounds) pYout Yout
               * FElem (Some tight_bounds) pZout Zout
               * Bignum.Bignum 1 pc [cout]
               * R)%sep mem'}.


  Definition cmov_func : bedrock2.Syntax.func :=
    (group_cmov, (["outx"; "outy"; "outz"; "x1"; "y1"; "z1"; "x2"; "y2"; "z2"; "pc"], []:list String.string, bedrock_func_body:(
                                                                                                                                  coq:(cmd.call [] (F_cmov) [expr.var ("outx"); expr.load access_size.word (expr.var ("pc")); expr.var ("x1"); expr.var("x2")]);
                                                                                                                                  coq:(cmd.call [] (F_cmov) [expr.var ("outy"); expr.load access_size.word (expr.var ("pc")); expr.var ("y1"); expr.var("y2")]);
                                                                                                                                  coq:(cmd.call [] (F_cmov) [expr.var ("outz"); expr.load access_size.word (expr.var ("pc")); expr.var ("z1"); expr.var("z2")])))).

  (* From bedrock2 Require Import ToCString Bytedump. *)
  (* Definition c_mod := (c_module (cmov_func :: nil)). *)
  (* Eval native_compute in c_mod. *)

  Ltac solve_locals l1 := subst l1; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

  Instance spec_of_select_znz : spec_of select_znz := spec_of_selectznz.

  (* TODO: Move? *)
  Lemma bignum_1_scalar pc c :
    forall m R, (@Bignum.Bignum width word mem 1 pc [c] ⋆ R) m <-> (scalar pc c ⋆ R) m.
  intros. apply Util.iff1_sep_cancel_both.
    unfold Bignum.Bignum. simpl. split.
    - rewrite sep_emp_l, sep_emp_r. easy.
    - rewrite sep_emp_l, sep_emp_r. easy.
    - easy.
  Qed.

  Lemma cmov_ok : program_logic_goal_for_function! cmov_func.
  Proof.
    cbv [cmov_func]. cbv [program_logic_goal_for].
    cbv [spec_of_group_cmov].
    repeat straightline.
    unfold1_call_goal.
    cbv match beta delta [call_body].
    assert ((group_cmov =? group_cmov)%string = true).
    { eapply eqb_eq. auto. }
    rewrite H4.
    cbv match beta delta [func].
    repeat straightline.

    eexists; split.
    1: {
      repeat straightline. eexists; split.
      - solve_locals l.
      - repeat straightline. eexists; split; [solve_locals l| ].
        repeat straightline. eexists. split.
        {
          eapply load_word_of_sep.
          rewrite <- bignum_1_scalar.
          ecancel_assumption.
        }
        repeat straightline. eexists; split; [solve_locals l| ].
        repeat straightline. eexists; split; [solve_locals l| ].
        repeat straightline.
    }

    (*prepare context for first function call. *)
    eassert (Hx1: ((FElem (Some tight_bounds) pX1 X1) * _)%sep mem0) by ecancel_assumption.
    eassert (Hx2: ((FElem (Some tight_bounds) pX2 X2) * _)%sep mem0) by ecancel_assumption.
    eassert (Hxout: ((FElem (Some tight_bounds) pXout Xoutold) * _)%sep mem0) by ecancel_assumption.
    clear H2.
    destruct Hxout as [mxout Hxout]. destruct Hxout as [mxout' Hxout]. destruct Hxout as [Hxoutsplit Hxout]. destruct Hxout as [Hxout' Hxout].
    destruct Hx1 as [mx1 Hx1]. destruct Hx1 as [mx1' Hx1]. destruct Hx1 as [Hx1split Hx1]. destruct Hx1 as [Hx1' Hx1].
    destruct Hx2 as [mx2 Hx2]. destruct Hx2 as [mx2' Hx2]. destruct Hx2 as [Hx2split Hx2]. destruct Hx2 as [Hx2' Hx2].
    cbv [FElem] in Hxout', Hx1', Hx2'. sepsimpl_hyps.
    (* destruct H5, H2, H2, H5. cbv [FElem] in H5. sepsimpl_hyps. *)

    straightline_call.

    1: {
      split; [| split; [| split]].
      1: {
        eexists. eexists.
        split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hxout.
      }
      1: {
        eexists. eexists.
        split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hx1.
      }
      1: {
        eexists. eexists.
        split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hx2.
      }
      auto.
    }
    repeat straightline.
    eexists; split.
    1: {
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split.
      { destruct (word.unsigned c =? 1).
        - eapply load_word_of_sep.
          rewrite <- bignum_1_scalar.
          ecancel_assumption.
        - eapply load_word_of_sep.
          rewrite <- bignum_1_scalar.
          ecancel_assumption. }
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline. eexists. split; [solve_locals l| ].
      repeat straightline.
    }
    destruct (word.unsigned c =? 1) eqn:eq.
    { clear Hxout Hx1 Hx2 H6 H12 H2 H8 H7 H9 H11 Hxoutsplit Hx1split Hx2split mx2 mx2' mxout mxout' mx1 mx1'. rename H5 into Hfeval. rename H10 into Hx0.
      (*preparing context for second function call*)
      eassert (Hx1: ((FElem (Some tight_bounds) pY1 Y1) * _)%sep a0) by ecancel_assumption.
      eassert (Hx2: ((FElem (Some tight_bounds) pY2 Y2) * _)%sep a0) by ecancel_assumption.
      eassert (Hxout: ((FElem (Some tight_bounds) pYout Youtold) * _)%sep a0) by ecancel_assumption.
      clear H14.
      destruct Hxout as [mxout Hxout]. destruct Hxout as [mxout' Hxout]. destruct Hxout as [Hxoutsplit Hxout]. destruct Hxout as [Hxout' Hxout].
      destruct Hx1 as [mx1 Hx1]. destruct Hx1 as [mx1' Hx1]. destruct Hx1 as [Hx1split Hx1]. destruct Hx1 as [Hx1' Hx1].
      destruct Hx2 as [mx2 Hx2]. destruct Hx2 as [mx2' Hx2]. destruct Hx2 as [Hx2split Hx2]. destruct Hx2 as [Hx2' Hx2].
      cbv [FElem] in Hxout', Hx1', Hx2'. sepsimpl_hyps.

      straightline_call.
      1: { split; [| split; [| split]].
        1: { eexists. eexists. split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hxout. }
        1: { eexists. eexists. split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hx1. }
        1: { eexists. eexists. split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hx2. }
        auto.
      }
      repeat straightline.
      eexists; split.
      1: {
        repeat straightline. eexists. split; [solve_locals l| ].
        repeat straightline. eexists. split; [solve_locals l| ].
        repeat straightline. eexists. split.
        {
          destruct (word.unsigned c =? 1).
          - eapply load_word_of_sep.
            rewrite <- bignum_1_scalar.
            ecancel_assumption.
          - eapply load_word_of_sep.
            rewrite <- bignum_1_scalar.
            ecancel_assumption.
        }

        repeat straightline. eexists. split; [solve_locals l| ].
        repeat straightline. eexists. split; [solve_locals l| ].
        repeat straightline.
      }

      rewrite eq in H14.
      clear Hxout Hx1 Hx2 H6 H12 H2 H8 H7 H9 H11 Hxoutsplit Hx1split Hx2split mx2 mx2' mxout mxout' mx1 mx1'. rename H10 into Hx01. rename H5 into Hfeval1.

      eassert (Hx1: ((FElem (Some tight_bounds) pZ1 Z1) * _)%sep a2) by ecancel_assumption.
      eassert (Hx2: ((FElem (Some tight_bounds) pZ2 Z2) * _)%sep a2) by ecancel_assumption.
      eassert (Hxout: ((FElem (Some tight_bounds) pZout Zoutold) * _)%sep a2) by ecancel_assumption.
      clear H14.
      destruct Hxout as [mxout Hxout]. destruct Hxout as [mxout' Hxout]. destruct Hxout as [Hxoutsplit Hxout]. destruct Hxout as [Hxout' Hxout].
      destruct Hx1 as [mx1 Hx1]. destruct Hx1 as [mx1' Hx1]. destruct Hx1 as [Hx1split Hx1]. destruct Hx1 as [Hx1' Hx1].
      destruct Hx2 as [mx2 Hx2]. destruct Hx2 as [mx2' Hx2]. destruct Hx2 as [Hx2split Hx2]. destruct Hx2 as [Hx2' Hx2].
      cbv [FElem] in Hxout', Hx1', Hx2'. sepsimpl_hyps.

      straightline_call.
      1: {
        split; [| split; [| split]].
        1: {
          eexists. eexists.
          split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hxout.
        }
        1: {
          eexists. eexists.
          split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hx1.
        }
        1: {
          eexists. eexists.
          split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hx2.
        }
        auto.
      }

      repeat straightline. split; auto. eexists. eexists. eexists; eexists.
      split; [repeat (try split)| ].
      - rewrite eq in H14.
        destruct H14, H13, H13, H14.
        eassert ((Field.FElem pYout _ * _)%sep x9) by ecancel_assumption. clear H15.
        destruct H16, H15, H15, H16.
        eassert ((Field.FElem pXout _ * _)%sep x11) by ecancel_assumption. clear H17.
        destruct H18, H17, H17, H18.
        eassert (((FElem (Some tight_bounds) pXout _ * FElem (Some tight_bounds) pYout _ * FElem (Some tight_bounds) pZout _ * _)%sep) a3).
        { (*should be automated!!*)
          eexists (map.putmany (map.putmany x8 x10) x12). eexists x13. split.
          {
            destruct H17. split. destruct H13.
            - rewrite H13. destruct H15. rewrite H15. rewrite H17.
              rewrite map.putmany_assoc.
              rewrite map.putmany_assoc. auto.
            - eapply map.disjoint_putmany_l; split; auto.
              eapply map.disjoint_putmany_l; split; auto.
              destruct H13, H15.
              + eapply map.disjoint_comm. eapply map.sub_domain_disjoint.
                * eapply map.disjoint_comm. eauto.
                * Search map.sub_domain. eapply map.sub_domain_trans.
                  2: {
                    rewrite H15. rewrite map.putmany_comm; eauto. eapply map.sub_domain_putmany_r.
                    eapply map.sub_domain_trans.
                    2: {
                      rewrite H17. erewrite map.putmany_comm; auto. eapply map.sub_domain_putmany_r.
                      eapply map.sub_domain_refl.
                    }
                    eapply map.sub_domain_refl.
                  }
                  eapply map.sub_domain_refl.
              + eapply map.disjoint_comm. destruct H15. eapply map.sub_domain_disjoint.
                * eapply map.disjoint_comm. eauto.
                * rewrite H17. erewrite map.putmany_comm; auto. eapply map.sub_domain_putmany_r.
                  eapply map.sub_domain_refl.
          }
          split; [| eapply H19].
          eexists. eexists. split; [| split].
          3: {
            cbv [FElem]. cbv [Lift1Prop.ex1]. eexists. sepsimpl.
            3: eapply H14.
            2: eauto.
            eauto.
          }
          1: {
            erewrite <- map.putmany_assoc.
            erewrite map.putmany_comm; auto.
            - eapply map.split_disjoint_putmany. eapply map.disjoint_putmany_l. split.
              + eapply map.sub_domain_disjoint.
                * destruct H13. eapply map.disjoint_comm. eapply d.
                * destruct H15. rewrite H15. eapply map.sub_domain_putmany_r.
                  eapply map.sub_domain_refl.
              + eapply map.sub_domain_disjoint.
                * destruct H13. erewrite map.disjoint_comm. eapply d.
                * destruct H15, H17. eapply map.sub_domain_trans.
                  2: {
                    rewrite H15. erewrite map.putmany_comm; auto. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
                  }
                  rewrite H17. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
            - erewrite map.disjoint_comm. eapply map.disjoint_putmany_l. split.
              + eapply map.sub_domain_disjoint.
                * destruct H13. eapply map.disjoint_comm. eapply d.
                * destruct H15. rewrite H15. eapply map.sub_domain_putmany_r.
                  eapply map.sub_domain_refl.
              + eapply map.sub_domain_disjoint.
                * destruct H13. erewrite map.disjoint_comm. eapply d.
                * destruct H15, H17. eapply map.sub_domain_trans.
                  2: {
                    rewrite H15. erewrite map.putmany_comm; auto. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
                  }
                  rewrite H17. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
          }
          eexists x12. eexists x10. split; eauto.
          1: {
            erewrite map.putmany_comm; eauto.
            1: eapply map.split_disjoint_putmany; eapply map.disjoint_comm.
            - destruct H15. destruct H17. eapply map.disjoint_comm. eapply map.sub_domain_disjoint.
              + eapply map.disjoint_comm. eauto.
              + rewrite H17. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
            - destruct H15. destruct H17. eapply map.disjoint_comm. eapply map.sub_domain_disjoint.
              + eapply map.disjoint_comm. eauto.
              + rewrite H17. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
          }
          split.
          - cbv [FElem]. eexists. sepsimpl.
            3: ecancel_assumption.
            2: eauto.
            eauto.
          - cbv [FElem]. eexists. sepsimpl.
            3: ecancel_assumption.
            2: eauto.
            eauto.
        }
        ecancel_assumption.
    }
    {
      clear Hxout Hx1 Hx2 H2 H8 H7 H9 H11 Hxoutsplit Hx1split Hx2split mx2 mx2' mxout mxout' mx1 mx1'. rename H5 into Hfeval. rename H10 into Hx0. rename H6 into Hypx1'. rename H12 into Hypx1''.
      (*preparing context for second function call*)
      eassert (Hx1: ((FElem (Some tight_bounds) pY1 Y1) * _)%sep a0) by ecancel_assumption.
      eassert (Hx2: ((FElem (Some tight_bounds) pY2 Y2) * _)%sep a0) by ecancel_assumption.
      eassert (Hxout: ((FElem (Some tight_bounds) pYout Youtold) * _)%sep a0) by ecancel_assumption.
      clear H14.
      destruct Hxout as [mxout Hxout]. destruct Hxout as [mxout' Hxout]. destruct Hxout as [Hxoutsplit Hxout]. destruct Hxout as [Hxout' Hxout].
      destruct Hx1 as [mx1 Hx1]. destruct Hx1 as [mx1' Hx1]. destruct Hx1 as [Hx1split Hx1]. destruct Hx1 as [Hx1' Hx1].
      destruct Hx2 as [mx2 Hx2]. destruct Hx2 as [mx2' Hx2]. destruct Hx2 as [Hx2split Hx2]. destruct Hx2 as [Hx2' Hx2].
      cbv [FElem] in Hxout', Hx1', Hx2'. sepsimpl_hyps.

      straightline_call.
      1: {
        split; [| split; [| split]].
        1: {
          eexists. eexists.
          split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hxout.
        }
        1: {
          eexists. eexists.
          split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hx1.
        }
        1: {
          eexists. eexists.
          split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hx2.
        }
        auto.
      }
      repeat straightline.
      eexists; split.
      1: {
        repeat straightline. eexists. split; [solve_locals l| ].
        repeat straightline. eexists. split; [solve_locals l| ].
        repeat straightline. eexists. split.
        {
          destruct (word.unsigned c =? 1).
          - eapply load_word_of_sep.
            rewrite <- bignum_1_scalar.
            ecancel_assumption.
          - eapply load_word_of_sep.
            rewrite <- bignum_1_scalar.
            ecancel_assumption.
        }
        repeat straightline. eexists. split; [solve_locals l| ].
        repeat straightline. eexists. split; [solve_locals l| ].
        repeat straightline.
      }

      rewrite eq in H14.
      clear Hxout Hx1 Hx2 H2 H8 H7 H9 H11 Hxoutsplit Hx1split Hx2split mx2 mx2' mxout mxout' mx1 mx1'. rename H10 into Hx01. rename H5 into Hfeval1.
      rename H6 into Hypy. rename H12 into Hypy'.

      eassert (Hx1: ((FElem (Some tight_bounds) pZ1 Z1) * _)%sep a2) by ecancel_assumption.
      eassert (Hx2: ((FElem (Some tight_bounds) pZ2 Z2) * _)%sep a2) by ecancel_assumption.
      eassert (Hxout: ((FElem (Some tight_bounds) pZout Zoutold) * _)%sep a2) by ecancel_assumption.
      clear H14.
      destruct Hxout as [mxout Hxout]. destruct Hxout as [mxout' Hxout]. destruct Hxout as [Hxoutsplit Hxout]. destruct Hxout as [Hxout' Hxout].
      destruct Hx1 as [mx1 Hx1]. destruct Hx1 as [mx1' Hx1]. destruct Hx1 as [Hx1split Hx1]. destruct Hx1 as [Hx1' Hx1].
      destruct Hx2 as [mx2 Hx2]. destruct Hx2 as [mx2' Hx2]. destruct Hx2 as [Hx2split Hx2]. destruct Hx2 as [Hx2' Hx2].
      cbv [FElem] in Hxout', Hx1', Hx2'. sepsimpl_hyps.

      straightline_call.
      1: {
        split; [| split; [| split]].
        1: {
          eexists. eexists.
          split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hxout.
        }
        1: {
          eexists. eexists.
          split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hx1.
        }
        1: {
          eexists. eexists.
          split; [| split; [ecancel_assumption |]]; [eauto| ]. eapply Hx2.
        }
        auto.
      }

      repeat straightline. split; auto. eexists. eexists. eexists; eexists.
      split.
      - split; try reflexivity. split; reflexivity.
      - rewrite eq in H14.
        destruct H14, H13, H13, H14.
        eassert ((Field.FElem pYout _ * _)%sep x9) by ecancel_assumption. clear H15.
        destruct H16, H15, H15, H16.
        eassert ((Field.FElem pXout _ * _)%sep x11) by ecancel_assumption. clear H17.
        destruct H18, H17, H17, H18.
        eassert (((FElem (Some tight_bounds) pXout _ * FElem (Some tight_bounds) pYout _ * FElem (Some tight_bounds) pZout _ * _)%sep) a3).
        { (*should be automated!!*)
          eexists (map.putmany (map.putmany x8 x10) x12). eexists x13. split.
          {
            destruct H17. split. destruct H13.
            - rewrite H13. destruct H15. rewrite H15. rewrite H17.
              rewrite map.putmany_assoc.
              rewrite map.putmany_assoc. auto.
            - eapply map.disjoint_putmany_l; split; auto.
              eapply map.disjoint_putmany_l; split; auto.
              destruct H13, H15.
              + eapply map.disjoint_comm. eapply map.sub_domain_disjoint.
                * eapply map.disjoint_comm. eauto.
                * eapply map.sub_domain_trans.
                  2: {
                    rewrite H15. rewrite map.putmany_comm; eauto. eapply map.sub_domain_putmany_r.
                    eapply map.sub_domain_trans.
                    2: {
                      rewrite H17. erewrite map.putmany_comm; auto. eapply map.sub_domain_putmany_r.
                      eapply map.sub_domain_refl.
                    }
                    eapply map.sub_domain_refl.
                  }
                  eapply map.sub_domain_refl.
              + eapply map.disjoint_comm. destruct H15. eapply map.sub_domain_disjoint.
                * eapply map.disjoint_comm. eauto.
                * rewrite H17. erewrite map.putmany_comm; auto. eapply map.sub_domain_putmany_r.
                  eapply map.sub_domain_refl.
          }
          split; [| eapply H19].
          eexists. eexists. split; [| split].
          3: {
            cbv [FElem]. cbv [Lift1Prop.ex1]. eexists. sepsimpl.
            3: eapply H14.
            2: eauto.
            eauto.
          }
          1: {
            erewrite <- map.putmany_assoc.
            erewrite map.putmany_comm; auto.
            - eapply map.split_disjoint_putmany. eapply map.disjoint_putmany_l. split.
              + eapply map.sub_domain_disjoint.
                * destruct H13. eapply map.disjoint_comm. eapply d.
                * destruct H15. rewrite H15. eapply map.sub_domain_putmany_r.
                  eapply map.sub_domain_refl.
              + eapply map.sub_domain_disjoint.
                * destruct H13. erewrite map.disjoint_comm. eapply d.
                * destruct H15, H17. eapply map.sub_domain_trans.
                  2: {
                    rewrite H15. erewrite map.putmany_comm; auto. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
                  }
                  rewrite H17. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
            - erewrite map.disjoint_comm. eapply map.disjoint_putmany_l. split.
              + eapply map.sub_domain_disjoint.
                * destruct H13. eapply map.disjoint_comm. eapply d.
                * destruct H15. rewrite H15. eapply map.sub_domain_putmany_r.
                  eapply map.sub_domain_refl.
              + eapply map.sub_domain_disjoint.
                * destruct H13. erewrite map.disjoint_comm. eapply d.
                * destruct H15, H17. eapply map.sub_domain_trans.
                  2: {
                    rewrite H15. erewrite map.putmany_comm; auto. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
                  }
                  rewrite H17. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
          }
          eexists x12. eexists x10. split; eauto.
          1: {
            erewrite map.putmany_comm; eauto.
            1: eapply map.split_disjoint_putmany; eapply map.disjoint_comm.
            - destruct H15. destruct H17. eapply map.disjoint_comm. eapply map.sub_domain_disjoint.
              + eapply map.disjoint_comm. eauto.
              + rewrite H17. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
            - destruct H15. destruct H17. eapply map.disjoint_comm. eapply map.sub_domain_disjoint.
              + eapply map.disjoint_comm. eauto.
              + rewrite H17. eapply map.sub_domain_putmany_r. eapply map.sub_domain_refl.
          }
          split.
          - cbv [FElem]. eexists. sepsimpl.
            3: ecancel_assumption.
            2: eauto.
            eauto.
          - cbv [FElem]. eexists. sepsimpl.
            3: ecancel_assumption.
            2: eauto.
            eauto.
        }
        ecancel_assumption.
    }
  Qed.

End __.

Existing Instance spec_of_group_cmov.
