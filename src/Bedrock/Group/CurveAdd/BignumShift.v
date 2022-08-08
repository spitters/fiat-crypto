Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.ArrayUtil.
(* Require Import Crypto.Bedrock.Specs.PrimeField. *)
Local Open Scope Z_scope.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  (* Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}. *)
  Check Bignum. Check Positional.eval.
  Check uweight 64.

  Local Notation eval n := (Positional.eval (uweight 64) n).

  Instance spec_of_shift_scalar : spec_of "shift_scalar" :=
    fnspec! "shift_scalar"
          (pout pin : word)
          / (xinold xoutold: list word) R,
    { requires tr mem :=
        (Bignum 6 pin xinold * Bignum 1 pout xoutold * R)%sep mem;
      ensures tr' mem' :=
             exists xin xout (* output values *)
                  : list word ,
              eval 6 (rev (List.map word.unsigned xinold)) / 2 = eval 6 ( rev (List.map word.unsigned xin))
              /\ eval 6 (rev (List.map word.unsigned xinold)) mod 2 = eval 1 (List.map word.unsigned xout)
          /\ ((Bignum 6 pin xin * Bignum 1 pout xout * R)%sep mem')}.
    
          Require Import bedrock2.NotationsCustomEntry.
          Require Import bedrock2.WeakestPrecondition.
          Import Syntax BinInt String List.ListNotations.
          Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

          Local Infix "x & y" := (expr.op bopname.and (expr.load access_size.word x) (expr.literal y)) (at level 90).
          Local Infix "x ++ y" := (expr.op bopname.add x (expr.literal y)) (at level 90).

          Local Notation get := (expr.load access_size.word).
          Local Notation and := (expr.op bopname.and).
          Local Notation store := (cmd.store access_size.word).
          Local Notation lit := (expr.literal).
          Local Notation sr1 x := (expr.op bopname.sru x (expr.literal 1)).
          Local Notation sl7 x := (expr.op bopname.slu x (expr.literal 63)).
          Local Notation add_words x y := (expr.op bopname.add x y).
          Local Notation add8 x := (expr.op bopname.add (expr.var x) (expr.literal 8)).
          Local Notation addany n x := (expr.op bopname.add (expr.var x) (expr.literal n)).
          Local Notation op1 carry scalar n := (store (expr.var carry) (and (get ( addany n scalar)) (lit 1))).
          Local Notation op2 carry := ( store (expr.var carry) (sl7 (get (expr.var carry)))).
          Local Notation op3 carry scalar n := ( store (addany n scalar) (add_words ((sr1 (get (addany n scalar)))) (get (expr.var carry)))).
          Local Notation op4 carry n := (store (addany n carry) (expr.literal 0)).

    Definition shift_scalar : bedrock2.Syntax.func :=
        ("shift_scalar", (["c2"; "scalar"], []:list String.string, bedrock_func_body:(
            stackalloc (Memory.bytes_per_word 64) as carry;
            coq:( store (expr.var "c2") (expr.literal 0));
            coq:( store (expr.var "carry") (and (get (expr.var "scalar")) (lit 1)));
            coq:( store (expr.var "scalar") (sr1 (get (expr.var "scalar"))));

            coq:( store (expr.var "c2") (and (get ( add8 "scalar")) (lit 1)));
            coq:( store (expr.var "carry") (sl7 (get (expr.var "carry"))));
            coq:( store (add8 "scalar") (add_words ((sr1 (get (add8 "scalar")))) (get (expr.var "carry"))));

            coq:( op1 "carry" "scalar" 16 );
            coq:( op2 "c2");
            coq:( op3 "c2" "scalar" 16);

            coq:( op1 "c2" "scalar" 24 );
            coq:( op2 "carry");
            coq:( op3 "carry" "scalar" 24);

            coq:( op1 "carry" "scalar" 32 );
            coq:( op2 "c2");
            coq:( op3 "c2" "scalar" 32);

            coq:( op1 "c2" "scalar" 40 );
            coq:( op2 "carry");
            coq:( op3 "carry" "scalar" 40)
        ))).

        From bedrock2 Require Import ToCString Bytedump.
        Definition c_mod := (c_module (shift_scalar :: nil)).
    
        Eval native_compute in c_mod.

    Ltac solve_locals l :=
        subst l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

    Ltac solve_locals2 l0 l :=
        subst l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.
        
    Ltac solve_locals3 l1 l0 l :=
        subst l1 l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

    Ltac solve_locals4 l2 l1 l0 l :=
        subst l2 l1 l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

    Ltac solve_locals5 l3 l2 l1 l0 l :=
        subst l3 l2 l1 l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

                
        (* Lemma alloc_to_FElem : forall a m, Memory.anybytes a felem_size_in_bytes m -> exists f, AbstractField.FElem a f m.
        Proof.
          intros. eapply anybytes_to_array_1 in H. destruct H, H. cbv [felem_size_in_bytes] in *.
          eapply (Bignum.Bignum_of_bytes felem_size_in_words) in H; try lia.
          eexists. cbv [AbstractField.FElem]. eauto.
        Qed. *)


    Lemma cmov_ok : program_logic_goal_for_function! shift_scalar.
    Proof.
        repeat straightline.
        cbv [Bignum] in H. sepsimpl_hyps.
        eapply sep_assoc in H1. eapply sep_comm in H1.
        do 7 (destruct xinold; try discriminate). clear H.
        do 2 (destruct xoutold; try discriminate); clear H0.

        assert (Htriv : forall {A : Type} (x : A), Datatypes.length [x] = 1%nat) by auto.
        assert (Hlist : forall {A: Type} (x : A) (l : list A), x :: l = [x] ++ l) by auto.
        rewrite Hlist in H1.
        eapply array_append_R' in H1; rewrite Htriv in H1.
        remember (word.of_Z (Memory.bytes_per_word width)) as w1.
        remember (word.mul w1 (word.of_Z (Z.of_nat 1))) as w2.

        rewrite Hlist in H1.
        eapply array_append_R' in H1; rewrite Htriv in H1. rewrite <- Heqw2 in H1.

        rewrite Hlist in H1.
        eapply array_append_R' in H1; rewrite Htriv in H1. rewrite <- Heqw2 in H1.

        rewrite Hlist in H1.
        eapply array_append_R' in H1; rewrite Htriv in H1. rewrite <- Heqw2 in H1.
        
        rewrite Hlist in H1.
        eapply array_append_R' in H1; rewrite Htriv in H1. rewrite <- Heqw2 in H1.

        cbv [array] in H1. sepsimpl_hyps.

        Lemma bw_eq : width = 64.
        Proof. Admitted.

        eexists.
        1: {
            cbv [Memory.bytes_per_word].
            destruct word_ok.
            destruct BW. destruct width_cases; subst width; simpl; cbv; auto.
        }
        repeat straightline.

        eexists. repeat straightline. split.
        {
            repeat straightline. eexists; split; [ solve_locals2 l0 l| repeat straightline].
        }
        
        repeat straightline. eexists; split.
        {
            repeat straightline. eexists; split; [solve_locals2 l0 l| repeat straightline].
        }


        
        eexists. repeat straightline. split.
        { repeat straightline. eexists; split; [solve_locals2 l0 l| repeat straightline]. }

        clear H1. rename H4 into H1.


        eassert ((array ptsto (word.of_Z 1) a stack * _)%sep m) by ecancel_assumption.
        clear H1.
        destruct H4, H1, H1, H4.


        eapply store_word_of_sep.
        { eexists. eexists; split; [eauto | split; [| eapply H5]].
          eapply scalar_of_bytes in H4; try rewrite bw_eq; try lia. eauto. }
        
        repeat straightline. eexists; split; repeat straightline.
        {eexists; split; [solve_locals2 l0 l| eauto]. }

        repeat straightline. eexists; split; repeat straightline.
        {eexists; split; [solve_locals2 l0 l| eauto]. repeat straightline. }

        repeat straightline. eexists; split; repeat straightline.
        {eexists; split; [solve_locals2 l0 l| repeat straightline]. }
        
        repeat straightline. eexists; split; repeat straightline.
        {eexists; split; [solve_locals2 l0 l| repeat straightline].
            eexists. split; repeat straightline.
            eapply load_word_of_sep. subst v.
            assert (Hw1: w1 = word.of_Z 8).
            {
                subst w1. pose proof (bw_eq). eapply f_equal.
                simpl. rewrite H10. simpl. cbv. auto.
            }

            eassert ( Hw2: w2 = w1).
            {
                subst w2. simpl.
                destruct word.ring_theory.
                rewrite Rmul_comm. rewrite Rmul_1_l. eauto.
            }
            rewrite Hw2.
            rewrite Hw2 in H9. rewrite Hw1 in H9.
            pose proof H9.
            ecancel_assumption.
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        assert (Hw1: w1 = word.of_Z 8).
        {
            subst w1. pose proof (bw_eq). eapply f_equal.
            simpl. rewrite H11. simpl. cbv. auto.
        }

        eassert ( Hw2: w2 = w1).
        {
            subst w2. simpl.
            destruct word.ring_theory.
            rewrite Rmul_comm. rewrite Rmul_1_l. eauto.
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
            eexists; split; repeat straightline.
                - eapply load_word_of_sep. subst v.
                rewrite Hw2.
                rewrite Hw2 in H11. rewrite Hw1 in H11.
                ecancel_assumption.
                - eexists; split; repeat straightline. solve_locals2 l0 l.
        }

        rewrite Hw2 in H11. rewrite Hw1 in H11.

        eapply store_word_of_sep.
        {
            ecancel_assumption.
        }

        repeat straightline.

        assert (Hpin : forall w1 w2, (word.add (word.add pin w2) w1 = word.add pin (word.add w1 w2))).
        {
            destruct word.ring_theory. intros. rewrite <- Radd_assoc.
            rewrite (Radd_comm w3 w0). eauto.
        }

        repeat rewrite Hpin in H12.
        assert ( Hw16 : @word.add width word (word.of_Z 8) (word.of_Z 8) = word.of_Z 16).
        { rewrite <- word.ring_morph_add. simpl. auto. }



        eexists; split; repeat straightline. eexists; split; [solve_locals2 l0 l| repeat straightline]. repeat straightline.
         repeat rewrite Hw16 in H12.

         assert ( Hw24 : @word.add width word (word.of_Z 8) (word.of_Z 16) = word.of_Z 24).
         { rewrite <- word.ring_morph_add. simpl. auto. }
         repeat rewrite Hw24 in H12.

         assert ( Hw32 : @word.add width word (word.of_Z 8) (word.of_Z 24) = word.of_Z 32).
         { rewrite <- word.ring_morph_add. simpl. auto. }
         repeat rewrite Hw32 in H12.

         assert ( Hw40 : @word.add width word (word.of_Z 8) (word.of_Z 32) = word.of_Z 40).
         { rewrite <- word.ring_morph_add. simpl. auto. }
         repeat rewrite Hw40 in H12.

        eexists; split; repeat straightline. eexists; split; [solve_locals2 l0 l| repeat straightline]. repeat straightline.
        eexists; split; repeat straightline. eexists; split; [solve_locals2 l0 l| repeat straightline]. repeat straightline.
        eexists; split; repeat straightline. eexists; split; [solve_locals2 l0 l| repeat straightline]. repeat straightline.
        eexists; split; repeat straightline. eexists; split; [solve_locals2 l0 l| repeat straightline]. repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
            eexists. split; [solve_locals2 l0 l |]. repeat straightline.
        }
        repeat straightline.
        
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }
        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        repeat straightline.
        eexists; split; repeat straightline.
        {
            eexists; split; [solve_locals2 l0 l| repeat straightline].
            eexists; split; [solve_locals2 l0 l| repeat straightline].
        }

        eassert ((scalar a _ * _)%sep m16) by ecancel_assumption. clear H24.
        destruct H25, H24, H24, H25.

        eexists. eexists. split.
        {
            assert (Memory.bytes_per_word width = 8).
            {
                rewrite bw_eq. simpl. cbv. auto.
            }
            rewrite <- H27.
            eapply scalar_to_anybytes. eapply H25.
        }
        split.
        1: eapply map.split_comm; eauto.
        repeat straightline. split; auto.

        eexists. eexists [word.and r4 (word.of_Z 1)]. split; [| split].

        3: {
            cbv [Bignum]. sepsimpl.
            2: auto.

            2: {
                eassert ((scalar pout _ * _)%sep x2) by ecancel_assumption. clear H26.
                destruct H27, H26, H26, H27.
                eassert ((_ * R)%sep x4) by ecancel_assumption. clear H28.
                destruct H29, H28, H28, H29.
                eexists. eexists. split; [eapply H26| ]. split.
                {
                    simpl. sepsimpl; auto.
                }
                eexists; eexists; split.
                1: eapply map.split_comm; eapply H28. split; eauto.
                eapply array_cons.
                Lemma array_cons' : forall R a x xs (mem : mem), (array scalar (word.of_Z 8) (word.add a (word.of_Z 8)) xs * (scalar a x * R))%sep mem -> (array scalar (word.of_Z 8) a (x :: xs) * R)%sep mem.
                Proof.
                    intros.
                    assert ((@word.of_Z width word 8) = word.of_Z (Memory.bytes_per_word width)).
                    {
                        simpl. pose proof (bw_eq).
                        eapply (f_equal (fun y => Memory.bytes_per_word y)) in H0.
                        rewrite H0. simpl. cbv [Memory.bytes_per_word]. eapply f_equal. lia.
                    } 
                    rewrite H0.
                    eassert ((_ * R)%sep mem0) by ecancel_assumption. clear H.
                    destruct H1, H, H, H1.
                    eexists; eexists; split.
                    1: eapply H. split; auto.
                    eapply array_cons. rewrite <- H0. eapply sep_comm. auto.
                Qed.

                eapply sep_comm.
                assert ((@word.of_Z width word 8) = word.of_Z (Memory.bytes_per_word width)).
                    {
                        simpl. pose proof (bw_eq).
                        eapply (f_equal (fun y => Memory.bytes_per_word y)) in H31.
                        rewrite H31. simpl. cbv [Memory.bytes_per_word]. eapply f_equal. lia.
                    }
                    rewrite <- H31.
                
                eapply array_cons'. eapply array_cons'. eapply array_cons'.
                eapply array_cons'. repeat rewrite Hpin. rewrite Hw16. rewrite Hw24. rewrite Hw32.
                rewrite Hw40.

                Lemma array_simpl : forall a (mem : mem) R x, (scalar a x * R)%sep mem -> (array scalar (word.of_Z 8) a [x] * R)%sep mem.
                Proof.
                    intros. cbv [array]. sepsimpl. eapply sep_assoc. eapply sep_comm. sepsimpl; auto. eapply sep_comm; auto.
                Qed.

                eapply array_simpl. ecancel_assumption.
            }
            auto.
        }
        {
        simpl. subst. clear H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 x1 x2 m16.
        clear  Hpin Hw16 Hw24 Hw32 Hw40 H12 m3 H11 m2 H10 Hw1 Hw2 m1 H9 m4 .
        destruct word_ok.
        repeat rewrite unsigned_sru.
        repeat rewrite unsigned_add.
        repeat rewrite unsigned_sru.
        repeat rewrite unsigned_add.
        repeat rewrite unsigned_slu.
        repeat rewrite unsigned_and.
        repeat rewrite unsigned_of_Z.
        assert (wrap 1 = 1).
        {
            cbv [wrap]. rewrite bw_eq. lia.
        }
        rewrite H9.

        assert (wrap 63 = 63).
        {
            cbv [wrap]. rewrite bw_eq. lia.
        }
        rewrite H10. 
        cbv [wrap]. remember (2 ^ width) as emod.
        repeat rewrite <- Z.add_mod.
        assert (forall x, (Z.land (word.unsigned x) 1 mod emod = Z.land (@word.unsigned width word x) 1)).
        {
            intros.
            erewrite Zmod_small; try lia. split; try lia.
                - eapply Z.land_nonneg. right. lia.
                - erewrite Z.land_comm.
                  epose proof (LandLorShiftBounds.Z.land_le').
                  eassert (Z.land 1 (word.unsigned x1) <= 1).
                  {
                      apply H11; try lia.
                  }
                  assert (1 < emod).
                  {
                      subst emod. rewrite bw_eq. lia.
                  }
                  lia.
        }
        repeat rewrite H11. Search (Z.shiftl). pose proof (OrdersEx.Z_as_DT.shiftl_mul_pow2).
        repeat rewrite Z.shiftl_mul_pow2. repeat rewrite Z.shiftr_div_pow2.
        assert (2 ^ 1 = 2) by lia.
        rewrite H13.

        remember (word.unsigned r) as q.
        remember (word.unsigned r0) as q0.
        remember (word.unsigned r1) as q1.
        remember (word.unsigned r2) as q2.
        remember (word.unsigned r3) as q3.
        remember (word.unsigned r4) as q4.

        Lemma Zand_1_r : forall q, Z.land q 1 = q mod 2.
        Proof.
            intros. Search Z.land. pose proof (Z.land_ones q 1). simpl in H. cbv [Z.ones] in H. simpl in H.
            rewrite H; lia.
        Qed.

        repeat rewrite Zand_1_r.


        cbv [eval Associational.eval]. simpl. cbv [uweight ModOps.weight]. simpl. repeat rewrite Z.add_0_r.
        assert (forall r, word.unsigned r = @word.unsigned width word r mod emod).
        {
            intros. rewrite <- word.wrap_unsigned. subst emod. rewrite Z.mod_mod; auto.
            lia.
        }
        simpl. repeat rewrite Z.mul_assoc. simpl. repeat rewrite Z.mul_1_l.
        subst emod.
        assert (forall q, 0 <= q ->  Z.land q 1 = 1 \/ Z.land q 1 = 0).
        {
            intros.
             epose proof (LandLorShiftBounds.Z.land_upper_bound_r q5 1 H15).
             assert ( 0 <= 1) by lia.
             specialize (H16 H17).
             erewrite Z.land_comm in H16.
             erewrite Z.land_comm.
             epose proof (Z.land_nonneg 1 q5). lia.
        }
        assert (q / 2 mod 2 ^ width = q / 2).
        {
            rewrite Zmod_small; auto.
            split.
                - eapply Div.Z.div_nonneg; try lia. subst q. rewrite H14. lia.
                - assert (forall x, 0 <= x -> x / 2 <= x) by lia.
                  pose proof (H16 q).
                  assert (0 <= q).
                  {
                      subst q. rewrite H14. lia.
                  }
                  specialize (H17 H18).
                  assert (q <= 2 ^ width) by (subst q; rewrite H14; lia).
                  lia.
        }
        rewrite H16.
        assert (forall r, 0 <= (@word.unsigned width word r)).
        {
            intros. rewrite H14. lia.
        }
        (*test*) (*Make general assertion to use Zmod_small*)
        repeat rewrite (Zmod_small _ (2 ^ width)).
        {
            (*rewriting left-hand side to normal form (Perhaps Ring tactic for Z will make this more stramlined? Does it work with Z.div? How about mod for right-hand side?)*)
            lazymatch goal with
            | |- ?LHS = _ => eassert (LHS = _)
            | _ => idtac
            end.
            {
                assert (H2pow : Z.pow_pos 2 1 = 2) by lia.
                assert (Htemp : (320 = 1 + 319)%positive) by lia. rewrite Htemp.
                rewrite Zpower_pos_is_exp. rewrite H2pow; clear Htemp.

                assert (Htemp : (256 = 1 + 255)%positive) by lia. rewrite Htemp.
                rewrite Zpower_pos_is_exp. rewrite H2pow; clear Htemp.

                assert (Htemp : (192 = 1 + 191)%positive) by lia. rewrite Htemp.
                rewrite Zpower_pos_is_exp. rewrite H2pow; clear Htemp.

                assert (Htemp : (128 = 1 + 127)%positive) by lia. rewrite Htemp.
                rewrite Zpower_pos_is_exp. rewrite H2pow; clear Htemp.

                assert (Htemp : (64 = 1 + 63)%positive) by lia. rewrite Htemp.
                rewrite Zpower_pos_is_exp. rewrite H2pow; clear Htemp.

                repeat rewrite <- Z.mul_assoc.

                repeat rewrite <- Z.mul_add_distr_l. rewrite (Z.mul_comm 2). rewrite Z_div_plus; [| lia].



                eauto.
            }
            lazymatch goal with | |- _ = ?RHS => remember RHS as rhs | _ => idtac end.
            rewrite H18.
            rewrite (Z_div_mod_eq_full q3 2).
            rewrite (Z_div_mod_eq_full q2 2).
            rewrite (Z_div_mod_eq_full q1 2).
            rewrite (Z_div_mod_eq_full q0 2).
            rewrite (Z_div_mod_eq_full q 2).
            subst rhs.
             ring_simplify.
            repeat rewrite <- Z.add_assoc. eapply (f_equal ).

            assert (H2pow : forall n, 2 * Z.pow_pos 2 n = Z.pow_pos 2 (n + 1)).
            {
                intros. rewrite Zpower_pos_is_exp. simpl. lia.
            }

            repeat rewrite H2pow.
            simpl.
            ring_simplify.
            repeat rewrite <- Z.add_assoc.
            eapply f_equal.

            repeat rewrite <- Zpower_pos_is_exp. simpl. ring_simplify. auto.
        }
        Lemma divmod_bounds : forall x1 x2, 0 <= (@word.unsigned width word x1) / 2 + (@word.unsigned width word x2 mod 2) * (Z.pow_pos 2 63) < 2 ^ width.
        Proof.
            intros. pose proof (bw_eq) as Hbw.
            assert (forall x, 0 <= @word.unsigned width word x < 2 ^ width).
            {
                destruct word_ok. intros. rewrite <- word.wrap_unsigned. lia.
            }
            pose proof (H x1). pose proof (H x2).
            assert (H' : 2 ^width = Z.pow_pos 2 64).
            {
                cbv. rewrite Hbw. auto.
            }
            lia.
        Qed.

        1: subst q0 q; eapply divmod_bounds.
        1: subst q1 q0; eapply divmod_bounds.
        1: subst q2 q1; eapply divmod_bounds.
        1: subst q3 q2; eapply divmod_bounds.
        1: subst q4 q3; eapply divmod_bounds.
        all: try lia.
        all: rewrite bw_eq; rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite bw_eq; lia.
        }

        simpl. cbv [eval Associational.eval]. simpl. cbv [uweight ModOps.weight]. simpl.
        do 2 rewrite Z.mul_1_l.
        do 2 rewrite Z.add_0_r.
        
        assert (r4 = word.of_Z (word.unsigned r4)).
        {
            rewrite word.of_Z_unsigned. auto.
        }
        rewrite H27.
        rewrite <- word.morph_and.
        rewrite <- H27.
        rewrite word.unsigned_of_Z. rewrite Zand_1_r.
        assert (word.wrap (word.unsigned r4 mod 2) = word.unsigned r4 mod 2).
        {
            cbv [word.wrap].
            erewrite Zmod_small; eauto.
            split; try lia. destruct BW; destruct width_cases; subst width; try lia.
        }
        rewrite H28. auto.
        (* subst r4. *)

        assert (H2pow : Z.pow_pos 2 1 = 2) by lia.
        assert (Htemp : (320 = 1 + 319)%positive) by lia. rewrite Htemp.
        rewrite Zpower_pos_is_exp. rewrite H2pow; clear Htemp.

        assert (Htemp : (256 = 1 + 255)%positive) by lia. rewrite Htemp.
        rewrite Zpower_pos_is_exp. rewrite H2pow; clear Htemp.

        assert (Htemp : (192 = 1 + 191)%positive) by lia. rewrite Htemp.
        rewrite Zpower_pos_is_exp. rewrite H2pow; clear Htemp.

        assert (Htemp : (128 = 1 + 127)%positive) by lia. rewrite Htemp.
        rewrite Zpower_pos_is_exp. rewrite H2pow; clear Htemp.

        assert (Htemp : (64 = 1 + 63)%positive) by lia. rewrite Htemp.
        rewrite Zpower_pos_is_exp. rewrite H2pow; clear Htemp.

        repeat rewrite <- Z.mul_assoc.

        repeat rewrite <- Z.mul_add_distr_l.
        
        rewrite Modulo.Z.mod_add'_full. auto.
    Qed.





        


End __.
