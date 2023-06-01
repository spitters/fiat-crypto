Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZeroGSpec.
Require Import Crypto.Bedrock.Group.CurveAdd.LoopBody.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAdd.
Require Import Crypto.Bedrock.Group.CurveAdd.BignumShift.
Require Import Crypto.Bedrock.Group.CurveAdd.CondMoveGroup.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Local Open Scope Z_scope.


Section __.
  Definition width := 64%Z.
  Context {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type} {field_parameters : FieldParameters F}
          {field_parameters_ok : FieldParameters_ok F}.
  
  Context {field_representation : FieldRepresentation F}
          {field_representation_ok : FieldRepresentation_ok F}
          {group_cmov : string}
          {store_zero : string}.

  Context {curve_add : (F * F * F) -> (F * F * F) -> (F * F * F)}.
  Context {group_prop1 : forall x y z, curve_add (x, y, z) (Fzero, Fone, Fzero) = (x, y, z)}.

    Instance spec_of_loop_body : spec_of "loop_body" := spec_of_loop_body (curve_add:=curve_add).

    Instance spec_of_store_zero : spec_of "store_zero_G" := spec_of_store_zero.

    Instance spec_of_scalar_mult : spec_of "scalar_mult" :=
    fnspec! "scalar_mult"
          (pPx pPy pPz pOutx pOuty pOutz pn : word)
          / (Px Py Pz Outx Outy Outz : F) (n : list word) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pPx Px
         * FElem (Some tight_bounds) pPy Py
         * FElem (Some tight_bounds) pPz Pz
         * FElem (Some tight_bounds) pOutx Outx
         * FElem (Some tight_bounds) pOuty Outy
         * FElem (Some tight_bounds) pOutz Outz
         * Bignum.Bignum 6 pn n
         * R)%sep mem
         ;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Pxnew Pynew Pznew Outxnew Outynew Outznew (* output values *)
                  : F,
           exists nnew : list word,
               (Outxnew, Outynew, Outznew) = (@scmul _ field_parameters curve_add) (Z.to_nat (Positional.eval (uweight 64) 6 (List.map word.unsigned n))) (Px, Py, Pz)
              /\ (FElem (Some tight_bounds) pPx Pxnew
                * FElem (Some tight_bounds) pPy Pynew
                * FElem (Some tight_bounds) pPz Pznew
                * FElem (Some tight_bounds) pOutx Outxnew
                * FElem (Some tight_bounds) pOuty Outynew
                * FElem (Some tight_bounds) pOutz Outznew
                * Bignum.Bignum 6 pn nnew
                * R)%sep mem'}.

    Require Import bedrock2.NotationsCustomEntry.
    Require Import bedrock2.WeakestPrecondition.
    Import Syntax BinInt String List.ListNotations.
    Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
    


    Ltac solve_locals5 l3 l2 l1 l0 l :=
      subst l3 l2 l1 l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

                
    
    Definition scalar_mult_func : bedrock2.Syntax.func :=
        ("scalar_mult", (["px"; "py"; "pz"; "outx"; "outy"; "outz"; "pn"], []:list String.string, bedrock_func_body:(
        stackalloc 48 as pauxx;
        stackalloc 48 as pauxy;
        stackalloc 48 as pauxz;
        stackalloc 8 as cond;
        stackalloc 8 as iter;
        coq:(cmd.call [] "store_zero_G" [expr.var "outx"; expr.var "outy"; expr.var "outz"]);
        coq:(cmd.store access_size.word (expr.var "iter") (expr.literal 0));
        while (coq:( expr.op bopname.ltu (expr.load access_size.word (expr.var "iter")) (expr.literal 384) )){
            coq:(cmd.store access_size.word (expr.var "iter") (expr.op bopname.add (expr.load access_size.word "iter") (expr.literal 1)));
            coq:(cmd.call [] "loop_body" [expr.var "px"; expr.var "py"; expr.var "pz"; expr.var "outx"; expr.var "outy"; expr.var "outz"; expr.var "pauxx"; expr.var "pauxy"; expr.var "pauxz"; expr.var "pn"; expr.var "cond" ])
        }
        ))).

        (* From bedrock2 Require Import ToCString Bytedump. *)
        (* Definition c_mod := (c_module (scalar_mult_func :: nil)). *)
        (* Eval native_compute in c_mod. *)

    Lemma scalar_mult_ok : program_logic_goal_for_function! scalar_mult_func.
    Proof.
      cbv [width] in *.
      cbv [program_logic_goal_for spec_of_scalar_mult]; repeat straightline.
      cbv [scalar_mult_func].
      repeat straightline.
      simpl.

      eexists; split; [ repeat straightline; cbv [map.of_list_zip]; simpl; eauto |].
      repeat straightline.

      eexists; split; [ repeat (repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| ]); repeat straightline| ].

      pose proof H as Hspec1.
      cbv [spec_of_store_zero LoopBody.spec_of_store_zero spec_of_store_zero] in Hspec1.


      eapply Proper_call; [| eapply Hspec1; ecancel_assumption].
      cbv [pointwise_relation Basics.impl]. repeat straightline.
      eexists. split; [subst a6; eauto |].

      repeat straightline.
      eexists; split; [repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| repeat straightline]| ].
      eexists; split; [repeat straightline| ].

      clear H1 H20 H18 H16 H14 H12.
      assert (Hwa3 : exists wa3, (scalar a3 wa3) = (array ptsto (word.of_Z 1) a3 stack3)) by admit.
      assert (Hwa2 : exists wa2, (scalar a2 wa2) = (array ptsto (word.of_Z 1) a2 stack2)) by admit.

      destruct Hwa3, Hwa2.
      rewrite <- H12 in H23.
      rewrite <- H1 in H23. 
      (* assert (exists wa3, (scalar a3 wa3) = (array ptsto (word.of_Z 1) a3 stack3)) by admit.
      assert (exists wa3, (scalar a3 wa3) = (array ptsto (word.of_Z 1) a3 stack3)) by admit.
      assert (exists wa3, (scalar a3 wa3) = (array ptsto (word.of_Z 1) a3 stack3)) by admit. *)

      eapply store_word_of_sep; [ecancel_assumption| repeat straightline].

      assert (Hc: exists wc, (scalar a2 x0) = Bignum.Bignum 1 a2 [wc]) by admit.
      destruct Hc. rewrite H16 in H14; clear H16.

      assert (Hf1 : exists f1, (FElem (Some tight_bounds) a1 f1) = (array ptsto (word.of_Z 1) a1 stack1)) by admit.
      destruct Hf1. rewrite <- H16 in H14.

      assert (Hf0 : exists f0, (FElem (Some tight_bounds) a0 f0) = (array ptsto (word.of_Z 1) a0 stack0)) by admit.
      destruct Hf0. rewrite <- H18 in H14.

      assert (Hf : exists f, (FElem (Some tight_bounds) a f) = (array ptsto (word.of_Z 1) a stack)) by admit.
      destruct Hf. rewrite <- H20 in H14.

      clear H16 H18 H20.

      rename a into pPauxx.
      rename a0 into pPauxy.
      rename a1 into pPauxz.
      rename a2 into pc.
      rename a3 into piter.


      remember ((Positional.eval (uweight 64) 6 (List.map word.unsigned n))) as n_init.
      remember (Px) as Px_init.
      remember (Py) as Py_init.
      remember (Pz) as Pz_init.


      eexists nat. eexists (fun s => (fun b => b < s < 400)%nat).


      (*Invariant*)
      
      exists ( fun (v : nat) (tr : Semantics.trace) (m' : mem) (l' : locals) =>
        l' = l3 /\
          exists Pauxx Pauxy Pauxz c viter Px Py Pz Outx Outy Outz n,

        ( scalar piter (word.of_Z viter)
        * FElem (Some tight_bounds) pPx Px
        * FElem (Some tight_bounds) pPy Py
        * FElem (Some tight_bounds) pPz Pz
        * FElem (Some tight_bounds) pOutx Outx
        * FElem (Some tight_bounds) pOuty Outy
        * FElem (Some tight_bounds) pOutz Outz
        * FElem (Some tight_bounds) pPauxx Pauxx
        * FElem (Some tight_bounds) pPauxy Pauxy
        * FElem (Some tight_bounds) pPauxz Pauxz
        * Bignum.Bignum 6 pn n
        * Bignum.Bignum 1 pc [c]
        * R)%sep m'
        /\ (*n*)
           (Positional.eval (uweight 64) 6 (List.map word.unsigned n)) = Z.shiftr n_init (Z.of_nat v)
        /\ (Outx, Outy, Outz) = @scmul _ field_parameters curve_add  (Z.to_nat (n_init mod (2 ^ (Z.of_nat v))))%Z (Px_init, Py_init, Pz_init)
        /\ (Px, Py, Pz) = @scmul _ field_parameters curve_add (2 ^ v) (Px_init, Py_init, Pz_init)
        /\ viter = Z.of_nat (v)
        /\ viter < 399
      ).


      split.
      {
        admit.
      }

      split.
      {
        exists 0%nat. split; [reflexivity |]. exists x4. exists x3. exists x2. exists x1. exists 0. exists Px_init, Py_init, Pz_init.
        exists Fzero, Fone, Fzero. exists n.
        
        split; [| split; [| split; [| split]]].
          - ecancel_assumption.
          - rewrite Z.shiftr_0_r. subst n_init. eauto.
          - assert (2 ^ Z.of_nat 0 = 1) by admit.
            assert (n_init mod 1 = 0) by admit.
            rewrite H16, H18. simpl. eauto.
          - simpl. rewrite group_prop1. eauto.
          - lia.
      }

      repeat straightline.
      eexists; split.
      {
        (repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| repeat straightline]).
        eexists. split.
          - repeat straightline.
            eapply load_word_of_sep. ecancel_assumption.
          - repeat straightline.
      }

      repeat straightline.
      split.
      {
        repeat straightline.
        eexists; split.
        {
          (repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| repeat straightline]).
        }

        repeat straightline.
        eexists; split.
        {
          (repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| repeat straightline]).
          eexists; split; repeat straightline.
          eapply load_word_of_sep. ecancel_assumption.
        }

        eapply store_word_of_sep; [ecancel_assumption| ].

        repeat straightline.
        eexists; split.
        {
          repeat (repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| repeat straightline]).
        }

        eapply Proper_call.

        2: {
          pose proof H0 as Hspec2. cbv [spec_of_loop_body LoopBody.spec_of_loop_body] in Hspec2.

          specialize (Hspec2  pPx pPy pPz pOutx pOuty pOutz pPauxx pPauxy pPauxz pn pc).

          eapply Hspec2; clear Hspec2.
          split; [| split; [| split]].

            - clear H18 H14 H23.  ecancel_assumption.
            - erewrite <- H20. eauto.
            - rewrite H22. eauto.
            - eassumption.
        }

        cbv [pointwise_relation Basics.impl].
        repeat straightline.
        eexists; split; [subst a1; eauto| ].

        eexists. split; [split; eauto | ].
        1: {
          do 12 eexists.
          split; [| split; [| split; [| split; [| split] ]]].
          1: {
            rewrite <- word.ring_morph_add in H32.
            ecancel_assumption.
          }
          5: {
            subst x9. destruct (word.ltu (word.of_Z (Z.of_nat v)) (word.of_Z 384)) eqn:eq.
              2: {
                rewrite word.unsigned_of_Z in H16. assert (@word.wrap width word word_ok Z0 = 0) by (cbv [word.wrap width]; lia).
                rewrite H27 in H16.
                exfalso. apply H16. auto.
              }
              pose proof eq. Search (word.ltu).
              erewrite <- word.morph_ltu in H27.
              3: cbv [width]; lia.
              2: split; cbv [width]; lia.
              lia.
              }
          4: {
            subst x9.
            assert (Z.of_nat ((v)) + 1 = Z.of_nat (v + 1)) by lia.
            eapply H27.
          }
          3: eauto.
          2: eauto.
          eauto.
        }
        split; try lia.
      }
      repeat straightline.

      assert (Memory.anybytes piter 8 = scalar piter (word.of_Z x9)) by admit.
      rewrite H25.
      eassert ((scalar piter (word.of_Z x9) * _)%sep m0) by ecancel_assumption.
      destruct H27, H27, H27, H28.
      eexists. eexists. split.
      {
        eapply H28.
      }
      split; [apply map.split_comm; eauto| ].

      assert (Memory.anybytes pc 8 = Bignum.Bignum 1 pc [x8]) by admit.
      rewrite H30.
      eassert ((Bignum.Bignum 1 pc [x8] * _)%sep x18) by ecancel_assumption.
      destruct H31, H31, H31, H32.
      do 2 eexists. split; eauto.
      split; [eapply map.split_comm; eauto| ].

      assert (Memory.anybytes pPauxz 48 = FElem (Some tight_bounds) pPauxz x7) by admit.
      rewrite H34.
      eassert ((FElem (Some tight_bounds) pPauxz x7 * _)%sep x20) by ecancel_assumption.
      destruct H35, H35, H35, H36.
      do 2 eexists. split; eauto.
      split; [eapply map.split_comm; eauto| ].

      assert (Memory.anybytes pPauxy 48 = FElem (Some tight_bounds) pPauxy x6) by admit.
      rewrite H38.
      eassert ((FElem (Some tight_bounds) pPauxy x6 * _)%sep x22) by ecancel_assumption.
      destruct H39, H39, H39, H40.
      do 2 eexists. split; eauto.
      split; [eapply map.split_comm; eauto| ].

      assert (Memory.anybytes pPauxx 48 = FElem (Some tight_bounds) pPauxx x5) by admit.
      rewrite H42.
      eassert ((FElem (Some tight_bounds) pPauxx x5 * _)%sep x24) by ecancel_assumption.
      destruct H43, H43, H43, H44.
      do 2 eexists. split; eauto.
      split; [eapply map.split_comm; eauto| ].
      split; eauto.
      split.
      1: admit. (*What is this trace even supposed to do????*)
      do 7 eexists. split.
      2: {
        ecancel_assumption.
      }
      1: {
        eauto.
        rewrite H22.
        assert (n_init mod 2 ^ (Z.of_nat v) = n_init) by admit.
        rewrite H46.
        eauto.
    Admitted.

    



    From bedrock2 Require Import ToCString Bytedump.
    Definition c_mod := (c_module (scalar_mult_func :: nil)).

    Eval native_compute in c_mod.

    End __.
