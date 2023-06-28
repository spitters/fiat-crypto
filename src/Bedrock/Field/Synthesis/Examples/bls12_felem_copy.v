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
    Existing Instance bls12_field_parameters.
    Existing Instance bls12_field_representation.

    Definition felem_copy_func : Syntax.func := (felem_copy, (["out"; "in"], (nil : list string), bedrock_func_body:(
      coq:(cmd.store access_size.word (expr.var "out") (expr.load access_size.word (expr.var "in")));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (8)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (16)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (24)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (32))))); coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (40)))))
    ))).

    From bedrock2 Require Import ToCString Bytedump.
    Definition c_mod := (c_module (felem_copy_func :: nil)).
    Eval compute in c_mod.

    Ltac collect H1 H2 := let Hnew := (fresh "Hnew") in
    eassert (Hnew : id (fun m => (_ m) /\ (_ m)) _) by (cbv [id]; split; [eapply H1| eapply H2]); clear H1 H2.

    Local Infix "+w" := word.add (at level 80).
    Local Infix "*w" := word.mul (at level 70).

    Instance bls12_felem_copy : spec_of felem_copy := spec_of_felem_copy.

    Lemma felem_copy_ok : program_logic_goal_for_function! felem_copy_func.
    Proof.
      cbv [bls12_felem_copy Field.spec_of_felem_copy]. cbv [program_logic_goal_for].
      intros. simpl.
      repeat straightline.

      cbv [FElem Bignum.Bignum] in *.
      sepsimpl.

      assert (size : (felem_size_in_words = 6)%nat) by auto.
      rewrite size in *.
      do 7 (destruct x0; try discriminate).
      do 7 (destruct x1; try discriminate).
      do 7 (destruct x2; try discriminate).
      repeat seprewrite_in (array_cons (T:=@word.rep 64 BasicC64Semantics.word) (word:=BasicC64Semantics.word) (mem:=BasicC64Semantics.mem)) H9.
      repeat seprewrite_in (array_cons (T:=@word.rep 64 BasicC64Semantics.word) (word:=BasicC64Semantics.word) (mem:=BasicC64Semantics.mem)) H6.
      repeat seprewrite_in (array_nil (T:=@word.rep 64 BasicC64Semantics.word) (word:=BasicC64Semantics.word) (mem:=BasicC64Semantics.mem)) H9.
      repeat seprewrite_in (array_nil (T:=@word.rep 64 BasicC64Semantics.word) (word:=BasicC64Semantics.word) (mem:=BasicC64Semantics.mem)) H6.

      cbn [word.of_Z Memory.bytes_per_word] in *.
      replace (Memory.bytes_per_word 64) with 8 in * by reflexivity.
      rewrite <- word.add_assoc in H6.
      rewrite <- word.ring_morph_add in H6.

      Ltac straightline' :=
        match goal with
        | |- store Syntax.access_size.word _ _ _ _ =>
            eapply store_word_of_sep_2
        | _ => straightline
        end.

      repeat match goal with
             | H : context[ _ +w _ +w _ ] |- _ =>
                 rewrite <- word.add_assoc, <- word.ring_morph_add in H
             end.
      cbn -[scalar] in H9.
      cbn -[scalar] in H6.

      (* clear H6. *)
      do 2 straightline'.
      1: clear H6; ecancel_assumption.
      1: clear H9; ecancel_assumption.
      clear H6 H9.
      (* clear dependent mem. *)
      do 7 straightline'.
      1: clear H6; ecancel_assumption.
      1: clear H9; ecancel_assumption.
      clear H6 H9.
      do 7 straightline'.
      1: clear H6; ecancel_assumption.
      1: clear H9; ecancel_assumption.
      clear H6 H9.
      do 7 straightline'.
      1: clear H6; ecancel_assumption.
      1: clear H9; ecancel_assumption.
      clear H6 H9.
      do 7 straightline'.
      1: clear H6; ecancel_assumption.
      1: clear H9; ecancel_assumption.
      clear H6 H9.
      do 7 straightline'.
      1: clear H6; ecancel_assumption.
      1: clear H9; ecancel_assumption.
      clear H6 H9.
      repeat straightline'.
      split; auto.
      split; auto.

      (* this needs to be done before introducing the following evars *)
      eassert ((_ ⋆ Rout) m) by ecancel_assumption.
      destruct H10 as [mq[mr[Hsplit[Hout HRout]]]].

      eexists. eexists. split.
      eassumption.
      split.
      eexists.
      sepsimpl.
      eassumption.
      assumption.
      assumption.
      repeat seprewrite (array_cons (T:=@word.rep 64 BasicC64Semantics.word) (word:=BasicC64Semantics.word) (mem:=BasicC64Semantics.mem)).
      repeat match goal with
             | |- context[ _ +w _ +w _ ] =>
                 rewrite <- word.add_assoc, <- word.ring_morph_add
             end.
      cbn -[scalar].
      ecancel_assumption.
      ecancel_assumption.

    Qed.

End FelemCopy.
