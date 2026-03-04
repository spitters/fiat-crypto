Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZero.
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
  (* Definition width := 64%Z. *)
  Context {width : Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
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

    (* Instance spec_of_loop_body : spec_of "loop_body" := spec_of_loop_body (curve_add:=curve_add). *)

    Instance spec_of_store_zero : spec_of "store_zero" := spec_of_store_zero.

    Context {scalar_words : nat}.

    Definition scalar_bits := (width * Z.of_nat scalar_words).

    Context {scalar_words_ok1 : scalar_bits < 2 ^ width}.
    (* Context {scalar_words_ok2 : (0 < scalar_words)%nat}. *)

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
             * Bignum.Bignum scalar_words pn n
             * R)%sep mem
        ;
          ensures tr' mem' :=
            tr = tr'
            /\ exists Pxnew Pynew Pznew Outxnew Outynew Outznew (* output values *)
              : F,
            exists nnew : list word,
              (Outxnew, Outynew, Outznew) = (@scmul _ field_parameters curve_add) (Z.to_nat (Positional.eval (uweight width) scalar_words (List.map word.unsigned n))) (Px, Py, Pz)
              /\ (FElem (Some tight_bounds) pPx Pxnew
                 * FElem (Some tight_bounds) pPy Pynew
                 * FElem (Some tight_bounds) pPz Pznew
                 * FElem (Some tight_bounds) pOutx Outxnew
                 * FElem (Some tight_bounds) pOuty Outynew
                 * FElem (Some tight_bounds) pOutz Outznew
                 * Bignum.Bignum scalar_words pn nnew
                 * R)%sep mem'}.

    Require Import bedrock2.NotationsCustomEntry.
    Require Import bedrock2.WeakestPrecondition.
    Import Syntax BinInt String List.ListNotations.
    Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

    (* MaxBounds lemmas *)
    Lemma max_bounds_map_max_range w n : @MaxBounds.max_bounds w n = List.map Some (List.repeat (@MaxBounds.max_range w) n).
    Proof. rewrite ListUtil.map_repeat. reflexivity. Qed.

    Lemma eval_max_range_lower w n :
      (0 <= w) ->
      Positional.eval (uweight w) n (List.map ZRange.lower (List.repeat (@MaxBounds.max_range w) n)) = 0.
    Proof.
      intros.
      induction n.
      - reflexivity.
      - simpl.
        rewrite Positional.eval_cons.
        rewrite uweight_eval_shift.
        3, 4: now rewrite map_length, repeat_length.
        2: assumption.
        rewrite uweight_0, IHn.
        lia.
    Qed.

    Lemma eval_max_range_upper w n :
      0 <= w ->
       Positional.eval (uweight w) n (List.map ZRange.upper (List.repeat (@MaxBounds.max_range w) n)) = 2 ^ (w * Z.of_nat n) - 1.
    Proof.
      induction n; intros.
      - simpl.
        rewrite Z.mul_0_r.
        rewrite Positional.eval_nil.
        reflexivity.
      -
        rewrite Nat2Z.inj_succ.
        remember (Z.of_nat n). simpl.
        rewrite Positional.eval_cons.
        rewrite uweight_eval_shift.
        3, 4: now rewrite map_length, repeat_length.
        2: auto.
        rewrite uweight_1, uweight_0, IHn; auto.
        rewrite Z.mul_succ_r.
        rewrite Z.pow_add_r.
        nia.
        nia.
        nia.
    Qed.

    Ltac solve_locals5 l3 l2 l1 l0 l :=
      subst l3 l2 l1 l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

    Ltac update_mem :=
      match goal with
      | Hsplit : map.split ?comb ?mem ?stack |- _ =>
          match goal with
          | Hold_mem : ?p mem,
              Hstack : Memory.anybytes ?a felem_size_in_bytes stack
            |- _ =>
              let x := fresh "x" in
              let Hmem := fresh "Hmem" in
              eapply FElem_from_bytes in Hstack as [x Hstack]
              ; eassert (Hnew_mem : (p ⋆ FElem None a x) comb) by (eexists; eauto)
              ; clear dependent mem
              ; clear dependent stack
              ; rename Hnew_mem into Hmem
          | Hold_mem : ?p mem,
              Hstack : Memory.anybytes ?a (Memory.bytes_per_word _) stack
            |- _ =>
              let x := fresh "x" in
              let Hmem := fresh "Hmem" in
              eapply anybytes_to_scalar in Hstack as [x Hstack]
              ; eassert (Hnew_mem : (p ⋆ scalar a x) comb) by (eexists; eauto)
              ; clear dependent mem
              ; clear dependent stack
              ; rename Hnew_mem into Hmem
          end
      end.

  Ltac straightline' :=
    match goal with
    | |- felem_size_in_bytes mod _ = 0 => eapply felem_size_in_bytes_mod
    | |- ?a mod ?a = 0 => eapply Z_mod_same_full
    | _ => update_mem
    | _ => straightline
    | l := _ : map.rep |- _ => subst l
    | l := _ : list word.rep |- _ => subst l
    | |- Some _ = Some _ => try reflexivity
    | |- exists _, _ => eexists
    | |- _ /\ _ => split
    | |- map.get _ _ = _ => repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same
    end.

  Ltac sep_and_fwd :=
    match goal with
    | H : context[fun m => _] |- _ =>
        let Hnew1 := fresh "Hmem" in
        let Hnew2 := fresh "Hmem" in
        eassert (Hnew1 : ((fun m => _) ⋆ _) _) by ecancel_assumption;
        eapply sep_and_l_fwd in Hnew1 as [Hnew1 Hnew2];
        clear H
    end.

    Definition scalar_mult_func : bedrock2.Syntax.func :=
        ("scalar_mult", (["px"; "py"; "pz"; "outx"; "outy"; "outz"; "pn"], []:list String.string, bedrock_func_body:(
        stackalloc felem_size_in_bytes as pauxx;
        stackalloc felem_size_in_bytes as pauxy;
        stackalloc felem_size_in_bytes as pauxz;
        stackalloc (Memory.bytes_per_word width) as cond;
        stackalloc (Memory.bytes_per_word width) as iter;
        coq:(cmd.call [] "store_zero" [expr.var "outx"; expr.var "outy"; expr.var "outz"]);
        coq:(cmd.store access_size.word (expr.var "iter") (expr.literal 0));
        while (coq:( expr.op bopname.ltu (expr.load access_size.word (expr.var "iter")) scalar_bits )){
            coq:(cmd.store access_size.word (expr.var "iter") (expr.op bopname.add (expr.load access_size.word "iter") (expr.literal 1)));
            coq:(cmd.call [] "loop_body"
                   [expr.var "px"; expr.var "py"; expr.var "pz"; expr.var "outx"; expr.var "outy"; expr.var "outz"; expr.var "pauxx"; expr.var "pauxy"; expr.var "pauxz"; expr.var "pn"; expr.var "cond" ])
        }
        ))).

        (* From bedrock2 Require Import ToCString Bytedump. *)
        (* Definition c_mod := (c_module (scalar_mult_func :: nil)). *)
        (* Eval native_compute in c_mod. *)


    (* Opaque felem_size_in_words. *)
    Opaque felem_size_in_bytes.
    Opaque scalar_words.
    Opaque scalar_bits.
    Opaque Memory.bytes_per_word.
    Opaque Z.of_nat.

    (* Lemma width_in_bytes_mod_width : *)
    (*   width_in_bytes mod Memory.bytes_per_word width = 0. *)
    (* Proof. *)
    (*   unfold Memory.bytes_per_word. *)

Require Import Crypto.COperationSpecifications.

    Lemma max_bounds_words : forall (x : list word) n, length x = n -> list_Z_bounded_by (@MaxBounds.max_bounds width n) (List.map word.unsigned x).
    Proof.
        intros. generalize dependent x.
        induction n; intros.
            - destruct x; try discriminate. simpl. cbv. auto.
            - destruct x; try discriminate. simpl.
              eapply Util.list_Z_bounded_by_cons. split.
              2: {
                  simpl in IHn. eapply IHn. auto.
              }
              apply Expr.is_bounded_by_bool_width_range.
              eauto.
              pose proof Properties.word.unsigned_range. auto.
    Qed.

  Instance spec_of_loop_body : spec_of "loop_body" :=
    fnspec! "loop_body"
          (pPx pPy pPz pOutx pOuty pOutz pPauxx pPauxy pPauxz pn pc : word)
          / (Px Py Pz Outx Outy Outz Pauxx Pauxy Pauxz Px_init Py_init Pz_init : F) (iter : nat) (n_init : Z) (n : list word) (c : word) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pPx Px
         * FElem (Some tight_bounds) pPy Py
         * FElem (Some tight_bounds) pPz Pz
         * FElem (Some tight_bounds) pOutx Outx
         * FElem (Some tight_bounds) pOuty Outy
         * FElem (Some tight_bounds) pOutz Outz
         * FElem None pPauxx Pauxx
         * FElem None pPauxy Pauxy
         * FElem None pPauxz Pauxz
         * Bignum.Bignum scalar_words pn n
         * scalar pc c
         * R)%sep mem
        (* these bounds should be incorporated in the Bignum.Bignum predicate, as it is in FElem *)
         /\ (Positional.eval (uweight width) scalar_words (List.map word.unsigned n)) = Z.shiftr n_init (Z.of_nat iter)
         /\ (Outx, Outy, Outz) = scmul (curve_add:=curve_add) (Z.to_nat (n_init mod (2 ^ (Z.of_nat iter))))%Z (Px_init, Py_init, Pz_init)
         /\ (Px, Py, Pz) = scmul (curve_add:=curve_add) (2 ^ iter) (Px_init, Py_init, Pz_init)
         ;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Pxnew Pynew Pznew Outxnew Outynew Outznew Pauxxnew Pauxynew Pauxznew (* output values *)
                  : F,
           exists nnew : list word,
           exists cnew : word,
               (*n*)
            (Positional.eval (uweight width) scalar_words (List.map word.unsigned nnew)) = Z.shiftr n_init (Z.of_nat (iter + 1))
            /\ (Outxnew, Outynew, Outznew) = scmul (curve_add:=curve_add) (Z.to_nat (n_init mod (2 ^ (Z.of_nat (iter + 1)))))%Z (Px_init, Py_init, Pz_init)
            /\ (Pxnew, Pynew, Pznew) = scmul (curve_add:=curve_add) (2 ^ (iter + 1)) (Px_init, Py_init, Pz_init)
          /\ (FElem (Some tight_bounds) pPx Pxnew
                * FElem (Some tight_bounds) pPy Pynew
                * FElem (Some tight_bounds) pPz Pznew
                * FElem (Some tight_bounds) pOutx Outxnew
                * FElem (Some tight_bounds) pOuty Outynew
                * FElem (Some tight_bounds) pOutz Outznew
                * FElem (Some tight_bounds) pPauxx Pauxxnew
                * FElem (Some tight_bounds) pPauxy Pauxynew
                * FElem (Some tight_bounds) pPauxz Pauxznew
                * Bignum.Bignum scalar_words pn nnew
                * scalar pc cnew
                * R)%sep mem'}.

    Lemma scalar_mult_ok : program_logic_goal_for_function! scalar_mult_func.
    Proof.
      enter scalar_mult_func.
      repeat straightline'.

      eexists; split.
      cbv [map.of_list_zip]; simpl; eauto.

      repeat straightline'.

      straightline_call.

      ecancel_assumption_impl.
      clear dependent mCombined.
      repeat straightline'.

      remember #{ "px" => pPx; "py" => pPy; "pz" => pPz; "outx" => pOutx; "outy" => pOuty; "outz" => pOutz; "pn" => pn; "pauxx" => a; "pauxy" => a0; "pauxz" => a1; "cond" => a2; "iter" => a3 }# as l.

      clear dependent a5.

      exists nat.
      eexists (fun a => (fun b => b < a <= Z.to_nat scalar_bits)%nat).

      rename a3 into piter.
      rename v into iter.

      rename a2 into pc.
      rename x2 into c.

      rename a into pPauxx.
      rename a0 into pPauxy.
      rename a1 into pPauxz.
      rename x into pauxx.
      rename x0 into pauxy.
      rename x1 into pauxz.

      remember ((Positional.eval (uweight width) scalar_words (List.map word.unsigned n))) as n_init.

      assert (nlength : Datatypes.length n = scalar_words).
      { eassert (htemp : (Bignum.Bignum _ _ _ ⋆ _) _) by ecancel_assumption.
        destruct htemp as [?[?[?[htemp ?]]]].
        destruct htemp as [?[?[?[htemp ?]]]].
      destruct htemp. assumption. }

      rename Px into Px_old.
      rename Py into Py_old.
      rename Pz into Pz_old.

      rename a4 into tr.

      exists ( fun (v : nat) (tr' : Semantics.trace) (m' : mem) (l' : locals) =>
        l' = l /\
        tr' = tr /\
          exists Pauxx Pauxy Pauxz c viter Px Py Pz Outx Outy Outz n,

        ( scalar piter (word.of_Z viter)
        * FElem (Some tight_bounds) pPx Px
        * FElem (Some tight_bounds) pPy Py
        * FElem (Some tight_bounds) pPz Pz
        * FElem (Some tight_bounds) pOutx Outx
        * FElem (Some tight_bounds) pOuty Outy
        * FElem (Some tight_bounds) pOutz Outz
        * FElem None pPauxx Pauxx
        * FElem None pPauxy Pauxy
        * FElem None pPauxz Pauxz
        * Bignum.Bignum scalar_words pn n
        * scalar pc c
        * R)%sep m'
        /\ (Positional.eval (uweight width) scalar_words (List.map word.unsigned n)) = Z.shiftr n_init (Z.of_nat v)
        /\ (Outx, Outy, Outz) = @scmul _ field_parameters curve_add  (Z.to_nat (n_init mod (2 ^ (Z.of_nat v))))%Z (Px_old, Py_old, Pz_old)
        /\ (Px, Py, Pz) = @scmul _ field_parameters curve_add (2 ^ v) (Px_old, Py_old, Pz_old)
        /\ viter = Z.of_nat v
        /\ (Z.of_nat v <= scalar_bits)
      ).
      split.
      eapply Nat.gt_wf.
      split.
      exists 0%nat.
      split. auto.
      split. auto.
      do 3 eexists.
      do 9 eexists.
      split.
      ecancel_assumption.
      split.
      rewrite Z.shiftr_0_r.
      easy.
      split.

      rewrite Z.pow_0_r.
      rewrite Z.mod_1_r.
      simpl.
      reflexivity.
      simpl.
      rewrite group_prop1.
      split; auto.
      split; auto.
      Transparent scalar_bits.
      unfold scalar_bits.
      destruct word_ok.
      clear -width_pos.
      nia.

      intros.

      eexists; split.
      cbv [map.of_list_zip]; simpl; eauto.

      repeat straightline'.
      clear dependent m.

      destruct H2.
      destruct H2.
      rewrite H2.

      split.
      repeat straightline'.
      clear dependent m0.

      straightline_call.
      split.
      ecancel_assumption.

      split.
      (* admit. *)
      (* split. *)


      eassumption.
      split.
      eassumption.
      eassumption.
      clear dependent m.

      repeat straightline'.

      rewrite <- word.ring_morph_add in H11.
      subst x4.
      replace (Z.of_nat v + 1) with (Z.of_nat (v + 1)) in H11 by lia.

      (* clear H4 H5 H6. *)

      ecancel_assumption_impl.
      eassumption.
      eassumption.
      eassumption.

      destruct (word.ltu (word.of_Z (Z.of_nat v)) (word.of_Z scalar_bits)) eqn:E.
      rewrite <- word.morph_ltu in E.
      lia.
      lia.
      lia.
      rewrite word.unsigned_of_Z_0 in H4. lia.
      lia.
      destruct (word.ltu (word.of_Z (Z.of_nat v)) (word.of_Z scalar_bits)) eqn:E.
      rewrite <- word.morph_ltu in E.
      lia.
      lia.
      lia.
      rewrite word.unsigned_of_Z_0 in H4. lia.

      repeat straightline.

      (* this is hacky, but note the order has to match order of the exists in the goal *)
      eassert ((_
                  ⋆ FElem _ pPauxx _
                  ⋆ FElem _ pPauxy _
                  ⋆ FElem _ pPauxz _
                  ⋆ scalar pc _
                  ⋆ scalar piter _) m0) by ecancel_assumption.
      clear H3.
      (* destruct H2 as [mq'[mr'[hs' [h'' Hr']]]]. *)
      (* destruct H2 as [?[?[?[? ?]]]]. *)
      do 5 match goal with
             | H : (_ ⋆ _) _ |- _ =>
                 let mq := fresh "mq" in
                 let mr := fresh "mr" in
                 let Hs := fresh "Hs" in
                 let H' := fresh "H" in
                 let Hr := fresh "Hr" in
                 destruct H as [mq[mr[Hs [H' Hr]]]]
             (* | H : FElem _ _ _ _ |- _ => eapply drop_bounds_FElem in H; eapply FElem_from_bytes in H *)
             (* | H : scalar _ _ _ |- _ => eapply scalar_to_anybytes in H *)
             end.
      eexists. eexists. split; [|split].
      eapply scalar_to_anybytes. eassumption.
      eassumption.
      eexists. eexists. split; [|split].
      eapply scalar_to_anybytes. eassumption.
      eassumption.
      eexists. eexists. split; [|split].
      eapply FElem_from_bytes. eexists. eassumption.
      eassumption.
      eexists. eexists. split; [|split].
      eapply FElem_from_bytes. eexists. eassumption.
      eassumption.
      eexists. eexists. split; [|split].
      eapply FElem_from_bytes. eexists. eassumption.
      eassumption.

      destruct (word.ltu (word.of_Z (Z.of_nat v)) (word.of_Z scalar_bits)) eqn:E.
      rewrite word.unsigned_of_Z_1 in H4. discriminate.
      rewrite <- word.morph_ltu in E.
      subst x4.
      assert (Heq : Z.of_nat v = scalar_bits) by lia.
      rewrite Heq in *.

      repeat straightline'.
      rewrite Z.mod_small in H6.
      eassumption.
(* Signature.max_bounds_words *)
      unshelve epose proof
        eval_list_Z_bounded_by
        (uweight width)
        scalar_words
        (@MaxBounds.max_bounds width scalar_words)
        (List.repeat (@MaxBounds.max_range width) scalar_words)
        (List.map word.unsigned n)
        _ _ _ _.
      eapply max_bounds_words.

      eassert ((Bignum.Bignum _ _ _ ⋆ _) _) by ecancel_assumption.
      destruct H1 as [mq'[mr'[hs[h1 h2]]]].
      destruct h1 as [mq''[mr''[hs'[h1' h2']]]].
      destruct h1'.
      assumption.
      eapply max_bounds_map_max_range.
      now rewrite repeat_length.
      intros.

      unshelve epose proof uwprops width _.
      destruct word_ok.
      assumption.
      destruct H3.
      lia.

      rewrite eval_max_range_lower in H1.
      rewrite eval_max_range_upper in H1.
      subst n_init.
      unfold scalar_bits.
      lia.
      destruct word_ok.
      clear -width_pos.
      lia.

      destruct word_ok.
      clear -width_pos.
      lia.




      ecancel_assumption.

      lia.
      lia.
      Qed.

     (* match goal with *)
     (* | Hsplit : map.split ?comb ?mem ?stack |- _ => *)
     (*     match goal with *)
     (*       Hold_mem : ?p mem, *)
     (*         Hstack : Memory.anybytes ?a felem_size_in_bytes stack *)
     (*       |- _ => *)
     (*         let x := fresh "x" in *)
     (*         let Hmem := fresh "Hmem" in *)
     (*         eapply FElem_from_bytes in Hstack as [x Hstack] *)
     (*         ; eassert (Hnew_mem : (p ⋆ FElem None a x) comb) by (eexists; eauto) *)
     (*         ; clear dependent mem *)
     (*         ; clear dependent stack *)
     (*         ; rename Hnew_mem into Hmem *)
     (*     end *)
     (* end. *)
     (*  update_mem. *)

     (*  straightline_call. *)

     (*  eexists; split; [ repeat (repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| ]); repeat straightline| ]. *)

     (*  straightline_call. *)

     (*  { *)
     (*    ecancel_assumption_impl. *)

     (*  } *)

     (*  eapply Proper_call; [| eapply Hspec1; ecancel_assumption]. *)
     (*  cbv [pointwise_relation Basics.impl]. repeat straightline. *)
     (*  eexists. split; [subst a6; eauto |]. *)

     (*  repeat straightline. *)
     (*  eexists; split; [repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| repeat straightline]| ]. *)
     (*  eexists; split; [repeat straightline| ]. *)

     (*  clear H1 H20 H18 H16 H14 H12. *)
     (*  assert (Hwa3 : exists wa3, (scalar a3 wa3) = (array ptsto (word.of_Z 1) a3 stack3)) by admit. *)
     (*  assert (Hwa2 : exists wa2, (scalar a2 wa2) = (array ptsto (word.of_Z 1) a2 stack2)) by admit. *)

     (*  destruct Hwa3, Hwa2. *)
     (*  rewrite <- H12 in H23. *)
     (*  rewrite <- H1 in H23.  *)
      (* assert (exists wa3, (scalar a3 wa3) = (array ptsto (word.of_Z 1) a3 stack3)) by admit.
      assert (exists wa3, (scalar a3 wa3) = (array ptsto (word.of_Z 1) a3 stack3)) by admit.
      assert (exists wa3, (scalar a3 wa3) = (array ptsto (word.of_Z 1) a3 stack3)) by admit. *)

      (* eapply store_word_of_sep; [ecancel_assumption| repeat straightline]. *)

      (* assert (Hc: exists wc, (scalar a2 x0) = Bignum.Bignum 1 a2 [wc]) by admit. *)
      (* destruct Hc. rewrite H16 in H14; clear H16. *)

      (* assert (Hf1 : exists f1, (FElem (Some tight_bounds) a1 f1) = (array ptsto (word.of_Z 1) a1 stack1)) by admit. *)
      (* destruct Hf1. rewrite <- H16 in H14. *)

      (* assert (Hf0 : exists f0, (FElem (Some tight_bounds) a0 f0) = (array ptsto (word.of_Z 1) a0 stack0)) by admit. *)
      (* destruct Hf0. rewrite <- H18 in H14. *)

      (* assert (Hf : exists f, (FElem (Some tight_bounds) a f) = (array ptsto (word.of_Z 1) a stack)) by admit. *)
      (* destruct Hf. rewrite <- H20 in H14. *)

      (* clear H16 H18 H20. *)

      (* rename a into pPauxx. *)
      (* rename a0 into pPauxy. *)
      (* rename a1 into pPauxz. *)
      (* rename a2 into pc. *)
      (* rename a3 into piter. *)


      (* remember ((Positional.eval (uweight 64) 6 (List.map word.unsigned n))) as n_init. *)
      (* remember (Px) as Px_init. *)
      (* remember (Py) as Py_init. *)
      (* remember (Pz) as Pz_init. *)


      (* eexists nat. eexists (fun s => (fun b => b < s < 400)%nat). *)


      (*Invariant*)
      
    (*   exists ( fun (v : nat) (tr : Semantics.trace) (m' : mem) (l' : locals) => *)
    (*     l' = l3 /\ *)
    (*       exists Pauxx Pauxy Pauxz c viter Px Py Pz Outx Outy Outz n, *)

    (*     ( scalar piter (word.of_Z viter) *)
    (*     * FElem (Some tight_bounds) pPx Px *)
    (*     * FElem (Some tight_bounds) pPy Py *)
    (*     * FElem (Some tight_bounds) pPz Pz *)
    (*     * FElem (Some tight_bounds) pOutx Outx *)
    (*     * FElem (Some tight_bounds) pOuty Outy *)
    (*     * FElem (Some tight_bounds) pOutz Outz *)
    (*     * FElem (Some tight_bounds) pPauxx Pauxx *)
    (*     * FElem (Some tight_bounds) pPauxy Pauxy *)
    (*     * FElem (Some tight_bounds) pPauxz Pauxz *)
    (*     * Bignum.Bignum 6 pn n *)
    (*     * Bignum.Bignum 1 pc [c] *)
    (*     * R)%sep m' *)
    (*     /\ (*n*) *)
    (*        (Positional.eval (uweight 64) 6 (List.map word.unsigned n)) = Z.shiftr n_init (Z.of_nat v) *)
    (*     /\ (Outx, Outy, Outz) = @scmul _ field_parameters curve_add  (Z.to_nat (n_init mod (2 ^ (Z.of_nat v))))%Z (Px_init, Py_init, Pz_init) *)
    (*     /\ (Px, Py, Pz) = @scmul _ field_parameters curve_add (2 ^ v) (Px_init, Py_init, Pz_init) *)
    (*     /\ viter = Z.of_nat (v) *)
    (*     /\ viter < 399 *)
    (*   ). *)


    (*   split. *)
    (*   { *)
    (*     admit. *)
    (*   } *)

    (*   split. *)
    (*   { *)
    (*     exists 0%nat. split; [reflexivity |]. exists x4. exists x3. exists x2. exists x1. exists 0. exists Px_init, Py_init, Pz_init. *)
    (*     exists Fzero, Fone, Fzero. exists n. *)

    (*     split; [| split; [| split; [| split]]]. *)
    (*       - ecancel_assumption. *)
    (*       - rewrite Z.shiftr_0_r. subst n_init. eauto. *)
    (*       - assert (2 ^ Z.of_nat 0 = 1) by admit. *)
    (*         assert (n_init mod 1 = 0) by admit. *)
    (*         rewrite H16, H18. simpl. eauto. *)
    (*       - simpl. rewrite group_prop1. eauto. *)
    (*       - lia. *)
    (*   } *)

    (*   repeat straightline. *)
    (*   eexists; split. *)
    (*   { *)
    (*     (repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| repeat straightline]). *)
    (*     eexists. split. *)
    (*       - repeat straightline. *)
    (*         eapply load_word_of_sep. ecancel_assumption. *)
    (*       - repeat straightline. *)
    (*   } *)

    (*   repeat straightline. *)
    (*   split. *)
    (*   { *)
    (*     repeat straightline. *)
    (*     eexists; split. *)
    (*     { *)
    (*       (repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| repeat straightline]). *)
    (*     } *)

    (*     repeat straightline. *)
    (*     eexists; split. *)
    (*     { *)
    (*       (repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| repeat straightline]). *)
    (*       eexists; split; repeat straightline. *)
    (*       eapply load_word_of_sep. ecancel_assumption. *)
    (*     } *)

    (*     eapply store_word_of_sep; [ecancel_assumption| ]. *)

    (*     repeat straightline. *)
    (*     eexists; split. *)
    (*     { *)
    (*       repeat (repeat straightline; eexists; split; [solve_locals5 l3 l2 l1 l0 l| repeat straightline]). *)
    (*     } *)

    (*     eapply Proper_call. *)

    (*     2: { *)
    (*       pose proof H0 as Hspec2. cbv [spec_of_loop_body LoopBody.spec_of_loop_body] in Hspec2. *)

    (*       specialize (Hspec2  pPx pPy pPz pOutx pOuty pOutz pPauxx pPauxy pPauxz pn pc). *)

    (*       eapply Hspec2; clear Hspec2. *)
    (*       split; [| split; [| split]]. *)

    (*         - clear H18 H14 H23.  ecancel_assumption. *)
    (*         - erewrite <- H20. eauto. *)
    (*         - rewrite H22. eauto. *)
    (*         - eassumption. *)
    (*     } *)

    (*     cbv [pointwise_relation Basics.impl]. *)
    (*     repeat straightline. *)
    (*     eexists; split; [subst a1; eauto| ]. *)

    (*     eexists. split; [split; eauto | ]. *)
    (*     1: { *)
    (*       do 12 eexists. *)
    (*       split; [| split; [| split; [| split; [| split] ]]]. *)
    (*       1: { *)
    (*         rewrite <- word.ring_morph_add in H32. *)
    (*         ecancel_assumption. *)
    (*       } *)
    (*       5: { *)
    (*         subst x9. destruct (word.ltu (word.of_Z (Z.of_nat v)) (word.of_Z 384)) eqn:eq. *)
    (*           2: { *)
    (*             rewrite word.unsigned_of_Z in H16. assert (@word.wrap width word word_ok Z0 = 0) by (cbv [word.wrap width]; lia). *)
    (*             rewrite H27 in H16. *)
    (*             exfalso. apply H16. auto. *)
    (*           } *)
    (*           pose proof eq. Search (word.ltu). *)
    (*           erewrite <- word.morph_ltu in H27. *)
    (*           3: cbv [width]; lia. *)
    (*           2: split; cbv [width]; lia. *)
    (*           lia. *)
    (*           } *)
    (*       4: { *)
    (*         subst x9. *)
    (*         assert (Z.of_nat ((v)) + 1 = Z.of_nat (v + 1)) by lia. *)
    (*         eapply H27. *)
    (*       } *)
    (*       3: eauto. *)
    (*       2: eauto. *)
    (*       eauto. *)
    (*     } *)
    (*     split; try lia. *)
    (*   } *)
    (*   repeat straightline. *)

    (*   assert (Memory.anybytes piter 8 = scalar piter (word.of_Z x9)) by admit. *)
    (*   rewrite H25. *)
    (*   eassert ((scalar piter (word.of_Z x9) * _)%sep m0) by ecancel_assumption. *)
    (*   destruct H27, H27, H27, H28. *)
    (*   eexists. eexists. split. *)
    (*   { *)
    (*     eapply H28. *)
    (*   } *)
    (*   split; [apply map.split_comm; eauto| ]. *)

    (*   assert (Memory.anybytes pc 8 = Bignum.Bignum 1 pc [x8]) by admit. *)
    (*   rewrite H30. *)
    (*   eassert ((Bignum.Bignum 1 pc [x8] * _)%sep x18) by ecancel_assumption. *)
    (*   destruct H31, H31, H31, H32. *)
    (*   do 2 eexists. split; eauto. *)
    (*   split; [eapply map.split_comm; eauto| ]. *)

    (*   assert (Memory.anybytes pPauxz 48 = FElem (Some tight_bounds) pPauxz x7) by admit. *)
    (*   rewrite H34. *)
    (*   eassert ((FElem (Some tight_bounds) pPauxz x7 * _)%sep x20) by ecancel_assumption. *)
    (*   destruct H35, H35, H35, H36. *)
    (*   do 2 eexists. split; eauto. *)
    (*   split; [eapply map.split_comm; eauto| ]. *)

    (*   assert (Memory.anybytes pPauxy 48 = FElem (Some tight_bounds) pPauxy x6) by admit. *)
    (*   rewrite H38. *)
    (*   eassert ((FElem (Some tight_bounds) pPauxy x6 * _)%sep x22) by ecancel_assumption. *)
    (*   destruct H39, H39, H39, H40. *)
    (*   do 2 eexists. split; eauto. *)
    (*   split; [eapply map.split_comm; eauto| ]. *)

    (*   assert (Memory.anybytes pPauxx 48 = FElem (Some tight_bounds) pPauxx x5) by admit. *)
    (*   rewrite H42. *)
    (*   eassert ((FElem (Some tight_bounds) pPauxx x5 * _)%sep x24) by ecancel_assumption. *)
    (*   destruct H43, H43, H43, H44. *)
    (*   do 2 eexists. split; eauto. *)
    (*   split; [eapply map.split_comm; eauto| ]. *)
    (*   split; eauto. *)
    (*   split. *)
    (*   1: admit. (*What is this trace even supposed to do????*) *)
    (*   do 7 eexists. split. *)
    (*   2: { *)
    (*     ecancel_assumption. *)
    (*   } *)
    (*   1: { *)
    (*     eauto. *)
    (*     rewrite H22. *)
    (*     assert (n_init mod 2 ^ (Z.of_nat v) = n_init) by admit. *)
    (*     rewrite H46. *)
    (*     eauto. *)
    (* Admitted. *)





    (* From bedrock2 Require Import ToCString Bytedump. *)
    (* Definition c_mod := (c_module (scalar_mult_func :: nil)). *)

    (* Eval native_compute in c_mod. *)

    End __.
