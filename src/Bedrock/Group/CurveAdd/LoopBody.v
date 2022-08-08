Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZeroGSpec.
Require Import Crypto.Bedrock.Specs.AbstractField.
(* Require Import Crypto.Bedrock.Specs.PrimeField. *)
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAddAlt.
Require Import Crypto.Bedrock.Group.CurveAdd.BignumShift.
Require Import Crypto.Bedrock.Group.CurveAdd.CondMoveGroup.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
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
  Context {field_parameters : AbstractField.FieldParameters}
          {field_parameters_ok : AbstractField.FieldParameters_ok}.
  
  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}
          {group_cmov : string}
          {store_zero : string}.

  Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.
  Instance my_field_representation : FieldRepresentation.
  Proof.
      exact field_representation.
  Defined.

  Context (Hbounds_eq : loose_bounds = tight_bounds).
  Context (three_b : felem).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Instance spec_of_curve_add : spec_of "ladderstep".
  Proof.
    eapply (spec_of_curve_add_alt). exact three_b.
  Defined.


  Instance spec_of_bignum_shift : spec_of "shift_scalar".
  Proof.
    eapply spec_of_shift_scalar.
  Defined.

  Instance spec_of_cond_move : spec_of "group_cmov".
  Proof.
    eapply spec_of_group_cmov.
  Defined.

  Instance spec_of_store_zero : spec_of "store_zero_G".
  Proof.
    eapply spec_of_store_zero.
  Defined.


  Context {n_init : Z}
          {Px_init Py_init Pz_init : F}
          {curve_add : (F * F * F) -> (F * F * F) -> (F * F * F)}.

          Fixpoint scmul (n : nat)  : F * F * F -> F * F * F :=
            fun (P : F * F * F) =>
              let X := (fst (fst P) ) in
              let Y := (snd (fst P)) in
              let Z := (snd P) in
            match n with
            | O => (Fzero, Fone, Fzero)
            | S m => curve_add (X, Y, Z) (scmul m (X, Y, Z))
            end.
        
  Context {group_prop1 : forall x y z a b c n m k,
        @CurveAdd.ladderstep_gallina _ _ _ _ field_parameters field_representation three_b x y z a b c = \<n, m, k\>
        -> (n, m, k) = curve_add (x, y, z) (a, b, c)}
        {group_prop2 : forall x y z n m k iter xinit yinit zinit,
        (n, m, k) = curve_add (x, y, z) (x, y, z) ->
        (x, y, z) = scmul (2 ^ iter) (xinit, yinit, zinit) ->
        (n, m, k) = scmul (2 ^ (iter + 1)) (xinit, yinit, zinit)}
        .

  Context (group_property1 : forall x, curve_add (Fzero, Fone, Fzero) x = x) .

  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

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
         * FElem (Some tight_bounds) pPauxx Pauxx
         * FElem (Some tight_bounds) pPauxy Pauxy
         * FElem (Some tight_bounds) pPauxz Pauxz
         * Bignum.Bignum 6 pn n
         * Bignum.Bignum 1 pc [c]
         * R)%sep mem
         /\ (*n*)
            (Positional.eval (uweight 64) 6 (List.map word.unsigned n)) = Z.shiftr n_init (Z.of_nat iter)
         /\ (Outx, Outy, Outz) = scmul  (Z.to_nat (n_init mod (2 ^ (Z.of_nat iter))))%Z (Px_init, Py_init, Pz_init)
         /\ (Px, Py, Pz) = scmul (2 ^ iter) (Px_init, Py_init, Pz_init)
         ;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Pxnew Pynew Pznew Outxnew Outynew Outznew Pauxxnew Pauxynew Pauxznew (* output values *)
                  : F,
           exists nnew : list word,
           exists cnew : word,
               (*n*)
               (Positional.eval (uweight 64) 6 (List.map word.unsigned nnew)) = Z.shiftr n_init (Z.of_nat (iter + 1))
            /\ (Outxnew, Outynew, Outznew) = scmul  (Z.to_nat (n_init mod (2 ^ (Z.of_nat (iter + 1)))))%Z (Px_init, Py_init, Pz_init)
            /\ (Pxnew, Pynew, Pznew) = scmul (2 ^ (iter + 1)) (Px_init, Py_init, Pz_init)

          /\ (FElem (Some tight_bounds) pPx Pxnew
                * FElem (Some tight_bounds) pPy Pynew
                * FElem (Some tight_bounds) pPz Pznew
                * FElem (Some tight_bounds) pOutx Outxnew
                * FElem (Some tight_bounds) pOuty Outynew
                * FElem (Some tight_bounds) pOutz Outznew
                * FElem (Some tight_bounds) pPauxx Pauxxnew
                * FElem (Some tight_bounds) pPauxy Pauxynew
                * FElem (Some tight_bounds) pPauxz Pauxznew
                * Bignum.Bignum 6 pn nnew
                * Bignum.Bignum 1 pc [cnew]
                * R)%sep mem'}.

  Require Import bedrock2.NotationsCustomEntry.
  Require Import bedrock2.WeakestPrecondition.
  Import Syntax BinInt String List.ListNotations.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
             

  Definition loop_body_func : bedrock2.Syntax.func :=
    ("loop_body", (["px"; "py"; "pz"; "outx"; "outy"; "outz"; "pauxx"; "pauxy"; "pauxz"; "pn"; "pc"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] ("store_zero_G") [expr.var ("pauxx"); expr.var ("pauxy"); expr.var ("pauxz")]);
      coq:(cmd.call [] ("shift_scalar") [expr.var ("pc"); expr.var ("pn")]);
      coq:(cmd.call [] ("group_cmov") [expr.var ("pauxx"); expr.var ("pauxy"); expr.var ("pauxz"); expr.var ("outx"); expr.var ("outy"); expr.var ("outz"); expr.var ("px"); expr.var ("py"); expr.var ("pz"); expr.var("pc")]);
      coq:(cmd.call [] ("ladderstep") [expr.var ("outx"); expr.var ("outy"); expr.var ("outz"); expr.var ("pauxx"); expr.var ("pauxy"); expr.var ("pauxz"); expr.var ("outx"); expr.var ("outy"); expr.var ("outz")]);
      coq:(cmd.call [] ("ladderstep") [expr.var ("px"); expr.var ("py"); expr.var ("pz"); expr.var ("px"); expr.var ("py"); expr.var ("pz"); expr.var ("px"); expr.var ("py"); expr.var ("pz")])
    ))).

    From bedrock2 Require Import ToCString Bytedump.
    Definition c_mod := (c_module (loop_body_func :: nil)).
    Eval native_compute in c_mod.

    Print c_mod.

    Lemma loop_body_ok : program_logic_goal_for_function! loop_body_func.
    Proof.
      repeat straightline.
      eexists; split.
      {
        repeat straightline. eexists. split.
          - subst l.
            repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
            eapply map.get_put_same.
          - repeat straightline. eexists. split.
          {
            subst l.
            repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
            eapply map.get_put_same.
          }
          repeat straightline. eexists. split.
          {
            subst l.
            repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
            eapply map.get_put_same.
          }
          repeat straightline.
      }
      repeat straightline.

      eapply Proper_call.
      2: {
        eapply H. ecancel_assumption.
      }
      cbv [pointwise_relation Basics.impl].
      repeat straightline.

      eexists. split.
      {
        subst l. repeat straightline. eexists; split.
        {
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists; split.
        {
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline.
      }

      eapply Proper_call.
      2: eapply H0; ecancel_assumption.

      cbv [pointwise_relation Basics.impl].
      repeat straightline.

      eexists. split.
      {
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. 
      }

      assert (length x0 = 1)%nat.
      {
        cbv [Bignum.Bignum] in H12. sepsimpl. eauto.
      }
      destruct x0; try discriminate.
      destruct x0; try discriminate.

      eapply Proper_call.
      2: eapply H1.
      2: {
        cbv [my_field_representation] in *.
        split; [ecancel_assumption| ].
        eassert (Positional.eval (uweight 64) 1 [word.unsigned r] = word.unsigned r).
        {
          rewrite Positional.eval_cons; eauto. simpl.
          cbv [uweight ModOps.weight]; simpl.
          rewrite Positional.eval_nil. lia.
        }
        simpl in H11.
        rewrite H13 in H11.

        cbv [ZRange.is_bounded_by_bool]. simpl.
        assert (0 <=? word.unsigned r = true).
        {
          rewrite <- H11; lia.
        }
        rewrite H14.
        assert (word.unsigned r <=? 1 = true) by (rewrite <- H11; lia).
        rewrite H15. auto.
      }

      cbv [pointwise_relation Basics.impl].
      repeat straightline.

      repeat straightline. eexists. split.
      {
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline.
      }

      eapply Proper_call.
      2 : {
        eapply H2.
        cbv [CurveAddAlt.my_field_representation my_field_representation] in *.
        do 2 (try split); ecancel_assumption.
      }

      cbv [pointwise_relation Basics.impl].
      repeat straightline.

      eexists. split.
      {
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline. eexists. split.
        {
          subst l.
          repeat (erewrite map.get_put_diff; [| intros contra; discriminate]).
          eapply map.get_put_same.
        }
        repeat straightline.
      }
      eapply Proper_call.

      2: {
        eapply H2.
        cbv [CurveAddAlt.my_field_representation my_field_representation] in *.
        repeat (try split); ecancel_assumption.
      }

      cbv [pointwise_relation Basics.impl].

      repeat straightline.

      split; auto.
      split; [admit| ]. (*What is this trace? Check callees to make sure it is not changed*)

      do 11 eexists.
      repeat try split.
      4: {
        cbv [CurveAddAlt.my_field_representation my_field_representation] in *.
        ecancel_assumption.
      }
      3: { eapply group_prop1 in H20. eapply group_prop2; eauto. }
      2: {
        eapply group_prop1 in H18. rewrite H18.
        destruct (word.unsigned r =? 1) eqn:eq.
        {
          subst x0. subst x1. subst x2. pose proof eq.
          (*Prove this at a higher level*)
          assert (word.unsigned r =? 1 = true ->
                  (Px, Py, Pz) = scmul (2 ^ iter) (Px_init0, Py_init0, Pz_init0) ->
                  (Outx, Outy, Outz) = scmul (Z.to_nat (n_init mod 2 ^ Z.of_nat iter)) (Px_init0, Py_init0, Pz_init0) -> 
                  curve_add (Outx, Outy, Outz) (Px, Py, Pz) = scmul (Z.to_nat (n_init mod 2 ^ Z.of_nat (iter + 1))) (Px_init0, Py_init0, Pz_init0)
          ) by admit.

          apply H14; eauto.
        }

        subst x0. subst x1. subst x2.
        admit.
      }

      admit.
    

    Admitted.


(*
  Lemma compile_ladderstep {tr m l functions}
        (x1 x2 y1 y2 z1 z2 xout1 yout1 zout1 : F) :
    let v := @ladderstep_gallina _ _ _ _ _ _ three_b x1 x2 y1 y2 z1 z2 xout1 yout1 zout1 in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           Rout
           X1_ptr X1_var X2_ptr X2_var Y1_ptr Y1_var Y2_ptr Y2_var
           Z1_ptr Z1_var Z2_ptr Z2_var Xout_ptr Xout_var Yout_ptr Yout_var Zout_ptr Zout_var,

      spec_of_ladderstep functions ->

      (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) X2_ptr x2 *
       FElem (Some tight_bounds) Y1_ptr y1 * FElem (Some tight_bounds) Y2_ptr y2 *
       FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) Z2_ptr z2 *
       FElem (Some tight_bounds) Xout_ptr xout1 * 
       FElem (Some tight_bounds) Yout_ptr yout1 * FElem (Some tight_bounds) Zout_ptr zout1 * Rout)%sep m ->

      map.get l X1_var = Some X1_ptr ->
      map.get l X2_var = Some X2_ptr ->
      map.get l Y1_var = Some Y1_ptr ->
      map.get l Y2_var = Some Y2_ptr ->
      map.get l Z1_var = Some Z1_ptr ->
      map.get l Z2_var = Some Z2_ptr ->
      map.get l Xout_var = Some Xout_ptr ->
      map.get l Yout_var = Some Yout_ptr ->
      map.get l Zout_var = Some Zout_ptr ->

      (let v := v in
       forall (* output values *) m',
       let '\<Xout', Yout', Zout'\> := @ladderstep_gallina _ _ _ _ _ _ three_b x1 x2 y1 y2 z1 z2 xout1 yout1 zout1 in
            (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) X2_ptr x2 *
            FElem (Some tight_bounds) Y1_ptr y1 * FElem (Some tight_bounds) Y2_ptr y2 *
            FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) Z2_ptr z2 *
            FElem (Some tight_bounds) Xout_ptr Xout' * 
            FElem (Some tight_bounds) Yout_ptr Yout' * FElem (Some tight_bounds) Zout_ptr Zout' * Rout)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->

      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq
        (cmd.call [] "ladderstep"
                  [ expr.var X1_var; expr.var X2_var;
                  expr.var Y1_var; expr.var Y2_var;
                  expr.var Z1_var; expr.var Z2_var;
                  expr.var Xout_var; expr.var Yout_var;
                  expr.var Zout_var])
        k_impl
      <{ pred (nlet_eq
                 [Xout_var; Yout_var; Zout_var]
                 v k) }>.
  Proof.
    repeat straightline'.
    handle_call.
    apply H10.
    rewrite H13.
    ecancel_assumption.
  Qed.

  Local Ltac ecancel_assumption ::=  repeat rewrite <- Hbounds_eq in *; ecancel_assumption_impl.

  (*Why must these instances be included?*)

  Instance spec_of_mul : spec_of (@mul field_parameters).
  Proof.
    pose proof (binop_spec bin_mul). cbv [spec_of]. eapply X.
  Defined.

  (* Instance spec_of_square : spec_of (@square field_parameters).
  Proof.
    pose proof (unop_spec un_square). cbv [spec_of]. eapply X.
  Defined. *)

  Instance spec_of_add : spec_of (@add field_parameters).
  Proof.
    pose proof (binop_spec bin_add). cbv [spec_of]. eapply X.
  Defined.

  Instance spec_of_sub : spec_of (@sub field_parameters).
  Proof.
    pose proof (binop_spec bin_sub). cbv [spec_of]. eapply X.
  Defined.

  Instance spec_of_from_list : spec_of (@from_list field_parameters).
  Proof.
    pose proof (spec_of_from_list (feval three_b)). exact X.
  Defined.

  (* Instance spec_of_scmula24 : spec_of (@scmula24 prime_field_parameters).
  Proof.
    pose proof (unop_spec un_scmula24). cbv [spec_of]. eapply X.
  Defined. *)

  Lemma relax_bounds_FElem_R : forall R x x_ptr, Lift1Prop.impl1 ((FElem (Some tight_bounds) x_ptr x * R)%sep) ((FElem (Some loose_bounds) x_ptr x * R)%sep).
  Proof.
    intros. cbv [Lift1Prop.impl1]. intros.
    destruct H, H, H, H0.
    eexists; eexists; split; [eapply H | ]. split; eauto. eapply relax_bounds_FElem. auto.
  Qed.

  Lemma relax_bounds_binop : forall R x x_ptr y y_ptr, Lift1Prop.impl1 ((FElem (Some tight_bounds) x_ptr x * FElem (Some tight_bounds) y_ptr y * R)%sep) ((FElem (Some loose_bounds) x_ptr x * FElem (Some loose_bounds) y_ptr y * R)%sep).
  Proof.
    intros. cbv [Lift1Prop.impl1]. intros. eapply sep_assoc. eapply relax_bounds_FElem_R.
    eapply sep_comm, sep_assoc. eapply relax_bounds_FElem_R. ecancel_assumption.
  Qed.

  (*tactics for applying field operations*)

  Ltac find_in_map :=
    repeat first [ erewrite map.get_put_diff; [| intros contra; discriminate] |
      eapply map.get_put_same].

  (* Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ ^ 2)%F _))) =>
    let Hsquare := (fresh "Hsquare") in pose proof compile_square as Hsquare;
    rewrite F.pow_2_r; cbv [ PrimeField.prime_field_parameters] in Hsquare;
    eapply Hsquare; clear Hsquare; shelve : compiler.

    Local Hint Extern 6 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (a24 * _)%F _))) =>
    let Hscmul := (fresh "Hscmul") in epose proof compile_scmula24 as Hscmul;
    cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in *;
    eapply Hscmul; clear Hscmul; shelve : compiler.

  Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ * _)%F _))) =>
    let Hmul := (fresh "Hmul") in pose proof compile_mul as Hmul;
    cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in Hmul;
    eapply Hmul; [| | | try (eapply relax_bounds_binop; ecancel_assumption) | | |]; clear Hmul; shelve : compiler.

    Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ - _)%F _))) =>
    let Hsub := (fresh "Hsub") in epose proof compile_sub as Hsub;
    cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in *;
    eapply Hsub; clear Hsub; shelve : compiler.

  Local Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (_ + _)%F _))) =>
    let Hadd := (fresh "Hadd") in epose proof compile_add as Hadd;
    cbv [Compilation2.field_parameters PrimeField.prime_field_parameters] in *;
    eapply Hadd; clear Hadd; shelve : compiler.

  Local Hint Extern 9 ((FElem (Some loose_bounds) _ _ ⋆ FElem (Some loose_bounds) _ _ ⋆ _)%sep _) =>
    eapply relax_bounds_binop; ecancel_assumption : compiler.

  Local Hint Extern 9 =>
  simple eapply (@compile_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((@FElem width BW word mem prime_field_parameters field_representaton
    (@None (@bounds field_parameters width BW word mem field_representaton)))));
    [ecancel_assumption | shelve] : compiler. *)


  Lemma FElem_bounds_None : forall x x_ptr R, Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x * R)%sep (FElem None x_ptr x * R)%sep.
  Proof.
    intros. cbv [Lift1Prop.impl1]; intros m Hsep.
    destruct Hsep as [m1 [m2 [Hsep1 [Hsep2 Hsep3]]]].
    do 2 eexists. split; eauto. split; eauto.
    cbv [FElem Lift1Prop.ex1] in *. sepsimpl. simpl.
    exists x0. sepsimpl; auto.
  Qed.

  Local Hint Extern 9 ((FElem None _ _ ⋆ _ )%sep _) =>
  eapply FElem_bounds_None; ecancel_assumption : compiler_cleanup_post.

  Ltac clear_pred_seps' :=   
  unfold pred_sep;
  repeat change (fun x => ?h x) with h;
  repeat match goal with
         | [ H : _ ?m |- _ ?m] =>
           eapply Proper_sep_impl1;
           [ eapply P_to_bytes | clear H m; intros H m |
            try (eapply FElem_bounds_None; ecancel_assumption);
            try (eapply FElem_bounds_None; eapply relax_bounds_FElem_R; ecancel_assumption)]
         end.

  Hint Extern 1 (pred_sep _ _ _ _ _ _) =>
         clear_pred_seps'; shelve : compiler_cleanup_post.

  Hint Extern 1 (Some tight_bounds) =>
         rewrite <- Hbounds_eq : compiler.

  Derive ladderstep_body SuchThat
         (defn! "ladderstep" ("X1", "X2", "Y1", "Y2", "Z1", "Z2", "Xout", "Yout", "Zout")
              { ladderstep_body },
           implements @ladderstep_gallina _ _ _ _ _ _ three_b
                      using [@mul field_parameters;@add field_parameters;@sub field_parameters; @from_list field_parameters])
         As ladderstep_correct.
  Proof.
    assert (1 + 1 = 2) by lia. 
    compile_setup.
    compile_step.
    compile_step.

    epose proof compile_from_list.
    eapply H7.
    5: {
      ecancel_assumption.
    }
    4: {
       eapply map.get_put_same.
    }
    2: {
      repeat compile_step.
    }
    1: {
      (*What is this goal??*)
      compile_step. repeat compile_step.
    }
    1: auto.


    compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step.
    compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
    compile_step; compile_step.
  Qed. *)

End __.
(* 
Existing Instance spec_of_ladderstep.

Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (ladderstep_gallina _ _ _ _ _ _ _) _))) =>
       simple eapply compile_ladderstep; shelve : compiler.

Import Syntax.
Local Unset Printing Coercions.
Local Set Printing Depth 70.
(* Set the printing width so that arguments are printed on 1 line.
   Otherwise the build breaks.
*)
Local Set Printing Width 140.
Redirect "Crypto.Bedrock.Group.ScalarMult.LadderStep.ladderstep_body" Print ladderstep_body. *)
