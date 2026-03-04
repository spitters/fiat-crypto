Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZero.
Require Import Crypto.Bedrock.Specs.Field.
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
  Context {F : Type} {field_parameters : Field.FieldParameters F}
          {field_parameters_ok : Field.FieldParameters_ok F}.
  
  Context {field_representation : FieldRepresentation F}
          {field_representation_ok : FieldRepresentation_ok F}
          {group_cmov : string}
          {store_zero : string}.
  Context {scalar_words : nat}.

  Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.
  (* Instance my_field_representation : FieldRepresentation F. *)
  (* Proof. *)
  (*     exact field_representation. *)
  (* Defined. *)
  Context (curve_add_name : string).

  Context (Hbounds_eq : loose_bounds = tight_bounds).
  Context (three_b : felem).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Instance spec_of_curve_add : spec_of curve_add_name := spec_of_curve_add_alt three_b.

  Instance spec_of_bignum_shift : spec_of "shift_scalar" := spec_of_shift_scalar (scalar_words:=scalar_words).

  Instance spec_of_cond_move : spec_of "group_cmov" := spec_of_group_cmov.
  Instance spec_of_cond_move_alt : spec_of "group_cmov_alt" := spec_of_group_cmov_alt.

  Instance spec_of_store_zero : spec_of "store_zero" := spec_of_store_zero.

  (* this should all be generalized: F * F * F should be a generic group etc. *)
  Context
    {n_init : Z}
      {Px_init Py_init Pz_init : F}
      {curve_add : (F * F * F) -> (F * F * F) -> (F * F * F)}
      {curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R}
      (* NB: both of these are used, and they hold in all groups,
         so we assume both rather than commutativity, since it is not necessary *)
      {curve_add_zero_l : forall P, curve_add (Fzero, Fone, Fzero) P = P}
      {curve_add_zero_r : forall P, curve_add P (Fzero, Fone, Fzero) = P}.

  Fixpoint scmul (n : nat)  : F * F * F -> F * F * F :=
    fun (P : F * F * F) =>
      let X := (fst (fst P) ) in
      let Y := (snd (fst P)) in
      let Z := (snd P) in
      match n with
      | O => (Fzero, Fone, Fzero)
      | S m => curve_add (X, Y, Z) (scmul m (X, Y, Z))
      end.

  Lemma scmul_add n m : forall x y z,
      scmul (n + m) (x, y, z) = curve_add (scmul n (x, y, z)) (scmul m (x, y, z)).
  Proof.
    intros.
    induction n.
    - simpl. rewrite curve_add_zero_l. reflexivity.
    - simpl. rewrite IHn. rewrite curve_add_assoc. reflexivity.
  Qed.

  Context
    {curve_add_spec : forall x y z a b c n m k, @CurveAdd.ladderstep_gallina _ _ _ _ _ field_parameters field_representation three_b x a y b z c = \<n, m, k\> -> (n, m, k) = curve_add (x, y, z) (a, b, c)}.
      (* {group_prop2 : forall x y z n m k iter xinit yinit zinit, *)
      (*   (n, m, k) = curve_add (x, y, z) (x, y, z) -> *)
      (*   (x, y, z) = scmul (2 ^ iter) (xinit, yinit, zinit) -> *)
      (*   (n, m, k) = scmul (2 ^ (iter + 1)) (xinit, yinit, zinit)} *)
      (*   . *)

  (* Context (group_property1 : forall x, curve_add (Fzero, Fone, Fzero) x = x) . *)

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
         * FElem None pPauxx Pauxx
         * FElem None pPauxy Pauxy
         * FElem None pPauxz Pauxz
         * Bignum.Bignum scalar_words pn n
         * scalar pc c
         * R)%sep mem
        (* these bounds should be incorporated in the Bignum.Bignum predicate, as it is in FElem *)
         /\ (Positional.eval (uweight width) scalar_words (List.map word.unsigned n)) = Z.shiftr n_init (Z.of_nat iter)
         /\ (Outx, Outy, Outz) = scmul (Z.to_nat (n_init mod (2 ^ (Z.of_nat iter))))%Z (Px_init, Py_init, Pz_init)
         /\ (Px, Py, Pz) = scmul  (2 ^ iter) (Px_init, Py_init, Pz_init)
         ;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Pxnew Pynew Pznew Outxnew Outynew Outznew Pauxxnew Pauxynew Pauxznew (* output values *)
                  : F,
           exists nnew : list word,
           exists cnew : word,
               (*n*)
            (Positional.eval (uweight width) scalar_words (List.map word.unsigned nnew)) = Z.shiftr n_init (Z.of_nat (iter + 1))
            /\ (Outxnew, Outynew, Outznew) = scmul  (Z.to_nat (n_init mod (2 ^ (Z.of_nat (iter + 1)))))%Z (Px_init, Py_init, Pz_init)
            /\ (Pxnew, Pynew, Pznew) = scmul  (2 ^ (iter + 1)) (Px_init, Py_init, Pz_init)
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

  Require Import bedrock2.NotationsCustomEntry.
  Require Import bedrock2.WeakestPrecondition.
  Import Syntax BinInt String List.ListNotations.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
             

  Definition loop_body_func : bedrock2.Syntax.func :=
    ("loop_body", (["px"; "py"; "pz"; "outx"; "outy"; "outz"; "pauxx"; "pauxy"; "pauxz"; "pn"; "pc"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] ("store_zero") [expr.var ("pauxx"); expr.var ("pauxy"); expr.var ("pauxz")]);
      coq:(cmd.call [] ("shift_scalar") [expr.var ("pc"); expr.var ("pn")]);
      coq:(cmd.call [] ("group_cmov_alt") [expr.var ("pauxx"); expr.var ("pauxy"); expr.var ("pauxz"); expr.var ("pauxx"); expr.var ("pauxy"); expr.var ("pauxz"); expr.var ("px"); expr.var ("py"); expr.var ("pz"); expr.var("pc")]);
      coq:(cmd.call [] (curve_add_name)
             [expr.var ("outx");
              expr.var ("pauxx");
              expr.var ("outy");
              expr.var ("pauxy");
              expr.var ("outz");
              expr.var ("pauxz");
              expr.var ("outx");
              expr.var ("outy");
              expr.var ("outz")]);
      coq:(cmd.call [] (curve_add_name)
             [expr.var ("px");
              expr.var ("px");
              expr.var ("py");
              expr.var ("py");
              expr.var ("pz");
              expr.var ("pz");
              expr.var ("px");
              expr.var ("py");
              expr.var ("pz")])
    ))).

    (* From bedrock2 Require Import ToCString Bytedump. *)
    (* Definition c_mod := (c_module (loop_body_func :: nil)). *)
    (* Eval native_compute in c_mod. *)

    (* Print c_mod. *)

  Ltac straightline' :=
    match goal with
    | |- felem_size_in_bytes mod _ = 0 => eapply felem_size_in_bytes_mod
    | |- ?a mod ?a = 0 => eapply Z_mod_same_full
    (* | _ => update_mem *)
    | _ => straightline
    | l := _ : map.rep |- _ => subst l
    | l := _ : list word.rep |- _ => subst l
    | |- Some _ = Some _ => try reflexivity
    | |- exists _, _ => eexists
    | |- _ /\ _ => split
    | |- map.get _ _ = _ => repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same
    end.

    Lemma loop_body_ok : program_logic_goal_for_function! loop_body_func.
    Proof.
      repeat straightline'.
      straightline_call.
      ecancel_assumption.
      clear dependent mem0.

      repeat straightline'.

      straightline_call.
      ecancel_assumption.
      clear dependent a0.

      repeat straightline'.

      straightline_call.
      sepsimpl.
      ecancel_assumption.
      ecancel_assumption.
      ecancel_assumption.
      ecancel_assumption.

      cbv [ZRange.is_bounded_by_bool]. simpl.
      {
        rewrite <- H10; lia.
      }

      repeat straightline'.
      clear dependent a2.

      straightline_call.
      sepsimpl.
      ecancel_assumption.
      ecancel_assumption.
      ecancel_assumption.
      clear dependent a0.

      repeat straightline'.
      straightline_call.
      sepsimpl.
      ecancel_assumption.
      ecancel_assumption.
      ecancel_assumption.
      clear dependent a2.

      repeat straightline'.

      rewrite <- H9.
      rewrite Nat2Z.inj_add.
      rewrite <- Z.shiftr_shiftr.
      rewrite Z.shiftr_div_pow2.
      rewrite Z.pow_1_r.
      f_equal.

      assumption.
      lia. lia.


      3: ecancel_assumption.

      1: {
        rewrite Modulo.Z.mod_pow_r_split with (e1:=Z.of_nat iter) by lia.
        destruct (word.unsigned x =? 1) eqn:E.
        - subst.
          rewrite Z2Nat.inj_add.
          rewrite scmul_add.
          (* rewrite !Z.pow_1_r. *)
          rewrite Nat2Z.inj_add.
          rewrite Z.add_simpl_l.
          rewrite !Z.pow_1_r.
          rewrite Z.shiftr_div_pow2 in *.
          rewrite H5 in *.

          rewrite H10.
          assert (word.unsigned x = 1) by lia.
          rewrite H4.
          rewrite Z.mul_1_r.
          rewrite <- !H6.
          rewrite Z2Nat.inj_pow.
          rewrite Nat2Z.id.
          replace (Z.to_nat 2) with (2%nat) by reflexivity.
          rewrite <- H7.
          apply curve_add_spec.
          assumption.
          all: lia.
        -
          rewrite Z2Nat.inj_add.
          rewrite scmul_add.
          (* rewrite !Z.pow_1_r. *)
          rewrite Nat2Z.inj_add.
          rewrite Z.add_simpl_l.
          rewrite !Z.pow_1_r.
          rewrite Z.shiftr_div_pow2 in *.
          rewrite H5 in *.

          rewrite H10.
          assert (word.unsigned x = 0) by lia.
          rewrite H4.
          rewrite Z.mul_0_r.
          rewrite <- !H6.
          replace (Z.to_nat 0) with (0%nat) by reflexivity.
          simpl.
          apply curve_add_spec.
          subst x1 x2 x3.
          assumption.
          all: lia.
      }

      rewrite Nat.pow_add_r.
      simpl.
      replace (2 ^ iter * 2)%nat with (2 ^ iter + 2 ^ iter)%nat by lia.
      rewrite scmul_add.
      rewrite <- H7.
      apply curve_add_spec. assumption.
    Qed.

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
