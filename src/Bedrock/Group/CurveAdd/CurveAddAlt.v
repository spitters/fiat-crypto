Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZeroGSpec.
Require Import Crypto.Bedrock.Specs.AbstractField.
(* Require Import Crypto.Bedrock.Specs.PrimeField. *)
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAdd.
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
          {curve_add_alt : string}.

  Hint Resolve relax_bounds : compiler.
  Instance my_field_representation : FieldRepresentation.
  Proof.
      exact field_representation.
  Defined.

  Context (three_b : felem).

  Instance spec_of_felem_copy : spec_of "felem_copy".
  Proof.
     pose proof spec_of_felem_copy. eapply X.
   Defined.

   Instance spec_of_curve_add : spec_of "curve_add".
   Proof.
      pose proof spec_of_ladderstep. specialize (X three_b). exact X.
   Defined.

  Instance spec_of_curve_add_alt : spec_of curve_add_alt :=
  fnspec! curve_add_alt
        (pX1 pX2 pY1 pY2 pZ1 pZ2 pXout pYout pZout : word)
        / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) R1 R2 Rout,
  { requires tr mem :=
      (FElem (Some tight_bounds) pX1 X1
       * FElem (Some tight_bounds) pY1 Y1
       * FElem (Some tight_bounds) pZ1 Z1
       * R1)%sep mem /\
      (FElem (Some tight_bounds) pX2 X2
       * FElem (Some tight_bounds) pY2 Y2
       * FElem (Some tight_bounds) pZ2 Z2
       * R2)%sep mem /\
       (FElem (Some tight_bounds) pXout Xoutold
       * FElem (Some tight_bounds) pYout Youtold
       * FElem (Some tight_bounds) pZout Zoutold * Rout)%sep mem;
    ensures tr' mem' :=
         exists Xout Yout Zout (* output values *)
                : F ,
                (@ladderstep_gallina _ _ _ _ _ _ three_b X1 X2 Y1 Y2 Z1 Z2
         = \<Xout, Yout, Zout\>)
        /\
        (* (FElem (Some tight_bounds) pX1 X1
              * FElem (Some tight_bounds) pY1 Y1
              * FElem (Some tight_bounds) pZ1 Z1 * R1)%sep mem' /\
           (FElem (Some tight_bounds) pX2 X2
              * FElem (Some tight_bounds) pY2 Y2
              * FElem (Some tight_bounds) pZ2 Z2 * R2)%sep mem' /\ *)
           (FElem (Some tight_bounds) pXout Xout
              * FElem (Some tight_bounds) pYout Yout
              * FElem (Some tight_bounds) pZout Zout * Rout)%sep mem'}.

   Require Import bedrock2.NotationsCustomEntry.
   Require Import bedrock2.WeakestPrecondition.
   Import Syntax BinInt String List.ListNotations.
   Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

   Definition curve_add_alt_func : bedrock2.Syntax.func :=
   ("curve_add_alt", (["px1"; "px2"; "py1"; "py2"; "pz1"; "pz2"; "outx"; "outy"; "outz"], []:list String.string, bedrock_func_body:(
      stackalloc 48 as px1a;
      stackalloc 48 as py1a;
      stackalloc 48 as pz1a;
      stackalloc 48 as px2a;
      stackalloc 48 as py2a;
      stackalloc 48 as pz2a;
      coq:(cmd.call [] ("felem_copy") [expr.var ("px1a"); expr.var ("px1")]);
      coq:(cmd.call [] ("felem_copy") [expr.var ("px2a"); expr.var ("px2")]);
      coq:(cmd.call [] ("felem_copy") [expr.var ("py1a"); expr.var ("py1")]);
      coq:(cmd.call [] ("felem_copy") [expr.var ("py2a"); expr.var ("py2")]);
      coq:(cmd.call [] ("felem_copy") [expr.var ("pz1a"); expr.var ("pz1")]);
      coq:(cmd.call [] ("felem_copy") [expr.var ("pz2a"); expr.var ("pz2")]);
      coq:(cmd.call [] ("curve_add") [expr.var ("px1"); expr.var ("px2"); expr.var ("py1"); expr.var ("py2"); expr.var ("pz1"); expr.var ("pz2"); expr.var ("outx"); expr.var ("outy"); expr.var ("outz")])
   ))).

    From bedrock2 Require Import ToCString Bytedump.
    Definition c_mod := (c_module (curve_add_alt_func :: nil)).
    Eval native_compute in c_mod.

    Print c_mod.

   Ltac solve_locals7 l5 l4 l3 l2 l1 l0 l :=
      subst l5 l4 l3 l2 l1 l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

   Ltac solve_locals6 l4 l3 l2 l1 l0 l :=
      subst l4 l3 l2 l1 l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.


   Lemma curve_add_alt_ok : program_logic_goal_for_function! curve_add_alt_func.
   Proof.
      enter curve_add_alt_func.
      repeat straightline.

      remember ((FElem (Some tight_bounds) pX1 X1 ⋆ FElem (Some tight_bounds) pY1 Y1
      ⋆ FElem (Some tight_bounds) pZ1 Z1 ⋆ R1))%sep as P1.

      remember ((FElem (Some tight_bounds) pX2 X2 ⋆ FElem (Some tight_bounds) pY2 Y2
      ⋆ FElem (Some tight_bounds) pZ2 Z2 ⋆ R2))%sep as P2.

      remember ((FElem (Some tight_bounds) pXout Xoutold
      ⋆ FElem (Some tight_bounds) pYout Youtold
      ⋆ FElem (Some tight_bounds) pZout Zoutold ⋆ Rout))%sep as P3.

      assert ( (fun m => (P1 m /\ P2 m /\ P3 m)) mem0) by auto.
      clear H8 H7 H6.

      simpl.
      assert (curve_add_alt =? curve_add_alt = true)%string.
      {
         eapply String.eqb_eq. auto.
      }
      rewrite H6.
      eexists; split; [cbv [map.of_list_zip]; simpl; eauto| ].

      remember  (fun m : mem => P1 m /\ P2 m /\ P3 m) as eyy.

      repeat straightline.

      split.
      {
         admit.
      }

      repeat straightline.

      split.
      {
         admit.
      }

      repeat straightline.
      split.
      {
         admit.
      }

      repeat straightline. split.
      {
         admit.
      }

      repeat straightline.

      split.
      {
         admit.
      }

      repeat straightline. split.
      {
         admit.
      }

      
      repeat straightline.

      eexists. split.
      {
         repeat straightline. eexists. split; [solve_locals6 l4 l3 l2 l1 l0 l| ].
         repeat straightline. eexists. split; [solve_locals6 l4 l3 l2 l1 l0 l| ].
         repeat straightline.
      }

      repeat straightline. clear H30 H26 H22 H18 H14.
      subst eyy P1 P2 P3.
      repeat straightline.

      eassert (Htemp : exists f, array ptsto (word.of_Z 1) a stack17 = AbstractField.FElem a f) by admit.
      destruct Htemp. rewrite H65 in *.

      eassert (Htemp : exists f, array ptsto (word.of_Z 1) a0 stack18 = AbstractField.FElem a f) by admit.
      destruct Htemp. rewrite H66 in *.

      eassert (Htemp : exists f, array ptsto (word.of_Z 1) a1 stack19 = AbstractField.FElem a f) by admit.
      destruct Htemp. rewrite H67 in *.

      eassert (Htemp : exists f, array ptsto (word.of_Z 1) a2 stack20 = AbstractField.FElem a f) by admit.
      destruct Htemp. rewrite H68 in *.

      eassert (Htemp : exists f, array ptsto (word.of_Z 1) a3 stack21 = AbstractField.FElem a f) by admit.
      destruct Htemp. rewrite H69 in *.

      eassert (Htemp : exists f, array ptsto (word.of_Z 1) a4 stack22 = AbstractField.FElem a f) by admit.
      destruct Htemp. rewrite H70 in *.

      eassert (Htemp : exists f, FElem (Some tight_bounds) pX1 X1 = AbstractField.FElem pX1 f /\ bounded_by tight_bounds f /\ feval f = X1) by admit.
      destruct Htemp, H71, H72. rewrite H71 in *.

      eassert (Htemp : exists f, FElem (Some tight_bounds) pX2 X2 = AbstractField.FElem pX2 f /\ bounded_by tight_bounds f /\ feval f = X2) by admit.
      destruct Htemp, H73, H74. rewrite H73 in *.

      eassert (Htemp : exists f, FElem (Some tight_bounds) pY1 Y1 = AbstractField.FElem pY1 f /\ bounded_by tight_bounds f /\ feval f = Y1) by admit.
      destruct Htemp, H75, H76. rewrite H75 in *.

      eassert (Htemp : exists f, FElem (Some tight_bounds) pY2 Y2 = AbstractField.FElem pY2 f /\ bounded_by tight_bounds f /\ feval f = Y2) by admit.
      destruct Htemp, H77, H78. rewrite H77 in *.

      eassert (Htemp : exists f, FElem (Some tight_bounds) pZ1 Z1 = AbstractField.FElem pZ1 f /\ bounded_by tight_bounds f /\ feval f = Z1) by admit.
      destruct Htemp, H79, H80. rewrite H79 in *.






      eapply Proper_call.
      2: {
         pose proof H. cbv [spec_of_felem_copy AbstractField.spec_of_felem_copy] in H82.
         assert (felem_copy = "felem_copy") by admit.
         rewrite H83 in H82.
         eapply H82. split; cbv [my_field_representation].
         1: {
            cbv [my_field_representation] in *.
             ecancel_assumption.
         }
         cbv [my_field_representation] in *. ecancel_assumption.
      }

       clear H63 H61 H59 H57  H55 H51  H49 H47 H45 H43 H39 H37 H35 H33 H30.

      cbv [pointwise_relation Basics.impl]. intros.
      destruct H30.

      eexists. split.
      {
         subst 
      }

             eassert ((AbstractField.FElem pX1 x5 * AbstractField.FElem a x0 * _)%sep mem0).
             {
                cbv [my_field_representation] in *.
                ecancel_assumption.
             }
             eapply H85.
             
             ecancel_assumption.
             Set Printing All.

             cbv [my_field_representation] in *.
             ecancel_assumption.
            rewrite H68.


            Set Printing All.
            Lemma forall p x

         }
         1: ecancel_assumption.
         pose proof H9.
         
         ecancel_assumption.
         ecancel_assumption.
      }

      repeat straightline.



      repeat straightline.
      split; [admit| ].
      compile_step.




End __.