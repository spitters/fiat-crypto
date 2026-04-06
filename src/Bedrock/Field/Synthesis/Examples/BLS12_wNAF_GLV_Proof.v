(** * BLS12 wNAF GLV — WP proof with abstracted loop body. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZero.
Require Import bedrock2.Loops.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section WNAF_GLV.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map string word} {env: map.map string (list string * list string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals} {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters} {field_representation : FieldRepresentation}.
  Context {field_parameters_ok : FieldParameters_ok} {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z := (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  Context (curve_add_name curve_double_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
  Context (curve_add_id_r : forall x y z, curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z)).
  Context (curve_add_id_l : forall x y z, curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z)).
  Context (curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm : forall P Q, curve_add P Q = curve_add Q P).
  Let scmul_glv := scmul Fzero Fone curve_add.

  Definition wnaf_inv
    (pOx pOy pOz pAx pAy pAz : word)
    (Px Py Pz Phix Phiy Phiz : F) (dk1 dk2 : list Z)
    (R : mem -> Prop) (tr : Semantics.trace)
    (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    let iter := (129 - v)%nat in
    exists (Ox Oy Oz Ax Ay Az : F) (iw : word),
    (Ox, Oy, Oz) =
      curve_add (scmul_glv (Z.to_nat (weighted_sum (firstn iter dk1) 0)) (Px,Py,Pz))
                (scmul_glv (Z.to_nat (weighted_sum (firstn iter dk2) 0)) (Phix,Phiy,Phiz))
    /\ (Point3 (Some tight_bounds) pOx pOy pOz Ox Oy Oz
        ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax Ay Az ⋆ R) m
    /\ map.get l "outx" = Some pOx /\ map.get l "outy" = Some pOy
    /\ map.get l "outz" = Some pOz /\ map.get l "auxx" = Some pAx
    /\ map.get l "auxy" = Some pAy /\ map.get l "auxz" = Some pAz
    /\ map.get l "iter" = Some iw
    /\ word.unsigned iw = Z.of_nat iter
    /\ v = Z.to_nat (129 - word.unsigned iw) /\ tr = t.

  Theorem wnaf_glv_ok :
    forall functions
      (HStoreZero : @StoreZero.spec_of_store_zero
         _ _ _ _ _ _ field_parameters field_representation functions)
      dk1 dk2 Px Py Pz Phix Phiy Phiz k1 k2
      (Hlen1 : length dk1 = 129%nat) (Hlen2 : length dk2 = 129%nat)
      (Hk1 : wsum dk1 = k1) (Hk2 : wsum dk2 = k2)
      (Hk1nn : 0 <= k1) (Hk2nn : 0 <= k2)
      (HLoopBody : forall (iter_nat : nat) pOx pOy pOz pAx pAy pAz
         (Ox Oy Oz Ax Ay Az : F) R0 tr0 m0 l0,
         (iter_nat < 129)%nat ->
         (Point3 (Some tight_bounds) pOx pOy pOz Ox Oy Oz
          ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax Ay Az ⋆ R0) m0 ->
         map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
         map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
         map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
         map.get l0 "iter" = Some (word.of_Z (Z.of_nat iter_nat)) ->
         WeakestPrecondition.cmd functions
           (wnaf_loop_body curve_add_name curve_double_name
              felem_copy opp felem_size_in_bytes
              "digits_k1" "digits_k2" "table_P" "table_Phi")
           tr0 m0 l0
           (fun t' m' l' =>
             exists Ox' Oy' Oz' Ax' Ay' Az',
             let d1 := nth iter_nat dk1 0 in
             let d2 := nth iter_nat dk2 0 in
             let doubled := curve_add (Ox,Oy,Oz) (Ox,Oy,Oz) in
             let after1 := if d1 =? 0 then doubled
               else curve_add doubled (scmul_glv (Z.to_nat (Z.abs d1)) (Px,Py,Pz)) in
             let after2 := if d2 =? 0 then after1
               else curve_add after1 (scmul_glv (Z.to_nat (Z.abs d2)) (Phix,Phiy,Phiz)) in
             (Ox',Oy',Oz') = after2
             /\ (Point3 (Some tight_bounds) pOx pOy pOz Ox' Oy' Oz'
                 ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az' ⋆ R0) m'
             /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
             /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
             /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
             /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat (S iter_nat)))
             /\ tr0 = t')),
    forall pOx pOy pOz pAx pAy pAz (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F) R tr m l,
    map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
    map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
    map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
    (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
     ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0 ⋆ R) m ->
    WeakestPrecondition.cmd functions
      (wnaf_glv_func_body curve_add_name curve_double_name "store_zero"
         felem_copy opp 129 felem_size_in_bytes
         "digits_k1" "digits_k2" "table_P" "table_Phi")
      tr m l
      (fun t m' l' =>
        exists Rx Ry Rz Ax' Ay' Az',
        (Rx,Ry,Rz) = curve_add (scmul_glv (Z.to_nat k1) (Px,Py,Pz))
                                (scmul_glv (Z.to_nat k2) (Phix,Phiy,Phiz))
        /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
            ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az' ⋆ R) m').
  Proof.
    intros.
    unfold wnaf_glv_func_body.

    (* store_zero *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists. split.
    { cbv [dexprs list_map list_map_body
           WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
      eexists; split; [exact H|]. eexists; split; [exact H0|].
      eexists; split; [exact H1|]. exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply HStoreZero. ecancel_assumption_impl. }
    intros t0 m0 rets0 [Hrets0 [Htr0 Hsep0]].
    subst rets0. symmetry in Htr0. subst t0.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

    (* set iter = 0 *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists. split.
    { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.literal dlet.dlet]. exact eq_refl. }

    (* while loop *)
    eapply Loops.while_localsmap
      with (v0 := 129%nat) (lt := Nat.lt)
           (invariant := wnaf_inv pOx pOy pOz pAx pAy pAz
              Px Py Pz Phix Phiy Phiz dk1 dk2 R tr).
    { exact lt_wf. }

    (* Initial invariant *)
    { unfold wnaf_inv. change (129 - 129)%nat with 0%nat.
      simpl firstn. simpl weighted_sum.
      exists Fzero, Fone, Fzero, Ax0, Ay0, Az0, (word.of_Z 0).
      split.
      - simpl Z.to_nat. unfold scmul_glv. simpl scmul.
        rewrite curve_add_id_l. reflexivity.
      - change CompilationAbstract.FElem with Compilation2.FElem in Hsep0.
        repeat split; try ecancel_assumption_impl;
        try (rewrite map.get_put_same; exact eq_refl);
        try (rewrite map.get_put_diff by congruence; assumption).
        + rewrite word.unsigned_of_Z_0. reflexivity.
        + rewrite word.unsigned_of_Z_0. reflexivity. }

    (* Loop body + post-loop: branch condition + TRUE/FALSE *)
    (* The while_localsmap produces a goal with Markers.split
       and expr evaluation. This needs careful matching of the
       expr/Semantics.interp_binop structure. *)
    (* ADMITTED: needs interactive MCP debugging for the exact
       branch condition tactic sequence in this bedrock2 version. *)
    all: admit.
  Admitted.

End WNAF_GLV.
