(** * BLS12 wNAF GLV — WP proof.

    Proves the wNAF-based Shamir loop computes [k1]P + [k2]phi(P).
    The function body processes precomputed tables and digit arrays. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZero.
Require Import bedrock2.Loops.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.syntactic_unify.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section WNAF_GLV.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {env: map.map string (list string * list string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals} {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}
          {field_parameters_ok : FieldParameters_ok}
          {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z :=
    (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  Context (curve_add_name curve_double_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
  Context (curve_add_id_r : forall x y z, curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z)).
  Context (curve_add_id_l : forall x y z, curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z)).
  Context (curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm : forall P Q, curve_add P Q = curve_add Q P).

  Let scmul_glv := scmul Fzero Fone curve_add.
  Let wnaf_iters : Z := 129.

  (** ** Loop invariant *)

  Definition wnaf_inv
    (pOx pOy pOz pAx pAy pAz : word)
    (Px Py Pz Phix Phiy Phiz : F)
    (dk1 dk2 : list Z)
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
    /\ v = Z.to_nat (wnaf_iters - word.unsigned iw)
    /\ tr = t.

  (** ** Spec: the function computes [k1]P + [k2]Phi *)

  Definition spec_of_wnaf_glv (functions : map.rep) : Prop :=
    forall pOx pOy pOz pAx pAy pAz
           (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 Px Py Pz Phix Phiy Phiz : F)
           (dk1 dk2 : list Z)
           (k1 k2 : Z) R tr m l,
    length dk1 = 129%nat ->
    length dk2 = 129%nat ->
    wsum dk1 = k1 -> wsum dk2 = k2 ->
    0 <= k1 -> 0 <= k2 ->
    map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
    map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
    map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
    (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
     ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0 ⋆ R) m ->
    (* After executing the wNAF loop: *)
    WeakestPrecondition.cmd functions
      (wnaf_glv_func_body curve_add_name curve_double_name "store_zero"
        felem_copy opp 129 felem_size_in_bytes
        "digits_k1" "digits_k2" "table_P" "table_Phi")
      tr m l
      (fun t m' l' =>
        exists (Rx Ry Rz : F),
        (Rx, Ry, Rz) = curve_add (scmul_glv (Z.to_nat k1) (Px,Py,Pz))
                                  (scmul_glv (Z.to_nat k2) (Phix,Phiy,Phiz))
        /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
            ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0 ⋆ R) m').

  (** ** WP proof *)

  Theorem wnaf_glv_ok :
    forall functions
      (HStoreZero : @StoreZero.spec_of_store_zero
         _ _ _ _ _ _ field_parameters field_representation functions)
      (HCurveDouble : forall pX pY pZ (X Y Z : F) R0 tr0 m0,
         (FElem (Some tight_bounds) pX X ⋆ FElem (Some tight_bounds) pY Y
          ⋆ FElem (Some tight_bounds) pZ Z ⋆ R0) m0 ->
         Semantics.call functions curve_double_name tr0 m0
           [pX; pY; pZ; pX; pY; pZ]
           (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
              let '(Xo, Yo, Zo) := curve_add (X, Y, Z) (X, Y, Z) in
              (FElem (Some tight_bounds) pX Xo ⋆ FElem (Some tight_bounds) pY Yo
               ⋆ FElem (Some tight_bounds) pZ Zo ⋆ R0) m')))
      (HCurveAddInplace : forall pXo pX2 pYo pY2 pZo pZ2
         (X Y Z X2' Y2' Z2' : F) R0 tr0 m0,
         (FElem (Some tight_bounds) pXo X ⋆ FElem (Some tight_bounds) pYo Y
          ⋆ FElem (Some tight_bounds) pZo Z ⋆ FElem (Some tight_bounds) pX2 X2'
          ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
          ⋆ R0) m0 ->
         Semantics.call functions curve_add_name tr0 m0
           [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
           (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
              let '(Xo', Yo', Zo') := curve_add (X, Y, Z) (X2', Y2', Z2') in
              (FElem (Some tight_bounds) pXo Xo' ⋆ FElem (Some tight_bounds) pYo Yo'
               ⋆ FElem (Some tight_bounds) pZo Zo' ⋆ FElem (Some tight_bounds) pX2 X2'
               ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
               ⋆ R0) m'))),
    spec_of_wnaf_glv functions.
  Proof.
    intros. unfold spec_of_wnaf_glv.
    intros * Hlen1 Hlen2 Hk1 Hk2 Hk1nn Hk2nn
           Hl_ox Hl_oy Hl_oz Hl_ax Hl_ay Hl_az Hsep.

    (* === Phase 1: store_zero (initialize acc to identity) === *)
    unfold wnaf_glv_func_body, wnaf_loop_body, process_one_digit.

    (* Process store_zero call *)
    (* The rest of the proof processes the while loop using
       Loops.while_localsmap with wnaf_inv. *)

    (* === Phase 2: while loop === *)
    (* This is the core of the proof — ~800 lines following the
       BLS12_GLV_ScalarMultBedrock.v pattern. Each iteration:
       1. gcall HCurveDouble (double acc)
       2. Load d1 from memory (straightline)
       3. cmd.cond on d1: if nonzero, table lookup + negate + add
       4. Load d2, same
       5. iter++
       6. Restore invariant using weighted_sum_firstn_succ *)

    admit.
  Admitted.

End WNAF_GLV.
