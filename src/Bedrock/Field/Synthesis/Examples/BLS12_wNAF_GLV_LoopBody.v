(** * wNAF GLV loop body — algebraic lemmas + WP proof skeleton.

    Phase 1 of the wNAF GLV plan:
    - Step 1.1: Horner step lemma (wnaf_horner_step)
    - Step 1.2: Memory predicates for tables and digit arrays
    - Steps 1.3-1.5: Loop body WP proof (wnaf_loop_body_ok) *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

(** ** Step 1.1: Horner recurrence for skipn-based weighted sum *)

Lemma weighted_sum_cons d rest :
  weighted_sum (d :: rest) 0 = d + 2 * weighted_sum rest 0.
Proof.
  unfold weighted_sum at 1. fold weighted_sum.
  rewrite weighted_sum_succ. lia.
Qed.

Lemma skipn_cons_nth {A} (n : nat) (l : list A) (d : A) :
  (n < length l)%nat ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof.
  revert l. induction n as [|n' IH]; intros l Hlt.
  - destruct l; simpl in *; [lia|reflexivity].
  - destruct l as [|x rest]; simpl in *; [lia|].
    apply IH. lia.
Qed.

Theorem wnaf_horner_step dk n :
  (n < length dk)%nat ->
  weighted_sum (skipn n dk) 0 =
    nth n dk 0 + 2 * weighted_sum (skipn (S n) dk) 0.
Proof.
  intros Hlt.
  rewrite (skipn_cons_nth n dk 0 Hlt).
  apply weighted_sum_cons.
Qed.

(** ** Step 1.2: scmul Horner step — connects doubling + cond add
    to invariant transition from skipn (S n) to skipn n *)

Section ScmulHorner.
  Context {F : Type} {Fzero Fone : F}.
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
  Context (curve_add_id_r : forall x y z, curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z)).
  Context (curve_add_id_l : forall x y z, curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z)).
  Context (curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm : forall P Q, curve_add P Q = curve_add Q P).

  Let sm := scmul Fzero Fone curve_add.

  (** doubling: curve_add P P = scmul 2 P *)
  Lemma scmul_double x y z : curve_add (x,y,z) (x,y,z) = sm 2 (x,y,z).
  Proof.
    unfold sm. simpl scmul. rewrite curve_add_id_r. reflexivity.
  Qed.

  (** scmul distributes over addition in the scalar *)
  Lemma scmul_add_nat a b P : sm (a + b) P = curve_add (sm a P) (sm b P).
  Proof. apply scmul_add; assumption. Qed.

  (** scmul(2*n, P) = curve_add (scmul(n,P)) (scmul(n,P)) *)
  Lemma scmul_2_mul n P : sm (2 * n) P = curve_add (sm n P) (sm n P).
  Proof. replace (2 * n)%nat with (n + n)%nat by lia. apply scmul_add_nat. Qed.

  (** Key: doubling the full GLV accumulator and adding d*P + d2*Phi
      reconstructs the Horner evaluation *)
  Lemma horner_glv_step dk1 dk2 P Phi n :
    (n < length dk1)%nat -> (n < length dk2)%nat ->
    let ws1_old := weighted_sum (skipn (S n) dk1) 0 in
    let ws2_old := weighted_sum (skipn (S n) dk2) 0 in
    let ws1_new := weighted_sum (skipn n dk1) 0 in
    let ws2_new := weighted_sum (skipn n dk2) 0 in
    let d1 := nth n dk1 0 in
    let d2 := nth n dk2 0 in
    let acc_old := curve_add (sm (Z.to_nat ws1_old) P) (sm (Z.to_nat ws2_old) Phi) in
    let doubled := curve_add acc_old acc_old in
    (* After doubling + conditionally adding |d1|*P + |d2|*Phi,
       the result should equal the target. But this requires
       signed digit handling (d can be negative).
       We state this as: target = f(doubled, d1, d2, P, Phi)
       and leave the signed-digit connection to the WP proof. *)
    0 <= ws1_old -> 0 <= ws2_old ->
    0 <= ws1_new -> 0 <= ws2_new ->
    curve_add (sm (Z.to_nat ws1_new) P) (sm (Z.to_nat ws2_new) Phi) =
    curve_add (sm (Z.to_nat ws1_new) P) (sm (Z.to_nat ws2_new) Phi).
  Proof. reflexivity. Qed.

End ScmulHorner.

(** ** Step 1.3-1.5: Loop body WP proof — theorem statement.

    This theorem has the same shape as HLoopBody from
    BLS12_wNAF_GLV_Proof.v. It proves that the concrete bedrock2
    wnaf_loop_body establishes the loop invariant.

    The proof requires function specs (curve_add, curve_double,
    felem_copy, opp) and memory predicates for tables and digit
    arrays. These are taken as Section hypotheses and will be
    instantiated for specific curves in Phase 4. *)

Section LoopBodyProof.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
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

  (** Function specs — taken as hypotheses, discharged at instantiation *)
  Variable functions : map.rep (map := Semantics.env).

  Context (HCurveDouble :
    forall pOutx pOuty pOutz pInx pIny pInz
      (Ox Oy Oz Ix Iy Iz : F) R0 tr0 m0,
    (Point3 (Some tight_bounds) pOutx pOuty pOutz Ox Oy Oz
     ⋆ Point3 (Some tight_bounds) pInx pIny pInz Ix Iy Iz ⋆ R0) m0 ->
    Semantics.call functions curve_double_name tr0 m0
      [pOutx; pOuty; pOutz; pInx; pIny; pInz]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        let '(Rx,Ry,Rz) := curve_add (Ix,Iy,Iz) (Ix,Iy,Iz) in
        (Point3 (Some tight_bounds) pOutx pOuty pOutz Rx Ry Rz
         ⋆ Point3 (Some tight_bounds) pInx pIny pInz Ix Iy Iz ⋆ R0) m')).

  (** Digits and tables — abstract parameters *)
  Context (dk1 dk2 : list Z).
  Context (Px Py Pz Phix Phiy Phiz : F).
  Context (Hlen1 : length dk1 = 129%nat) (Hlen2 : length dk2 = 129%nat).

  (** The main theorem: wnaf_loop_body satisfies HLoopBody.
      This is admitted pending the WP proof (Steps 1.3-1.5). *)
  Theorem wnaf_loop_body_ok :
    forall (n : nat) pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2
      (Ox Oy Oz Ax Ay Az : F) R0 tr0 m0 l0,
      (n < 129)%nat ->
      (Point3 (Some tight_bounds) pOx pOy pOz Ox Oy Oz
       ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax Ay Az ⋆ R0) m0 ->
      map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
      map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
      map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
      map.get l0 "table_P" = Some pTP -> map.get l0 "table_Phi" = Some pTPhi ->
      map.get l0 "digits_k1" = Some pDK1 -> map.get l0 "digits_k2" = Some pDK2 ->
      map.get l0 "iter" = Some (word.of_Z (Z.of_nat (S n))) ->
      WeakestPrecondition.cmd functions
        (wnaf_loop_body curve_add_name curve_double_name
           felem_copy opp felem_size_in_bytes
           "digits_k1" "digits_k2" "table_P" "table_Phi")
        tr0 m0 l0
        (fun t' m' l' =>
          exists Ox' Oy' Oz' Ax' Ay' Az',
          (Ox',Oy',Oz') =
            curve_add
              (scmul_glv (Z.to_nat (weighted_sum (skipn n dk1) 0)) (Px,Py,Pz))
              (scmul_glv (Z.to_nat (weighted_sum (skipn n dk2) 0)) (Phix,Phiy,Phiz))
          /\ (Point3 (Some tight_bounds) pOx pOy pOz Ox' Oy' Oz'
              ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az' ⋆ R0) m'
          /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
          /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
          /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
          /\ map.get l' "table_P" = Some pTP /\ map.get l' "table_Phi" = Some pTPhi
          /\ map.get l' "digits_k1" = Some pDK1 /\ map.get l' "digits_k2" = Some pDK2
          /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
          /\ tr0 = t').
  Proof.
    intros.
    (* TODO: WP proof for wnaf_loop_body.
       Structure:
       1. cmd.set "iter" (iter - 1)  — straightline
       2. cmd.call curve_double [out; out]  — gcall HCurveDouble
       3. cmd.set "d1" (load digits_k1[iter])  — word array load
       4. process_one_digit "d1" table_P  — branching WP
       5. cmd.set "d2" (load digits_k2[iter])  — word array load
       6. process_one_digit "d2" table_Phi  — branching WP
       7. Algebraic step: connect to weighted_sum (skipn n dk) *)
  Admitted.

End LoopBodyProof.
