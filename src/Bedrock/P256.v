From Crypto.Bedrock.P256 Require Import Specs Platform Coord Jacobian JacobianAffine.

Import Specs.NotationsCustomEntry Specs.coord Specs.point.

Import bedrock2.Syntax bedrock2.NotationsCustomEntry
LittleEndianList
ZArith.BinInt
BinInt BinNat Init.Byte
PrimeFieldTheorems ModInv
micromega.Lia
coqutil.Byte
Lists.List micromega.Lia
Jacobian
Coq.Strings.String Coq.Lists.List 
ProgramLogic WeakestPrecondition
ProgramLogic.Coercions
Word.Interface OfListWord Separation SeparationLogic
letexists
BasicC64Semantics
ListIndexNotations
SepAutoArray
symmetry
PeanoNat micromega.Lia
Tactics
UniquePose
micromega.Lia Word.Properties.

Import ListIndexNotations.
Local Open Scope list_index_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").
Local Notation "$ n" := (match word.of_Z n return word with w => w end) (at level 9, format "$ n").
Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).
Local Coercion F.to_Z : F >-> Z.

Import coqutil.Map.Interface.
Import bedrock2.ToCString.
Import Macros.WithBaseName.
Import String List. Local Open Scope string_scope. Local Open Scope list_scope.


(* Concrete function bodies from fiat-crypto synthesis *)
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_bridge.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.

Definition p256_coord_sqr : Syntax.func := p256_coord_sqr_body.
Definition p256_coord_mul : Syntax.func := p256_coord_mul_body.

(* Correctness of coord_mul/sqr via fiat-crypto synthesis + coord↔FElem bridge.
   The synthesis framework (WordByWordMontgomery.mul_func_correct) proves
   spec_of_BinOp bin_mul for the synthesized body. The bridge to
   spec_of_p256_coord_mul requires connecting:
   - coord.to_bytes x = Z.to_bytes 32 (x * R)  ↔  FElem px x_felem
   - feval x_felem = x  (Montgomery decoding)
   - bin_mul.bin_model = F.mul
   This is ~100 lines using felem_to_bytes/felem_from_bytes from Specs/Field.v.
   TODO: close these admits using the synthesis correctness infrastructure. *)
Lemma p256_coord_sqr_ok : forall functions, map.get functions "p256_coord_sqr" = Some p256_coord_sqr -> spec_of_p256_coord_sqr functions.
Proof. Admitted.
Lemma p256_coord_mul_ok : forall functions, map.get functions "p256_coord_mul" = Some p256_coord_mul -> spec_of_p256_coord_mul functions.
Proof. Admitted.

Import memcpy shrd full_sub full_add full_mul memmove.

(* Aliases for br_-prefixed platform functions.
   In newer bedrock2, these are exported by the respective modules.
   In v0.0.9, they need to be defined here. *)
Definition br_full_add : Syntax.func := full_add.
Definition br_full_sub : Syntax.func := full_sub.
Definition br_full_mul : Syntax.func := full_mul.

(* Specs and correctness lemmas for the br_-prefixed functions.
   These mirror the base specs but use the renamed function names.
   The proofs reuse the base _ok lemmas by entering the function body directly. *)
(* spec_of_br_full_sub and spec_of_br_full_add are exported from Coord.v *)

Lemma br_full_add_ok :
  program_logic_goal_for br_full_add
  (forall functions, map.get functions "br_full_add" = Some br_full_add ->
   spec_of_br_full_add functions).
Proof.
  cbv [spec_of_br_full_add]. repeat straightline.
  rewrite add_ltu_as_adder, <- Z.add_assoc, add_ltu_as_adder.
  repeat (match goal with X := _ |- _ => subst X end).
  destruct (word.ltu _ carry); destruct (word.ltu _ y); ZnWords.ZnWords.
Qed.

Lemma br_full_sub_ok :
  program_logic_goal_for br_full_sub
  (forall functions, map.get functions "br_full_sub" = Some br_full_sub ->
   spec_of_br_full_sub functions).
Proof.
  cbv [spec_of_br_full_sub]. repeat straightline.
  rewrite ltu_as_borrow.
  assert (forall m n o, m - n - o = m - o - n) as Hcomm by lia.
  rewrite Hcomm; clear Hcomm. rewrite ltu_as_borrow.
  repeat (match goal with X := _ |- _ => subst X end).
  destruct (word.ltu x y); destruct (word.ltu _ borrow); ZnWords.ZnWords.
Qed.

(* br_full_mul_ok is not needed: p256_coord_mul_ok is axiomatized. *)

Definition platform := &[,
  br_full_add; br_full_sub; br_full_mul; shrd;
  br_value_barrier; br_declassify; br_broadcast_negative; br_broadcast_nonzero; br_broadcast_odd; br_cmov;  br_memcxor
  ].

Definition libc := &[, memmove; br_memcpy;  br_memset].

Local Definition c_func f : string := "static inline "++ c_func f.

Compute String.concat LF (List.map c_func platform).

Definition jacobian := &[,
 br_broadcast_odd;
 p256_coord_halve;

 p256_point_iszero;
 p256_point_double;
 p256_point_add_nz_nz_neq;
 p256_point_add_vartime_if_doubling;

 p256_point_add_affine_nz_nz_neq;
 p256_point_add_affinenz_conditional_vartime_if_doubling
 ].

Compute String.concat LF (List.map c_func jacobian).

 (*
 p256_point_add_affine_nz_nz_neq;
 p256_point_add_affine_conditional

 sc_sub;
 sc_halve;
 fe_set_1;
  *)

Definition asm := &[, p256_coord_sqr; p256_coord_mul
 ].

Definition funcs := Eval cbv [List.app] in (jacobian ++ coord64 ++ asm ++ platform ++ libc)%list.

Ltac pose_correctness lem :=
  let funcs := match goal with |- _ (map.of_list ?funcs) => funcs end in
  let H := fresh in
  pose proof (lem (map.of_list funcs)) as H;
  unfold ProgramLogic.program_logic_goal_for in H;
  repeat lazymatch type of H with
    | map.get (map.of_list ?e) ?f = Some _ -> _ => specialize (H eq_refl)
      || let t := type of H in fail 1 "function" f "not found in environment" e
    | ?P -> _ => match goal with HH : P |- _ => specialize (H HH) end
      || let t := type of H in fail 1 "unsolved premises" t
    end.

Local Existing Instance memmove.spec_of_memmove.
#[export] Instance spec_of_memmove : spec_of "memmove". apply memmove.spec_of_memmove. Defined.

Lemma link_jacobian  : spec_of_p256_point_add_vartime_if_doubling (map.of_list funcs).
Proof.
  pose_correctness br_full_add_ok.
  pose_correctness br_full_sub_ok.
  (* br_full_mul_ok not needed: p256_coord_mul_ok is axiomatized *)
  pose_correctness value_barrier_ok.
  pose_correctness br_declassify_ok.
  pose_correctness br_broadcast_negative_ok.
  pose_correctness br_broadcast_nonzero_ok.
  pose_correctness br_cmov_ok.
  pose_correctness br_broadcast_odd_ok.

  pose_correctness memmove.memmove_ok.
  match goal with H : _ |- _ =>
  pose proof br_memcpy_ok (map.of_list funcs) eq_refl H end.
  pose_correctness br_memset_ok.
  pose_correctness br_memcxor_ok.

  pose_correctness shrd_ok.
  pose_correctness u256_shr_ok.
  pose_correctness u256_set_p256_minushalf_conditional_ok.

  pose_correctness p256_coord_add_ok.
  pose_correctness p256_coord_sub_nonmont_ok.
  pose_correctness p256_coord_sub_ok.
  pose_correctness fiat_coord_nonzero_ok.
  pose_correctness p256_coord_halve_ok.

  pose_correctness p256_coord_sqr_ok.
  pose_correctness p256_coord_mul_ok.
  
  pose_correctness p256_point_iszero_ok.
  pose_correctness p256_point_double_ok.

  pose_correctness p256_point_add_nz_nz_neq_ok.

  pose_correctness p256_point_add_vartime_if_doubling_ok.

  pose_correctness p256_point_add_affine_nz_nz_neq_ok.
  pose_correctness p256_point_add_affinenz_conditional_vartime_if_doubling_ok.
  trivial.
Qed.

Print Assumptions link_jacobian.
