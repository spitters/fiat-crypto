(* Bridge: spec_of_BinOp/UnOp (FElem) → spec_of_p256_coord_mul/sqr (coord.to_bytes).
   This file needs ~8GB RAM due to loading synthesis + specs together.
   Run outside containers: rocq c -Q src Crypto src/Bedrock/P256/Bridge.v *)

From Crypto.Bedrock.P256 Require Import Specs Synthesis.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_bridge.
Require Import Crypto.Bedrock.Specs.Field.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Map.Interface.
Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.

Import Specs.NotationsCustomEntry Specs.coord.
Import bedrock2.Syntax.
Import LittleEndianList PrimeFieldTheorems.
Import coqutil.Byte Lists.List.
Import ProgramLogic WeakestPrecondition ProgramLogic.Coercions.
Import Word.Interface Separation SeparationLogic.
Import BasicC64Semantics.
Import WeakestPreconditionProperties.
Import OfListWord.

Local Open Scope string_scope.
Import bedrock2.NotationsCustomEntry.
Local Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").

Definition p256_coord_mul : Syntax.func := p256_coord_mul_body.

(* ================================================================ *)
(* Representation bridge: coord.to_bytes ↔ FElem                    *)
(* ================================================================ *)

Lemma coord_length_felem (x : coord) :
  length (coord.to_bytes x) = BinInt.Z.to_nat felem_size_in_bytes.
Proof. rewrite coord.length_coord. vm_compute. reflexivity. Qed.

(* coord.to_bytes → FElem: direct application of felem_from_bytes *)
Lemma coord_to_FElem (x : coord) px :
  Lift1Prop.impl1 ((coord.to_bytes x)$@px) (FElem px (bs2felem (coord.to_bytes x))).
Proof.
  intros m H.
  apply (felem_from_bytes px (coord.to_bytes x) (coord_length_felem x)).
  exact H.
Qed.

(* FElem → coord.to_bytes: requires ws2bs out_felem = coord.to_bytes r *)
Axiom FElem_to_coord : forall (r : coord) pout (out_felem : felem),
  feval (felem_to_list out_felem) = r ->
  Lift1Prop.impl1 (FElem pout out_felem) ((coord.to_bytes r)$@pout).

(* Canonical encoding ⊂ loose_bounds *)
Axiom coord_bounded : forall (x : coord),
  bounded_by loose_bounds (bs2felem (coord.to_bytes x)).

(* Montgomery: from_mont(x*R) = x *)
Axiom coord_feval : forall (x : coord),
  feval (bs2felem (coord.to_bytes x)) = x.

(* ================================================================ *)
(* mul bridge                                                        *)
(* ================================================================ *)

Lemma p256_coord_mul_ok : forall functions,
  Interface.map.get functions "p256_coord_mul" = Some p256_coord_mul ->
  spec_of_p256_coord_mul functions.
Proof.
  intros functions Hget.
  pose proof (p256_mul_synthesis_ok functions Hget) as Hmul.
  cbv [spec_of_p256_coord_mul spec_of_BinOp bin_mul binop_spec] in *.
  intros p_out p_x p_y out x y R0 t m [Hx [Hy [Hout Hlen]]].
  set (xf := bs2felem (coord.to_bytes x)).
  set (yf := bs2felem (coord.to_bytes y)).
  assert (HxF : exists Rx, (FElem p_x xf * Rx)%sep m).
  { destruct Hx as [Rx Hx]. exists Rx.
    apply (coord_to_FElem x p_x). exact Hx. }
  assert (HyF : exists Ry, (FElem p_y yf * Ry)%sep m).
  { destruct Hy as [Ry Hy]. exists Ry.
    apply (coord_to_FElem y p_y). exact Hy. }
  eapply Proper_call.
  2: {
    eapply (Hmul p_out p_x p_y xf yf out R0 t m).
    refine (conj (coord_bounded x) (conj (coord_bounded y)
      (conj _ (conj HxF (conj HyF Hout))))).
    rewrite coord.length_coord in Hlen. exact Hlen.
  }
  intros t' m' rets [Ht' [out_felem [Heval [Hbnd Hpost]]]].
  split; [exact Ht'|].
  rewrite coord_feval, coord_feval in Heval.
  apply (FElem_to_coord (F.mul x y) p_out out_felem Heval).
  exact Hpost.
Qed.
