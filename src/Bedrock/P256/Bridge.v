(* Bridge: spec_of_BinOp/UnOp (FElem) → spec_of_p256_coord_mul/sqr (coord.to_bytes).
   This file needs ~6GB RAM due to loading synthesis + specs together.
   Compile outside containers: rocq c -Q src Crypto src/Bedrock/P256/Bridge.v *)

From Crypto.Bedrock.P256 Require Import Specs Synthesis.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_bridge.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.ArrayCasts.
Require Import coqutil.Map.Interface.
From Stdlib Require Import ZArith Lia.
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
Local Open Scope Z_scope.
Local Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").

Definition p256_coord_mul : Syntax.func := p256_coord_mul_body.
Definition p256_coord_sqr : Syntax.func := p256_coord_sqr_body.

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

(* Montgomery: from_mont(x*R) = x
   feval applies from_montgomerymod to the word representation.
   coord.to_bytes x encodes x*R, so from_mont(x*R) = x. *)
Lemma coord_feval : forall (x : coord),
  feval (bs2felem (coord.to_bytes x)) = x.
Proof.
  intro x.
  (* feval unfolds through the field_representation chain.
     For now we use the fact that the entire chain is a composition
     of definitional equalities + Montgomery inverse properties.
     This needs careful unfolding of Representation.eval_words,
     WordByWordMontgomery.eval_trans, etc. *)
  admit.
Admitted.

(* Canonical encoding satisfies loose_bounds.
   coord.to_bytes x = le_split 32 (F.to_Z (x*R)).
   The resulting 4 words each have unsigned values in [0, 2^64),
   and the positional evaluation is F.to_Z(x*R) < p. *)
Lemma coord_bounded : forall (x : coord),
  bounded_by loose_bounds (bs2felem (coord.to_bytes x)).
Proof.
  intro x.
  (* bounded_by loose_bounds for WBW Montgomery =
     WordByWordMontgomery.valid 64 4 m (map word.unsigned ws).
     This requires: small ws /\ 0 <= eval ws < m.
     - small: ws = partition (uweight 64) 4 (eval ws), which holds
       because the words come from le_split 32 z where z < 2^256.
     - eval < m: F.to_Z(x*R) < p by F.to_Z_range. *)
  admit.
Admitted.

(* FElem → coord.to_bytes: reverse direction.
   Uses felem_to_bytes to convert FElem to bytes, then shows
   the bytes equal coord.to_bytes r. *)
Lemma FElem_to_coord : forall (r : coord) pout (out_felem : felem),
  feval (felem_to_list out_felem) = r ->
  Lift1Prop.impl1 (FElem pout out_felem) ((coord.to_bytes r)$@pout).
Proof.
  intros r pout out_felem Heval m Hfelem.
  (* From felem_to_bytes: FElem pout out_felem → (ws2bs 8 out_felem)$@pout *)
  apply (felem_to_bytes pout out_felem) in Hfelem.
  (* Need: ws2bs 8 out_felem = coord.to_bytes r = le_split 32 (F.to_Z (r * coord.R))
     Since feval out_felem = r, by Montgomery encoding:
     eval(out_felem) = r * R mod p = F.to_Z(r * coord.R)
     And ws2bs 8 out_felem = le_split 32 (eval(out_felem)) by word↔byte roundtrip. *)
  admit.
Admitted.

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

(* ================================================================ *)
(* sqr bridge                                                        *)
(* ================================================================ *)

(* The synthesis name is "p256_coord_square" but the spec uses "p256_coord_sqr".
   We use call_body to enter the function body directly, bypassing the name. *)
Lemma p256_coord_sqr_ok : forall functions,
  Interface.map.get functions "p256_coord_sqr" = Some p256_coord_sqr ->
  spec_of_p256_coord_sqr functions.
Proof.
  intros functions Hget.
  cbv [spec_of_p256_coord_sqr].
  intros p_out p_x out x R0 t m [Hx [Hout Hlen]].
  set (xf := bs2felem (coord.to_bytes x)).
  assert (HxF : exists Rx, (FElem p_x xf * Rx)%sep m).
  { destruct Hx as [Rx Hx]. exists Rx.
    apply (coord_to_FElem x p_x). exact Hx. }
  (* Enter the function body directly via Hget, bypassing the name mismatch *)
  eapply Proper_call.
  2: {
    cbv [Semantics.call WeakestPrecondition.call WeakestPrecondition.call_body].
    eexists; split; [exact Hget|].
    (* The function body is p256_coord_sqr = b2_func square_op.
       The body WP is identical to what square_func_correct proves.
       We need to extract the body WP from the synthesis framework. *)
    admit.
  }
  intros t' m' rets [Ht' [out_felem [Heval [Hbnd Hpost]]]].
  split; [exact Ht'|].
  rewrite coord_feval in Heval.
  apply (FElem_to_coord (F.pow x 2) p_out out_felem Heval).
  exact Hpost.
Admitted.
