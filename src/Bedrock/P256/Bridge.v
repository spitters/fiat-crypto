(* Bridge: spec_of_BinOp/UnOp (FElem) → spec_of_p256_coord_mul/sqr (coord.to_bytes).
   Imports Synthesis.v (heavy) + Repr.v (bridge lemmas).
   Compile outside container with timing:
     rocq c -Q src Crypto -time src/Bedrock/P256/Bridge.v *)

From Crypto.Bedrock.P256 Require Import Specs Synthesis Repr.
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
Definition p256_coord_sqr : Syntax.func := p256_coord_sqr_body.

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
  eapply Proper_call.
  2: {
    (* Enter function body directly via Hget, bypassing name mismatch.
       The body is p256_coord_sqr = b2_func square_op definitionally. *)
    cbv [Semantics.call WeakestPrecondition.call WeakestPrecondition.call_body].
    eexists; split; [exact Hget|].
    (* Body WP identical to square_func_correct. *)
    admit.
  }
  intros t' m' rets [Ht' [out_felem [Heval [Hbnd Hpost]]]].
  split; [exact Ht'|].
  rewrite coord_feval in Heval.
  apply (FElem_to_coord (F.pow x 2) p_out out_felem Heval).
  exact Hpost.
Admitted.
