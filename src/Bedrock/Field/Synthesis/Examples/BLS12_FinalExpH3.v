(** * BLS12-381 Final Exponentiation: H3 Store Helper
    Encapsulates the expensive proof that 20 word stores write the h3
    exponent into a scalar array. Compiled once, imported by BLS12_FinalExp.v.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_Pairing.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section H3Store.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  (* The 20 little-endian u64 limbs of h3 = (p^4 - p^2 + 1)/r *)
  Definition h3_limbs : list word :=
    [ word.of_Z 0xe516c3f438e3ba79; word.of_Z 0xfa9912aae208ccf1;
      word.of_Z 0x905ce937335d5b68; word.of_Z 0xc71a2629b0dea236;
      word.of_Z 0x83774940996754c8; word.of_Z 0x21d160aeb6a1e799;
      word.of_Z 0x2ed0b283ed237db4; word.of_Z 0x915c97f36c6f1821;
      word.of_Z 0x67f17fcbde783765; word.of_Z 0x2378b9039096d1b7;
      word.of_Z 0x7988f8761bdc51dc; word.of_Z 0x2076995003fc77a1;
      word.of_Z 0x827eca0ba621315b; word.of_Z 0xe5a72bce8d63cb9f;
      word.of_Z 0xf68f7764c28b6f8a; word.of_Z 0x2f230063cf081517;
      word.of_Z 0x94506632528d6a9a; word.of_Z 0xd3cde88eeb996ca3;
      word.of_Z 0xc0bd38c3195c899e; word.of_Z 0x000f686b3d807d01 ].

  (* The 20-store command block extracted from the final_exp function body *)
  Definition h3_store_cmd : Syntax.cmd.cmd :=
    BLS12_Pairing.cmd_seq_list [
      cmd.store Syntax.access_size.word
        (expr.var "h3") (expr.literal 0xe516c3f438e3ba79);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 8))
        (expr.literal 0xfa9912aae208ccf1);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 16))
        (expr.literal 0x905ce937335d5b68);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 24))
        (expr.literal 0xc71a2629b0dea236);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 32))
        (expr.literal 0x83774940996754c8);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 40))
        (expr.literal 0x21d160aeb6a1e799);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 48))
        (expr.literal 0x2ed0b283ed237db4);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 56))
        (expr.literal 0x915c97f36c6f1821);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 64))
        (expr.literal 0x67f17fcbde783765);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 72))
        (expr.literal 0x2378b9039096d1b7);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 80))
        (expr.literal 0x7988f8761bdc51dc);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 88))
        (expr.literal 0x2076995003fc77a1);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 96))
        (expr.literal 0x827eca0ba621315b);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 104))
        (expr.literal 0xe5a72bce8d63cb9f);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 112))
        (expr.literal 0xf68f7764c28b6f8a);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 120))
        (expr.literal 0x2f230063cf081517);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 128))
        (expr.literal 0x94506632528d6a9a);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 136))
        (expr.literal 0xd3cde88eeb996ca3);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 144))
        (expr.literal 0xc0bd38c3195c899e);
      cmd.store Syntax.access_size.word
        (expr.op bopname.add (expr.var "h3") (expr.literal 152))
        (expr.literal 0x000f686b3d807d01)
    ].

  Lemma h3_store_limbs_wp :
    forall call t (m : mem) l (a_h3 : word) (oldws : list word) R,
      length oldws = 20%nat ->
      map.get l "h3" = Some a_h3 ->
      (array scalar (word.of_Z 8) a_h3 oldws ⋆ R) m ->
      WeakestPrecondition.cmd call h3_store_cmd t m l
        (fun t' m' l' =>
          t' = t /\ l' = l /\
          (array scalar (word.of_Z 8) a_h3 h3_limbs ⋆ R) m').
  Proof.
    (* This proof processes 20 word stores via repeat straightline.
       It takes ~50 minutes to compile. Run with:
       eval $(opam env --switch=rocq-9) && coqc -Q src Crypto \
         src/Bedrock/Field/Synthesis/Examples/BLS12_FinalExpH3.v

       Proof outline:
       1. Destruct oldws into 20 words
       2. simpl array + address normalization
       3. unfold h3_store_cmd + repeat straightline
       4. Rebuild h3_limbs array via ecancel_assumption *)
    intros call0 t0 m0 l0 a oldws R Hlen Hget Hsep.
    destruct oldws as [|o0 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o1 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o2 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o3 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o4 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o5 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o6 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o7 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o8 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o9 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o10 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o11 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o12 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o13 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o14 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o15 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o16 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o17 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o18 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o19 r]; [simpl in Hlen; discriminate|].
    destruct r; [|simpl in Hlen; discriminate]. clear Hlen.
    simpl array in Hsep.
    repeat rewrite word.add_assoc in Hsep.
    repeat match type of Hsep with
    | context [word.add (word.of_Z ?x) (word.of_Z ?y)] =>
      let v := eval cbv in (x + y) in
      change (word.add (word.of_Z x) (word.of_Z y)) with (word.of_Z v) in Hsep
    end.
    unfold h3_store_cmd, BLS12_Pairing.cmd_seq_list.
    repeat straightline.
    split. { reflexivity. }
    split. { reflexivity. }
    unfold h3_limbs. simpl array.
    repeat rewrite word.add_assoc.
    repeat match goal with
    | |- context [word.add (word.of_Z ?x) (word.of_Z ?y)] =>
      let v := eval cbv in (x + y) in
      change (word.add (word.of_Z x) (word.of_Z y)) with (word.of_Z v)
    end.
    ecancel_assumption.
  Qed.

  (* Weakening lemma for WP postconditions *)
  Lemma wp_cmd_weaken : forall call c t m l (p1 p2 : _ -> _ -> _ -> Prop),
    WeakestPrecondition.cmd call c t m l p1 ->
    (forall t' m' l', p1 t' m' l' -> p2 t' m' l') ->
    WeakestPrecondition.cmd call c t m l p2.
  Proof.
    intros.
    eapply WeakestPreconditionProperties.Proper_cmd;
      [exact WeakestPreconditionProperties.Proper_call | | exact H].
    cbv [Morphisms.pointwise_relation Basics.impl]. exact H0.
  Qed.

  (* Bridge lemma: apply h3_store_limbs_wp to the inlined store sequence.
     Since WP for cmd.seq is definitionally associative, the WP of
       cmd.seq s1 (cmd.seq s2 ... (cmd.seq s20 rest))
     is the same as the WP of
       cmd.seq h3_store_cmd rest
     This lemma packages the application for use in the main proof. *)
  Lemma h3_stores_then_rest :
    forall call t (m : mem) l (a_h3 : word) (oldws : list word) R
           (post : Semantics.trace -> mem -> locals -> Prop),
      length oldws = 20%nat ->
      map.get l "h3" = Some a_h3 ->
      (array scalar (word.of_Z 8) a_h3 oldws ⋆ R) m ->
      (forall m', (array scalar (word.of_Z 8) a_h3 h3_limbs ⋆ R) m' ->
        post t m' l) ->
      WeakestPrecondition.cmd call h3_store_cmd t m l post.
  Proof.
    intros.
    eapply wp_cmd_weaken.
    - exact (h3_store_limbs_wp call t m l a_h3 oldws R H H0 H1).
    - intros t' m' l' [Ht [Hl Hsep]]. subst t' l'. exact (H2 m' Hsep).
  Qed.

End H3Store.
