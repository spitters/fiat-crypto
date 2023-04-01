Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Export Crypto.Spec.ModularArithmetic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.

(*Move elsewhere*)
Lemma firstn_skipn {A : Type} : forall (l : list A) n, (firstn n l) ++ (skipn n l) = l.
Proof.
  intros. generalize dependent n. induction l.
  - destruct n; auto.
  - intros. destruct n; simpl; auto.
    rewrite IHl; auto.
Qed.

Lemma length_firstn {A: Type} : forall (l :list A) n, (length l >= n)%nat -> length (firstn n l) = n.
Proof.
  intros. generalize dependent n. induction l.
  - intros. simpl in H. destruct n; try lia. simpl. auto.
  - intros. destruct n; simpl; auto.
    eapply f_equal. simpl in H. eapply IHl. lia.
Qed.

Lemma length_skipn {A: Type} : forall (l : list A) n, (length l = n + n)%nat -> length (skipn n l) = n.
Proof.
  intros. pose proof H. pose proof (firstn_skipn l n).
  rewrite <- H1 in H.
  rewrite app_length in H.
  rewrite length_firstn in H; try lia.
Qed.

Lemma firstn_app {A : Type} : forall (a b : list A) n, (Datatypes.length a >= n)%nat -> firstn n (a ++ b) = firstn n a.
Proof.
  intros. generalize dependent n. induction a.
  - intros. simpl. simpl in H. destruct n; try discriminate.
    + simpl. auto.
    + inversion H.
  - intros. simpl. destruct n.
    + simpl; auto.
    + simpl. rewrite IHa; auto.
      simpl in H. lia.
Qed.

Lemma skipn_app {A : Type} : forall (a b : list A) n, (Datatypes.length a = n)%nat -> skipn n (a ++ b) = b.
Proof.
  intros. generalize dependent n. induction a.
  - intros; destruct n; try discriminate. auto.
  - intros. simpl. destruct n; try discriminate. simpl in *. inversion H. rewrite H1. apply IHa. auto.
Qed.

Lemma firstn_app' {A : Type} : forall (a b : list A) n, (Datatypes.length a = n)%nat -> firstn n (a ++ b) = a.
Proof.
  intros. rewrite firstn_app; try lia.
  generalize dependent n. induction a.
  - intros. destruct n; simpl; auto.
  - intros. destruct n; try discriminate. simpl in *. inversion H. rewrite H1. rewrite IHa; auto.
Qed.
(* end move elsewhere *)

Section Fp2.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}. 
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {prime_parameters : PrimeParameters}
          {prime_parameters_ok : PrimeParameters_ok}
          {M_mod : (Z.pos M_pos) mod 4 =? 3 = true}.

  Local Notation F := (F M_pos).
  Local Notation Fp2 := ((F * F)%type).

  Existing Instance prime_field_parameters.
  Context {F_names : FieldNames F}.
  Context {F_representation : FieldRepresentation F}
          {F_representation_ok : FieldRepresentation_ok F}.

  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  Instance spec_of_F_felem_copy : spec_of (felem_copy (F:=F)) := spec_of_felem_copy (F:=F).
  Instance spec_of_F_select_znz : spec_of (select_znz (F:=F)) := spec_of_selectznz (F:=F).
  Instance spec_of_F_add : spec_of (add (F:=F)) := binop_spec (bin_add (F:=F)).
  Instance spec_of_F_mul : spec_of (mul (F:=F)) := binop_spec (bin_mul (F:=F)).
  Instance spec_of_F_sub : spec_of (sub (F:=F)) := binop_spec (bin_sub (F:=F)).

  Local Arguments Field.FElem _ {_ _ _ _ _ _}.
  Local Arguments felem_size_in_words _ {_ _ _ _ _ _}.
  Local Arguments felem_size_in_bytes _ {_ _ _ _ _ _}.

  Local Notation felem_offset := (Memory.bytes_per_word width * Z.of_nat (felem_size_in_words F)).
  Local Notation felem_offset_word := (word.of_Z felem_offset).

  Existing Instance Fp2_field_parameters.
  Existing Instance Fp2_field_parameters_ok.
  Existing Instance Fp2_field_representation.
  Existing Instance Fp2_field_representation_ok.

  Lemma fst_felem_app : forall a b pa Ra m, (Field.FElem F pa a * Ra)%sep m
    -> fst_felem (a ++ b) = a.
  Proof.
    intros. cbv [Field.FElem Bignum.Bignum] in *. sepsimpl.
    cbv [fst_felem]. rewrite firstn_app'; auto.
  Qed.

  Lemma snd_felem_app : forall a b pa Ra m, (Field.FElem F pa a * Ra)%sep m
  -> snd_felem (a ++ b) = b.
  Proof.
    intros. cbv [Field.FElem Bignum.Bignum] in *. sepsimpl.
    cbv [snd_felem]. rewrite skipn_app; auto.
  Qed.

  Lemma Fp2_list_decomp : forall l, fst_felem l ++ snd_felem l = l.
  Proof.
    intros. cbv [fst_felem snd_felem]. rewrite firstn_skipn. auto.
  Qed.

  Lemma Fp_FElem_to_Fp2_sep : forall px x m,
    ((Field.FElem F px (fst_felem x)) * (Field.FElem F (word.add px felem_offset_word) (snd_felem x)))%sep m -> (Field.FElem Fp2 px x m).
  Proof.
    intros. cbv [Field.FElem Bignum.Bignum felem_size_in_words]. simpl. sepsimpl.
    1: {
      cbv [Field.FElem Bignum.Bignum] in H. sepsimpl.
      cbv [fst_felem snd_felem] in *.
      pose proof H.
      epose proof (firstn_skipn x (felem_size_in_words F)).
      rewrite <- H3.
      rewrite app_length.
      rewrite H, H0.
      auto.
    }

    pose proof (Fp2_list_decomp x).
    rewrite <- H0.
    eapply array_append.
    cbv [Field.FElem Bignum.Bignum] in H.
    sepsimpl.
    eapply sep_comm in H2.
    assert ( word.add px felem_offset_word =  (word.add px
    (word.of_Z
       (@word.unsigned width  _(word.of_Z (Memory.bytes_per_word width)) *
        Z.of_nat (Datatypes.length (fst_felem x))))) ).
    {
      eapply f_equal.
      rewrite word.ring_morph_mul. rewrite H.
      rewrite word.ring_morph_mul.
      rewrite word.of_Z_unsigned. auto.
    }
    rewrite <- H3. auto.
  Qed.

  Lemma Fp_FElem_to_Fp2_R_sep : forall px x m R,
    ((Field.FElem F px (fst_felem x)) * (Field.FElem F (word.add px felem_offset_word) (snd_felem x)) * R)%sep m -> ((Field.FElem Fp2 px x * R)%sep m).
  Proof.
    intros. destruct H, H, H, H0.
    eexists; eexists; split; eauto; split; eauto.
    apply Fp_FElem_to_Fp2_sep. auto.
  Qed.

  Lemma Fp2_FElem_to_Fp_sep : forall px x m,
    (Field.FElem Fp2 px x m) -> ((Field.FElem F px (fst_felem x)) * (Field.FElem F (word.add px felem_offset_word) (snd_felem x)))%sep m.
  Proof.
    intros. cbv [Field.FElem Bignum.Bignum felem_size_in_words] in H. simpl in H.
    rewrite Nat.add_0_r in H; sepsimpl.
    pose proof (Fp2_list_decomp x).
    rewrite <- H1 in H0.
    eapply array_append in H0.
    eassert ((word.of_Z
    (word.unsigned (word.of_Z (Memory.bytes_per_word width)) *
     Z.of_nat (Datatypes.length (fst_felem x)))) = _).
     {
       cbv [fst_felem]. rewrite length_firstn; [| lia].
       rewrite word.ring_morph_mul. rewrite word.of_Z_unsigned.
       rewrite <- word.ring_morph_mul. auto.
     }
     rewrite H2 in H0.
     clear H1 H2.
     cbv [Field.FElem Bignum.Bignum]. sepsimpl.
      - cbv [fst_felem]. eapply length_firstn. assert (forall n, (n + n >= n)%nat).
        {
          intros; lia.
        }
        rewrite H. apply H1.
      - cbv [snd_felem]. rewrite length_skipn; auto.
      - eapply sep_comm. auto.
  Qed.

  Lemma Fp2_FElem_to_Fp_R_sep : forall px x m R,
    ((Field.FElem Fp2 px x * R)%sep m) ->
    ((Field.FElem F px (fst_felem x)) * (Field.FElem F (word.add px felem_offset_word) (snd_felem x)) * R)%sep m.
  Proof.
    intros. destruct H, H, H, H0.
    eexists; eexists; split; eauto; split; eauto.
    apply Fp2_FElem_to_Fp_sep. auto.
  Qed.

  Definition expr_2nd_felem (x : Syntax.expr) := expr.op bopname.add x (expr.literal felem_offset).

  Context {Fp2_names : FieldNames Fp2}.

  Definition Fp2_select_znz : bedrock2.Syntax.func :=
    (select_znz (F:=Fp2), (["out"; "c"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes Fp2) as allocx;
      stackalloc (felem_size_in_bytes Fp2) as allocy;
      coq:(cmd.call [] (felem_copy (F:=F)) [expr.var ("allocx"); expr.var ("inx")]);
      coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var ("allocx")); expr_2nd_felem (expr.var ("inx"))]);
      coq:(cmd.call [] (felem_copy (F:=F)) [expr.var ("allocy"); expr.var ("iny")]);
      coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var ("allocy")); expr_2nd_felem (expr.var ("iny"))]);
      coq:(cmd.call [] (select_znz (F:=F)) [expr.var "out"; expr.var "c"; expr.var "allocx"; expr.var "allocy"]);
      coq:(cmd.call [] (select_znz (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "c"; expr_2nd_felem (expr.var "allocx"); expr_2nd_felem (expr.var "allocy")])
    ))).

  Instance spec_of_Fp2_select_znz : spec_of (select_znz (F:=Fp2)) := spec_of_selectznz (F:=Fp2).

  Definition Fp2_add : bedrock2.Syntax.func :=
    (add (F:=Fp2), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes Fp2) as allocx;
      stackalloc (felem_size_in_bytes Fp2) as allocy;
      coq:(cmd.call [] (felem_copy (F:=F)) [expr.var ("allocx"); expr.var ("inx")]);
      coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var ("allocx")); expr_2nd_felem (expr.var ("inx"))]);
      coq:(cmd.call [] (felem_copy (F:=F)) [expr.var ("allocy"); expr.var ("iny")]);
      coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var ("allocy")); expr_2nd_felem (expr.var ("iny"))]);
      coq:(cmd.call [] (add (F:=F)) [expr.var "out"; expr.var "allocx"; expr.var "allocy"]);
      coq:(cmd.call [] (add (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "allocx"); expr_2nd_felem (expr.var "allocy")])
    ))).

  Instance spec_of_Fp2_add : spec_of (add (F:=Fp2)) := binop_spec bin_add (F:=Fp2).

  Ltac bind_body_of_function' f := (*using alternative bind_body that does not normalize body of funcction, as it is horribly slow.*)
    let fname := open_constr:(_) in
    let fargs := open_constr:(_) in
    let frets := open_constr:(_) in
    let fbody := open_constr:(_) in
    let funif := open_constr:((fname, (fargs, frets, fbody))) in
    unify f funif;
    let G := lazymatch goal with |- ?G => G end in
    let P := lazymatch eval pattern f in G with ?P _ => P end in
    change (bindcmd fbody (fun c : Syntax.cmd => P (fname, (fargs, frets, c))));
             cbv beta iota delta [bindcmd]; intros.

  Ltac enter' f :=
  cbv beta delta [program_logic_goal_for]; intros;
  bind_body_of_function' f;
  lazymatch goal with |- ?s _ => cbv beta delta [s] end.

  Lemma alloc_to_FElem : forall a m, Memory.anybytes a (felem_size_in_bytes Fp2) m -> exists f, Field.FElem Fp2 a f m.
  Proof.
    intros. eapply anybytes_to_array_1 in H. destruct H, H. cbv [felem_size_in_bytes] in *.
    eapply (Bignum.Bignum_of_bytes (felem_size_in_words Fp2)) in H; try lia.
    eexists. cbv [Field.FElem]. eauto.
  Qed.

  Lemma alloc_to_FElem_F : forall a m, Memory.anybytes a (felem_size_in_bytes F) m -> exists f, Field.FElem F a f m.
  Proof.
    intros. eapply anybytes_to_array_1 in H. destruct H, H. cbv [felem_size_in_bytes] in *.
    eapply (Bignum.Bignum_of_bytes (felem_size_in_words F)) in H; try lia.
    eexists. cbv [Field.FElem]. eauto.
  Qed.

  Lemma FElem_F_to_anybytes : forall pa a m, Field.FElem F pa a m -> Memory.anybytes pa (felem_size_in_bytes F) m.
  Proof.
    intros.
    cbv [Field.FElem] in H.
    eapply Bignum.Bignum_to_bytes in H.
    sepsimpl.
    eapply array_1_to_anybytes in H0.
    assert (felem_size_in_bytes F = (Z.of_nat
    (Datatypes.length
       (flat_map
          (fun w : word =>
           LittleEndianList.le_split
             (Z.to_nat (Memory.bytes_per_word width)) 
             (word.unsigned w)) a)))).
             {
               rewrite H. cbv [felem_size_in_bytes].
               rewrite Nat2Z.inj_mul.
               rewrite Z2Nat.id; auto.
               cbv [Memory.bytes_per_word].
               destruct word_ok; lia.
             }
    rewrite <- H1 in H0. auto.
  Qed.

  Lemma FElem_Fp2_to_anybytes : forall pa a m, Field.FElem Fp2 pa a m -> Memory.anybytes pa (felem_size_in_bytes Fp2) m.
  Proof.
    intros.
    cbv [Field.FElem] in H.
    eapply Bignum.Bignum_to_bytes in H.
    sepsimpl.
    eapply array_1_to_anybytes in H0.
    assert (felem_size_in_bytes Fp2 = (Z.of_nat
    (Datatypes.length
       (flat_map
          (fun w : word =>
           LittleEndianList.le_split
             (Z.to_nat (Memory.bytes_per_word width)) 
             (word.unsigned w)) a)))).
             {
               rewrite H. cbv [felem_size_in_bytes].
               rewrite Nat2Z.inj_mul.
               rewrite Z2Nat.id; auto.
               cbv [Memory.bytes_per_word].
               destruct word_ok; lia.
             }
    rewrite <- H1 in H0. auto.
  Qed.

  Ltac collect H1 H2 := let Hnew := (fresh "Hnew") in
    eassert (Hnew : id (fun m => (_ m) /\ (_ m)) _) by (cbv [id]; split; [eapply H1| eapply H2]); clear H1 H2.

  Ltac solve_locals l1 l2 l3 :=
    repeat (repeat straightline; eexists; split; [
      subst l1 l2 l3;
      repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same|
    ]); repeat straightline.

  Ltac solve_locals5 l1 l2 l3 l4 l5 :=
    repeat (repeat straightline; eexists; split; [
      subst l1 l2 l3 l4 l5;
      repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same|
    ]); repeat straightline.

  Import Syntax BinInt String List.ListNotations.

  Lemma Fp2_select_znz_ok : program_logic_goal_for_function! Fp2_select_znz.
  Proof.
    enter' Fp2_select_znz. clear H0 H1 H2. cbv [spec_of_selectznz] in *.
    intros. unfold1_call_goal. cbv match beta delta [call_body].
    assert ((select_znz =? select_znz)%string = true) by (rewrite eqb_refl; auto).
    rewrite H1.
    cbv match beta delta [func].
    repeat straightline.

    eapply Fp2_FElem_to_Fp_R_sep in H0.
    eapply Fp2_FElem_to_Fp_R_sep in H2.
    eapply Fp2_FElem_to_Fp_R_sep in H5.

    collect H0 H2.
    collect Hnew H5.

    split; [eapply felem_size_in_bytes_mod |].
    repeat straightline.
    split; [eapply felem_size_in_bytes_mod |].
    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].

    eapply alloc_to_FElem in H5. destruct H5.
    eapply alloc_to_FElem in H0. destruct H0.
    eapply Fp2_FElem_to_Fp_sep in H0, H5.
    eassert (((_ * _) * _)%sep mCombined0).
    {
      do 2 eexists; split; [eauto |]; split; [| apply H5].
      do 2 eexists; split; [eauto |]; split; [| apply H0].
      apply Hnew0.
    }
    clear dependent mStack.
    clear dependent mStack0.

    straightline_call.
    1: {
      split; try ecancel_assumption.
      remember ((Field.FElem _ a (fst_felem x1))) as R1.
      remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x1)) as R2.
      remember ((Field.FElem _ a0 (fst_felem x0))) as R3.
      remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem x0)) as R4.
      remember (R1 * R2)%sep as R1'.
      remember (R3 * R4)%sep as R2'.
      eapply sep_assoc in H8.

      eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?].
      eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?].
      subst.
      ecancel_assumption.
    }
    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.
      cbv [id] in *.
      remember ((Field.FElem _ a (fst_felem x))) as R1.
      remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x1)) as R2.
      remember ((Field.FElem _ a0 (fst_felem x0))) as R3.
      remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem x0)) as R4.
      eapply sep_comm in H5.
      eapply sep_assoc in H5.
      remember (R2 * (R3 * R4) * R1)%sep as R1'.
      eapply sep_and_l_fwd in H5; destruct H5 as [H5 ?].
      eapply sep_and_l_fwd in H5; destruct H5 as [H5 ?].
      subst.
      ecancel_assumption.
    }
    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.
      cbv [id] in *.
      remember ((Field.FElem _ a (fst_felem x))) as R1.
      remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x)) as R2.
      remember ((Field.FElem _ a0 (fst_felem x0))) as R3.
      remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem x0)) as R4.
      eapply sep_comm in H7.
      eapply sep_assoc in H7.
      eapply sep_comm in H7.
      eapply sep_assoc in H7.
      remember ((R3 * R4))%sep as R1'.
      remember ((R2 * R1))%sep as R2'.
      eapply sep_assoc in H7.
      eapply sep_and_l_fwd in H7; destruct H7 as [H7 ?].
      eapply sep_and_l_fwd in H7; destruct H7 as [H7 ?].
      subst.
      ecancel_assumption.
    }

    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.
      cbv [id] in *.
      remember ((Field.FElem _ a (fst_felem x))) as R1.
      remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x)) as R2.
      remember ((Field.FElem _ a0 (fst_felem y))) as R3.
      remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem x0)) as R4.
      eapply sep_comm in H9.
      eapply sep_assoc in H9.
      eapply sep_comm in H9.
      eapply sep_assoc in H9.
      eapply (sep_assoc _ _ (R3 * R2)%sep) in H9.
      eapply (sep_comm R1) in H9.
      eapply sep_assoc in H9.
      remember ((R3 * R2 * R1))%sep as R1'.
      eapply sep_assoc in H9.
      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?].
      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?].
      subst.
      ecancel_assumption.
    }

    repeat straightline.
    eexists; split; [solve_locals l1 l0 l |].

    (*deconstructing sep hyp.*)
    cbv [id] in *.
    remember ((Field.FElem _ a (fst_felem x))) as R1.
    remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x)) as R2.
    remember ((Field.FElem _ a0 (fst_felem y))) as R3.
    remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem y)) as R4.
    rename H10 into H11.
    eapply sep_assoc in H11. eapply (sep_assoc (R4 * R3)%sep) in H11.
    eapply (sep_assoc (R4 * R3 * R2)%sep) in H11.
    eapply sep_comm in H11.
    eapply sep_and_l_fwd in H11; destruct H11 as [H11 ?].
    eapply sep_and_l_fwd in H11; destruct H11 as [H11 ?].
    subst.

    straightline_call.
    1: {
      split; [| split; [| split]].
      1: {
        subst. ecancel_assumption.
      }
      2: {
        subst. clear H2 H0. ecancel_assumption.
      }
      1: { subst. clear H2 H0. ecancel_assumption.
      }
      auto.
    }

    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].
    destruct (word.unsigned pc =? 1) eqn:eq.
    (*after destruct*)
    {

      straightline_call.
      1: {
        split; [| split; [| split]].
        1: subst; ecancel_assumption.
        1: subst; ecancel_assumption.
        1: subst; ecancel_assumption.
        1: auto.
      }

      repeat straightline. (*mStack is not in scope in the below proof; should otherwise go through. destruct sep hyp before introducing evars.*)

      rewrite eq in H16.

      eassert ((Field.FElem _ a0 _  * _)%sep a8).
      {
        eapply Fp_FElem_to_Fp2_R_sep. ecancel_assumption.
      }
      destruct H10, H10, H10, H17.
      eexists. eexists. split.
      1: {
        eapply FElem_Fp2_to_anybytes. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      clear H16 H12 H5 H0 H2 H11 H9 H7 H13 H14.

      eassert ((Field.FElem _ a _  * _)%sep x3).
      {
        eapply Fp_FElem_to_Fp2_R_sep. ecancel_assumption.
      }
      clear H18.

      destruct H0, H0, H0, H2.

      do 2 eexists; split.
      1: {
        eapply FElem_Fp2_to_anybytes; eauto.
      }

      split; [eapply map.split_comm; eauto| ].

      repeat straightline. split; auto. 
      eapply Fp_FElem_to_Fp2_R_sep.
      ecancel_assumption.
    }
    (*other case for conditional*)
    {
      straightline_call.
      1: {
        split; [| split; [| split]].
        1: subst; ecancel_assumption.
        1: subst; ecancel_assumption.
        1: subst; ecancel_assumption.
        1: auto.
      }

      repeat straightline. (*mStack is not in scope in the below proof; should otherwise go through. destruct sep hyp before introducing evars.*)

      rewrite eq in H16.

      eassert ((Field.FElem _ a0 _  * _)%sep a8).
      {
        eapply Fp_FElem_to_Fp2_R_sep. ecancel_assumption.
      }
      destruct H10, H10, H10, H17.
      eexists. eexists. split.
      1: {
        eapply FElem_Fp2_to_anybytes. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      clear H16 H12 H5 H0 H2 H11 H9 H7 H13 H14.

      eassert ((Field.FElem _ a _  * _)%sep x3).
      {
        eapply Fp_FElem_to_Fp2_R_sep. ecancel_assumption.
      }
      clear H18.

      destruct H0, H0, H0, H2.

      do 2 eexists; split.
      1: {
        eapply FElem_Fp2_to_anybytes; eauto.
      }

      split; [eapply map.split_comm; eauto| ].

      repeat straightline. split; auto.
      eapply Fp_FElem_to_Fp2_R_sep.
      ecancel_assumption.
    }
  Qed.
  (*Proof of select_znz_Fp2 finished.*)

  Lemma Fp2_add_ok : program_logic_goal_for_function! Fp2_add.
  Proof.
    enter' Fp2_add. clear H0 H1 H2. cbv [binop_spec] in *.
    intros. unfold1_call_goal. cbv match beta delta [call_body].
    assert ((Field.add =? Field.add)%string = true) by (rewrite eqb_refl; auto).
    rewrite H1.
    cbv match beta delta [func].
    repeat straightline.

    eapply Fp2_FElem_to_Fp_R_sep in H5, H6, H7.

    collect H5 H6.
    collect Hnew H7.

    split; [eapply felem_size_in_bytes_mod |].
    repeat straightline.
    split; [eapply felem_size_in_bytes_mod |].
    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].

    eapply alloc_to_FElem in H7. destruct H7.
    eapply alloc_to_FElem in H5. destruct H5.
    eapply Fp2_FElem_to_Fp_sep in H5, H7.
    eassert (((_ * _) * _)%sep mCombined0).
    {
      do 2 eexists; split; [eauto |]; split; [| apply H7].
      do 2 eexists; split; [eauto |]; split; [| apply H5].
      apply Hnew0.
    }
    clear dependent mStack.
    clear dependent mStack0.

    straightline_call.
    1: {
      split; try ecancel_assumption.
      remember ((Field.FElem _ a (fst_felem x3))) as R1.
      remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x3)) as R2.
      remember ((Field.FElem _ a0 (fst_felem x2))) as R3.
      remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem x2)) as R4.
      remember (R1 * R2)%sep as R1'.
      remember (R3 * R4)%sep as R2'.
      eapply sep_assoc in H9.

      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?].
      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?].
      subst.
      ecancel_assumption.
    }
    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.
      cbv [id] in *.
      remember ((Field.FElem _ a (fst_felem x))) as R1.
      remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x3)) as R2.
      remember ((Field.FElem _ a0 (fst_felem x2))) as R3.
      remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem x2)) as R4.
      eapply sep_comm in H7.
      eapply sep_assoc in H7.
      remember (R2 * (R3 * R4) * R1)%sep as R1'.
      eapply sep_and_l_fwd in H7; destruct H7 as [H7 ?].
      eapply sep_and_l_fwd in H7; destruct H7 as [H7 ?].
      subst.
      ecancel_assumption.
    }
    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.
      cbv [id] in *.
      remember ((Field.FElem _ a (fst_felem x))) as R1.
      remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x)) as R2.
      remember ((Field.FElem _ a0 (fst_felem x2))) as R3.
      remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem x2)) as R4.
      eapply sep_comm in H8.
      eapply sep_assoc in H8.
      eapply sep_comm in H8.
      eapply sep_assoc in H8.
      remember ((R3 * R4))%sep as R1'.
      remember ((R2 * R1))%sep as R2'.
      eapply sep_assoc in H8.
      eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?].
      eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?].
      subst.
      ecancel_assumption.
    }

    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.
      cbv [id] in *.
      remember ((Field.FElem _ a (fst_felem x))) as R1.
      remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x)) as R2.
      remember ((Field.FElem _ a0 (fst_felem y))) as R3.
      remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem x2)) as R4.
      eapply sep_comm in H10.
      eapply sep_assoc in H10.
      eapply sep_comm in H10.
      eapply sep_assoc in H10.
      eapply (sep_assoc _ _ (R3 * R2)%sep) in H10.
      eapply (sep_comm R1) in H10.
      eapply sep_assoc in H10.
      remember ((R3 * R2 * R1))%sep as R1'.
      eapply sep_assoc in H10.
      eapply sep_and_l_fwd in H10; destruct H10 as [H10 ?].
      eapply sep_and_l_fwd in H10; destruct H10 as [H10 ?].
      subst.
      ecancel_assumption.
    }

    repeat straightline.
    eexists; split; [solve_locals l1 l0 l |].

    (*deconstructing sep hyp.*)
    cbv [id] in *.
    remember ((Field.FElem _ a (fst_felem x))) as R1.
    remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x)) as R2.
    remember ((Field.FElem _ a0 (fst_felem y))) as R3.
    remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem y)) as R4.
    eapply sep_assoc in H11. eapply (sep_assoc (R4 * R3)%sep) in H11.
    eapply (sep_assoc (R4 * R3 * R2)%sep) in H11.
    eapply sep_comm in H11.
    eapply sep_and_l_fwd in H11; destruct H11 as [H11 ?].
    clear H11. subst.


    straightline_call.
    1: {
      split; [|split; [| split; [| split]]].
      5: {
        subst; ecancel_assumption.
      }
      3: {
        eexists. ecancel_assumption.
      }
      3: {
        eexists; ecancel_assumption.
      }
      1: {
        destruct H0. eauto.
      }
      1: {
        destruct H2; eauto.
      }
    }
    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].

    straightline_call.
    1: {
      split; [| split; [| split; [| split]]].
      5: ecancel_assumption.
      4: eexists; ecancel_assumption.
      3: eexists; ecancel_assumption.
      1: destruct H0; eauto.
      1: destruct H2; eauto.
    }

    repeat straightline. (*mStack is not in scope in the below proof; should otherwise go through. destruct sep hyp before introducing evars.*)
    eassert ((Field.FElem _ a0 _  * _)%sep a8).
    {
      eapply Fp_FElem_to_Fp2_R_sep. ecancel_assumption.
    }
    destruct H6, H6, H6, H11.
    eexists. eexists. split.
    1: {
      eapply FElem_Fp2_to_anybytes. eauto.
    }
    split; [eapply map.split_comm; eauto| ].

    clear H20 H14 H5 H10 H8 H7 H9.

    eassert ((Field.FElem _ a _  * _)%sep x7).
    {
      eapply Fp_FElem_to_Fp2_R_sep. ecancel_assumption.
    }
    clear H21.

    destruct H5, H5, H5, H7.

    do 2 eexists; split.
    1: {
      eapply FElem_Fp2_to_anybytes; eauto.
    }

    split; [eapply map.split_comm; eauto| ].

    repeat straightline. split; auto. split; auto.

    exists (x4 ++ x5). split; [| split].

    3: {
      eapply Fp_FElem_to_Fp2_R_sep. erewrite fst_felem_app; [| ecancel_assumption].
      erewrite snd_felem_app; [| ecancel_assumption].
      ecancel_assumption.
    }
    2: {
      split; eauto. erewrite fst_felem_app; try ecancel_assumption; auto.
      erewrite snd_felem_app; try ecancel_assumption; auto.
    }
    simpl.
    cbv [addp2].
    apply Prod.path_pair.
    1: {
      erewrite fst_felem_app; try ecancel_assumption. simpl. auto.
    }
    erewrite snd_felem_app; try ecancel_assumption; simpl; auto.
  Qed.

  (*multiplication in Fp2*)

  Definition Fp2_mul : bedrock2.Syntax.func :=
    (mul (F:=Fp2), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        stackalloc (felem_size_in_bytes F) as v0;
        stackalloc (felem_size_in_bytes F) as v1;
        stackalloc (felem_size_in_bytes Fp2) as allocx;
        stackalloc (felem_size_in_bytes Fp2) as allocy;
        coq:(cmd.call [] (felem_copy (F:=F)) [expr.var ("allocx"); expr.var ("inx")]);
        coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var ("allocx")); expr_2nd_felem (expr.var ("inx"))]);
        coq:(cmd.call [] (felem_copy (F:=F)) [expr.var ("allocy"); expr.var ("iny")]);
        coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var ("allocy")); expr_2nd_felem (expr.var ("iny"))]);
        coq:(cmd.call [] (mul (F:=F)) [expr.var "v0"; expr.var "allocx"; expr.var "allocy"]);
        coq:(cmd.call [] (mul (F:=F)) [expr.var "v1"; expr_2nd_felem (expr.var "allocx"); expr_2nd_felem (expr.var "allocy")]);
        coq:(cmd.call [] (add (F:=F)) [expr.var "out"; expr.var "allocx"; expr_2nd_felem (expr.var "allocx")]);
        coq:(cmd.call [] (add (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "allocy"; expr_2nd_felem (expr.var "allocy")]);
        coq:(cmd.call [] (mul (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "out"]);
        coq:(cmd.call [] (sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v0"]);
        coq:(cmd.call [] (sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v1"]);
        coq:(cmd.call [] (sub (F:=F)) [expr.var "out"; expr.var "v0"; expr.var "v1"])
    ))).

  Instance spec_of_Fp2_mul : spec_of (mul (F:=Fp2)) := binop_spec bin_mul (F:=Fp2).

  Lemma M_pos_prime : Znumtheory.prime (Z.pos M_pos).
  Proof.
    destruct prime_parameters_ok; auto.
  Qed.

  Lemma Fp2_mul_ok : program_logic_goal_for_function! Fp2_mul.
  Proof.
    enter' Fp2_mul. clear H0 H1 H2 H3 H4 H5 H8 H9. cbv [binop_spec] in *.
    intros. unfold1_call_goal. cbv match beta delta [call_body].
    assert ((Field.mul =? Field.mul)%string = true) by (rewrite eqb_refl; auto).
    rewrite H1.
    cbv match beta delta [func].
    repeat straightline.

    eapply Fp2_FElem_to_Fp_R_sep in H3, H4, H5.

    collect H3 H4.
    collect Hnew H5.

    split; [eapply felem_size_in_bytes_mod |].
    repeat straightline.
    split; [eapply felem_size_in_bytes_mod |].
    repeat straightline.
    split; [eapply felem_size_in_bytes_mod |].
    repeat straightline.
    split; [eapply felem_size_in_bytes_mod |].
    repeat straightline.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    eapply alloc_to_FElem in H9. destruct H9.
    eapply alloc_to_FElem in H12. destruct H12.
    eapply Fp2_FElem_to_Fp_sep in H9, H12.
    eapply alloc_to_FElem_F in H3. destruct H3.
    eapply alloc_to_FElem_F in H5; destruct H5.
    eassert (((_ * _ * _ * _) * _)%sep mCombined2).
    {
      do 2 eexists; split; [eassumption | split; [| apply H12]].
      do 2 eexists; split; [eassumption | split; [| apply H9]].
      do 2 eexists; split; [eassumption | split; [| apply H5]].
      do 2 eexists; split; [eassumption | split; [| apply H3]].
      apply Hnew0.
    }



    clear dependent mStack.
    clear dependent mStack0.
    clear dependent mStack1.
    clear dependent mStack2.

    (*unfolding as multiple preconditions*)
    (* cbv [id] in *.
      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?].
      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?]. *)

    remember (Field.FElem _ a x4) as R1.
    remember (Field.FElem _ a0 x5) as R2.
    remember (Field.FElem _ a1 (fst_felem x2)) as R3.
    remember (Field.FElem _ (word.add a1 felem_offset_word) (snd_felem x2)) as R4.
    remember (Field.FElem _ a2 (fst_felem x3)) as R5.
    remember (Field.FElem _ (word.add a2 felem_offset_word) (snd_felem x3)) as R6.
    eassert (( _ * (R1 * R2 * R3 * R4 * R5 * R6))%sep mCombined2) by ecancel_assumption.
    subst R1 R2 R3 R4 R5 R6.

    straightline_call.
    1: {
      split; try ecancel_assumption.

      eapply sep_and_l_fwd in H3; destruct H3 as [H3 ?].
      eapply sep_and_l_fwd in H3; destruct H3 as [H3 ?].
      ecancel_assumption.
    }
    repeat straightline. eapply sep_comm in H8. eapply (sep_assoc _ _ (Field.FElem _ a1 _)) in H8.

    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.
      eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?].
      eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?].
      ecancel_assumption.
    }
    repeat straightline. eapply sep_comm in H9. eapply (sep_assoc _ _ (Field.FElem _ (word.add a1 _) _)) in H9.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.

      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?].
      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?].
      ecancel_assumption.
    }
    repeat straightline. eapply sep_comm in H11. eapply (sep_assoc _ _ (Field.FElem _ a2 _)) in H11.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.
      eapply sep_and_l_fwd in H11; destruct H11 as [H11 ?].
      eapply sep_and_l_fwd in H11; destruct H11 as [H11 ?].
      ecancel_assumption.
    }
    repeat straightline. eapply sep_comm in H12. eapply (sep_assoc _ _ (Field.FElem _ (word.add a2 _) _)) in H12.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l |].

    (*deconstructing sep hyp.*)
    cbv [id] in *.
    eapply sep_and_l_fwd in H12; destruct H12 as [H12 ?].
    eapply sep_and_l_fwd in H12; destruct H12 as [H12 ?].
    clear H12 H5.

    Ltac handle_call' := straightline_call; [
          split; [|split; [| split; [| split; [| ecancel_assumption]]]]; [| | eexists; ecancel_assumption| eexists; ecancel_assumption]; eauto
    |].

    destruct H0, H2.

    handle_call'.
    repeat straightline.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    handle_call'.
    repeat straightline.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    handle_call'.
    repeat straightline.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    handle_call'.
    repeat straightline.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    handle_call'.
    repeat straightline.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    handle_call'.
    repeat straightline.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    handle_call'.
    repeat straightline.
    eexists; split; [solve_locals5 l3 l2 l1 l0 l| ].

    handle_call'.
    repeat straightline.

    let Hstack := (fresh "Hstack") in
    let Hsplit := (fresh "Hsplit") in
    let Hnew := (fresh "Hnew") in
    eassert (Hstack : (Field.FElem _ a2 _ * _)%sep a16) by (eapply Fp_FElem_to_Fp2_R_sep; ecancel_assumption);
    destruct Hstack as [? [? [Hsplit [Hstack' Hnew]]]]; do 2 eexists; split; [eapply FElem_Fp2_to_anybytes; eauto| split; [eapply map.split_comm; eauto| ]].

    let Hstack := (fresh "Hstack") in
    let Htemp := (fresh "Htemp") in
    let Hsplit := (fresh "Hsplit") in
    let Hnew := (fresh "Hnew") in
    eassert (Htemp : (Field.FElem _ a1 _ * _)%sep x15) by (eapply Fp_FElem_to_Fp2_R_sep; ecancel_assumption);
    destruct Htemp as [? [? [Hsplit [Hstack Hnew]]]]; do 2 eexists; split; [eapply FElem_Fp2_to_anybytes; eauto| split; [eapply map.split_comm; eauto| ]].


    let Hstack := (fresh "Hstack") in
    let Htemp := (fresh "Htemp") in
    let Hsplit := (fresh "Hsplit") in
    let Hnew := (fresh "Hnew") in
    eassert (Htemp : ((Field.FElem F) a0 _ * _)%sep x17) by (ecancel_assumption);
    destruct Htemp as [? [? [Hsplit [Hstack Hnew]]]]; do 2 eexists; split; [eapply FElem_F_to_anybytes; eauto| split; [eapply map.split_comm; eauto| ]].

    let Hstack := (fresh "Hstack") in
    let Htemp := (fresh "Htemp") in
    let Hsplit := (fresh "Hsplit") in
    let Hnew := (fresh "Hnew") in
    eassert (Htemp : ((Field.FElem F) a _ * _)%sep x19) by (ecancel_assumption);
    destruct Htemp as [? [? [Hsplit [Hstack Hnew]]]]; do 2 eexists; split; [eapply FElem_F_to_anybytes; eauto| split; [eapply map.split_comm; eauto| ]].

    repeat straightline. split; auto; split; auto.
    exists (x13 ++ x12); split; [| split].
    1: {
      simpl. erewrite fst_felem_app; try ecancel_assumption. erewrite snd_felem_app; try ecancel_assumption.
      eapply Prod.path_pair.
      - simpl.
        (* assert (forall x, @feval *)
        (* (@QuadraticFieldExtensionsSpecs.F_parameters prime_field_parameters) *)
        (* width BW word mem F_representation x *)
        (*   = (@feval F_parameters width BW word mem F_representation x)) by auto. *)
        (* rewrite H13. *)
        rewrite H40.
        rewrite H16. rewrite H22.
        eassert (Quad_non_res M_pos = _).
        {
          cbv [Quad_non_res]. assert (Z.pos M_pos mod 4 =? 3 = true) by lia.
          rewrite H13.
          eauto.
        }
        rewrite H13.
        simpl.
        Local Infix "*p" := ModularArithmetic.F.mul (at level 90).
        Local Infix "-p" := ModularArithmetic.F.sub (at level 90).
        Local Infix "+p" := ModularArithmetic.F.add (at level 90).
        remember (feval (fst_felem x)) as xr.
        remember (feval (snd_felem x)) as xi.
        remember (feval (fst_felem y)) as yr.
        remember (feval (snd_felem y)) as yi.
        rewrite F_mul_assoc; [| apply M_pos_prime]. (*admitted primality of M_pos*)
        rewrite <- H13.
        rewrite <- mul_neg_1; eauto. apply M_pos_prime.
      - simpl.
        (* assert (forall x, @feval *)
        (*   (@QuadraticFieldExtensionsSpecs.F_parameters prime_field_parameters) *)
        (*   width BW word mem F_representation x *)
        (*     = (@feval F_parameters width BW word mem F_representation x)) by auto. *)
        (*   rewrite H13. *)
        rewrite H37, H34, H31, H28, H25, H22, H16. simpl.
        remember (feval (fst_felem x)) as xr.
        remember (feval (snd_felem x)) as xi.
        remember (feval (fst_felem y)) as yr.
        remember (feval (snd_felem y)) as yi.
        rewrite mul_equiv; eauto. apply M_pos_prime.
    }
    1: {
      split.
      - erewrite fst_felem_app; try ecancel_assumption. auto.
      - erewrite snd_felem_app; try ecancel_assumption; auto.
    }
    eapply Fp_FElem_to_Fp2_R_sep. erewrite fst_felem_app; try ecancel_assumption.
    erewrite snd_felem_app; try ecancel_assumption.
  Qed.


  (*subtraction in Fp2*)
  Definition Fp2_sub : bedrock2.Syntax.func :=
    (sub (F:=Fp2), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        stackalloc (felem_size_in_bytes Fp2) as allocx;
        stackalloc (felem_size_in_bytes Fp2) as allocy;
        coq:(cmd.call [] (felem_copy (F:=F)) [expr.var ("allocx"); expr.var ("inx")]);
        coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var ("allocx")); expr_2nd_felem (expr.var ("inx"))]);
        coq:(cmd.call [] (felem_copy (F:=F)) [expr.var ("allocy"); expr.var ("iny")]);
        coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var ("allocy")); expr_2nd_felem (expr.var ("iny"))]);
        coq:(cmd.call [] (sub (F:=F)) [expr.var "out"; expr.var "allocx"; expr.var "allocy"]);
        coq:(cmd.call [] (sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "allocx"); expr_2nd_felem (expr.var "allocy")])
    ))).
  
  Instance spec_of_Fp2_sub : spec_of (sub (F:=Fp2)) := binop_spec bin_sub (F:=Fp2).

  Lemma Fp2_sub_ok : program_logic_goal_for_function! Fp2_sub.
  Proof.
    enter' Fp2_sub. clear H0 H1 H2 H4. cbv [binop_spec] in *.
    intros. unfold1_call_goal. cbv match beta delta [call_body].
    assert ((Field.sub =? Field.sub)%string = true) by (rewrite eqb_refl; auto).
    rewrite H1.
    cbv match beta delta [func].
    repeat straightline.

    eapply Fp2_FElem_to_Fp_R_sep in H4, H5, H6.

    collect H4 H5.
    collect Hnew H6.

    split; [eapply felem_size_in_bytes_mod |].
    repeat straightline.
    split; [eapply felem_size_in_bytes_mod |].
    repeat straightline.

    eexists; split; [solve_locals l1 l0 l| ].

    eapply alloc_to_FElem in H4. destruct H4.
    eapply alloc_to_FElem in H6. destruct H6.
    eapply Fp2_FElem_to_Fp_sep in H4, H6.
    eassert (((_ * _) * _)%sep mCombined0).
    {
      do 2 eexists; split; [eassumption | split; [| apply H6]].
      do 2 eexists; split; [eassumption | split; [| apply H4]].
      apply Hnew0.
    }

    clear dependent mStack.
    clear dependent mStack0.

    (*unfolding as multiple preconditions*)
    (* cbv [id] in *.
      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?].
      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?]. *)

    remember (Field.FElem _ a (fst_felem x2)) as R1.
    remember (Field.FElem _ a0 (fst_felem x3)) as R2.
    remember (Field.FElem _ (word.add a felem_offset_word) (snd_felem x2)) as R3.
    remember (Field.FElem _ (word.add a0 felem_offset_word) (snd_felem x3)) as R4.
    eassert (( _ * (R1 * R2 * R3 * R4))%sep mCombined0) by ecancel_assumption.
    subst R1 R2 R3 R4. clear H8.

    straightline_call.
    1: {
      split; try ecancel_assumption.

      eapply sep_and_l_fwd in H4; destruct H4 as [H4 ?].
      eapply sep_and_l_fwd in H4; destruct H4 as [H4 ?].
      ecancel_assumption.
    }
    repeat straightline. eapply sep_comm in H7. eapply (sep_assoc _ _ (Field.FElem _ a _)) in H7.

    eexists; split; [solve_locals l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.
      eapply sep_and_l_fwd in H7; destruct H7 as [H7 ?].
      eapply sep_and_l_fwd in H7; destruct H7 as [H7 ?].
      ecancel_assumption.
    }
    repeat straightline. eapply sep_comm in H8. eapply (sep_assoc _ _ (Field.FElem _ (word.add a _) _)) in H8.
    eexists; split; [solve_locals l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.

      eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?].
      eapply sep_and_l_fwd in H8; destruct H8 as [H8 ?].
      ecancel_assumption.
    }
    repeat straightline. eapply sep_comm in H9. eapply (sep_assoc _ _ (Field.FElem _ a0 _)) in H9.
    eexists; split; [solve_locals l1 l0 l| ].

    straightline_call.
    1: {
      split; try ecancel_assumption.
      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?].
      eapply sep_and_l_fwd in H9; destruct H9 as [H9 ?].
      ecancel_assumption.
    }
    repeat straightline. eapply sep_comm in H10. eapply (sep_assoc _ _ (Field.FElem _ (word.add a0 _) _)) in H10.
    eexists; split; [solve_locals l1 l0 l |].

    (*deconstructing sep hyp.*)
    cbv [id] in *.
    eapply sep_and_l_fwd in H10; destruct H10 as [H10 ?].
    eapply sep_and_l_fwd in H10; destruct H10 as [H10 ?].
    clear H10 H6.


    destruct H0, H2.

    handle_call'.
    repeat straightline.
    eexists; split; [solve_locals l1 l0 l| ].

    handle_call'.
    repeat straightline.

    let Hstack := (fresh "Hstack") in
    let Hsplit := (fresh "Hsplit") in
    let Hnew := (fresh "Hnew") in
    eassert (Hstack : (Field.FElem _ a0 _ * _)%sep a8) by (eapply Fp_FElem_to_Fp2_R_sep; ecancel_assumption);
    destruct Hstack as [? [? [Hsplit [Hstack' Hnew]]]]; do 2 eexists; split; [eapply FElem_Fp2_to_anybytes; eauto| split; [eapply map.split_comm; eauto| ]].

    let Hstack := (fresh "Hstack") in
    let Htemp := (fresh "Htemp") in
    let Hsplit := (fresh "Hsplit") in
    let Hnew := (fresh "Hnew") in
    eassert (Htemp : (Field.FElem _ a _ * _)%sep x7) by (eapply Fp_FElem_to_Fp2_R_sep; ecancel_assumption);
    destruct Htemp as [? [? [Hsplit [Hstack Hnew]]]]; do 2 eexists; split; [eapply FElem_Fp2_to_anybytes; eauto| split; [eapply map.split_comm; eauto| ]].

    repeat straightline. split; auto; split; auto.
    exists (x4 ++ x5); split; [| split].
    1: {
      simpl. erewrite fst_felem_app; try ecancel_assumption. erewrite snd_felem_app; try ecancel_assumption.
      eapply Prod.path_pair; auto.
    }
    1: {
      split.
      - erewrite fst_felem_app; try ecancel_assumption; auto.
      - erewrite snd_felem_app; try ecancel_assumption; auto.
    }
    eapply Fp_FElem_to_Fp2_R_sep. erewrite fst_felem_app; try ecancel_assumption.
    erewrite snd_felem_app; try ecancel_assumption.
  Qed.

End Fp2.
