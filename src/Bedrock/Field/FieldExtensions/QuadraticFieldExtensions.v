Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
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

  (* note that this excludes non-saturated representations *)
  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  Lemma equiv_bounds_FElem x_ptr x
    : Lift1Prop.iff1 (FElem (Some tight_bounds) x_ptr x)
        (FElem (Some loose_bounds) x_ptr x).
  Proof.
    split.
    - apply relax_bounds_FElem.
    - unfold FElem.
      intros H.
      sepsimpl.
      exists x1.
      sepsimpl; simpl in *; eauto.
  Qed.
  Hint Immediate equiv_bounds_FElem : ecancel_impl.

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

  Lemma Fp2_list_decomp : forall l, fst_felem l ++ snd_felem l = l.
  Proof.
    intros. cbv [fst_felem snd_felem]. rewrite firstn_skipn. auto.
  Qed.

  Lemma Fp_FElem_to_Fp2_sep : forall px (x : Fp2) m bounds,
      ((FElem F bounds px (fst x)) *
         (FElem F bounds (word.add px felem_offset_word) (snd x)))%sep m
      -> (FElem Fp2 bounds px x m).
  Proof.
    intros.
    cbv [FElem Bignum.Bignum] in *.
    sepsimpl.
    exists (x0 ++ x1).
    sepsimpl.
    unfold feval.
    simpl.
    unfold fst_felem, snd_felem.
    rewrite firstn_app', skipn_app. rewrite H, H2.
    destruct x; auto.
    auto.
    auto.

    destruct bounds.
    simpl in *.
    unfold fst_felem, snd_felem.
    rewrite firstn_app', skipn_app. easy.
    auto.
    auto.
    easy.

    rewrite app_length. rewrite H0, H3. simpl. lia.

    eapply array_append.
    assert (word.add px felem_offset_word =
              (word.add px
                 (word.of_Z
                    (@word.unsigned width _ (word.of_Z (Memory.bytes_per_word width)) *
                       Z.of_nat (Datatypes.length x0)))) ).
    {
      eapply f_equal.
      rewrite word.ring_morph_mul.
      rewrite word.ring_morph_mul.
      rewrite word.of_Z_unsigned.
      rewrite H0. auto.
    }
    rewrite <- H6.
    ecancel_assumption.
  Qed.

  Lemma Fp2_FElem_to_Fp_sep : forall px x m bounds,
    (FElem Fp2 bounds px x m) -> ((FElem F bounds px (fst x)) * (FElem F bounds (word.add px felem_offset_word) (snd x)))%sep m.
  Proof.
    intros.
    cbv [FElem Bignum.Bignum] in *.
    sepsimpl.
    rewrite <- (Fp2_list_decomp x0) in H2.
    eapply array_append in H2.

    exists (fst_felem x0).
    sepsimpl.
    exists (snd_felem x0).
    sepsimpl.

    simpl in H.

    destruct x. inversion H; subst; auto.
    destruct bounds; auto. simpl in *; easy.
    simpl in H0.
    unfold fst_felem.
    rewrite length_firstn; auto.
    lia.

    destruct x. inversion H; subst; auto.
    destruct bounds; auto. simpl in *; easy.
    simpl in H0.
    unfold snd_felem.
    rewrite length_skipn; auto.
    lia.

    eassert ((word.of_Z
                (word.unsigned (word.of_Z (Memory.bytes_per_word width)) *
                   Z.of_nat (Datatypes.length (fst_felem x0)))) = felem_offset_word).
    {
      cbv [fst_felem]. rewrite length_firstn; [| simpl in *; lia].
      rewrite word.ring_morph_mul. rewrite word.of_Z_unsigned.
      rewrite <- word.ring_morph_mul. auto.
    }
    rewrite H3 in H2.

    ecancel_assumption.
  Qed.

  Lemma Fp2_Fp_FElem : forall px x bounds,
    Lift1Prop.iff1
      (FElem Fp2 bounds px x)
      ((FElem F bounds px (fst x)) ⋆ (FElem F  bounds(word.add px felem_offset_word) (snd x))).
  Proof.
    intros; split.
    - apply Fp2_FElem_to_Fp_sep.
    - apply Fp_FElem_to_Fp2_sep.
  Qed.

  Definition expr_2nd_felem (x : Syntax.expr) := expr.op bopname.add x (expr.literal felem_offset).

  Context {Fp2_names : FieldNames Fp2}.

  Definition Fp2_felem_copy : bedrock2.Syntax.func :=
    (felem_copy (F:=Fp2), (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes Fp2) as allocx;
      coq:(cmd.call [] (felem_copy (F:=F)) [expr.var ("allocx"); expr.var ("x")]);
      coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var ("allocx")); expr_2nd_felem (expr.var ("x"))]);
      (* coq:(cmd.call [] (felem_copy (F:=F)) [expr.var ("allocy"); expr.var ("iny")]); *)
      (* coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var ("allocy")); expr_2nd_felem (expr.var ("iny"))]); *)
      (* coq:(cmd.call [] (select_znz (F:=F)) [expr.var "out"; expr.var "c"; expr.var "allocx"; expr.var "allocy"]); *)
      (* coq:(cmd.call [] (select_znz (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "c"; expr_2nd_felem (expr.var "allocx"); expr_2nd_felem (expr.var "allocy")]) *)
      coq:(cmd.call [] (felem_copy (F:=F)) [expr.var "out"; expr.var "allocx"]);
      coq:(cmd.call [] (felem_copy (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "allocx")])
    ))).

  Instance spec_of_Fp2_copy : spec_of (felem_copy (F:=Fp2)) := spec_of_felem_copy (F:=Fp2).

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
      (* coq:(cmd.call [] (select_znz (F:=F)) [expr.var "out"; expr.var "c"; expr.var "inx"; expr.var "iny"]); *)
      (* coq:(cmd.call [] (select_znz (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "c"; expr_2nd_felem (expr.var "inx"); expr_2nd_felem (expr.var "iny")]) *)
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

  Definition Fp2_zero : bedrock2.Syntax.func :=
    (zero (F:=Fp2), (["out"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (zero (F:=F)) [expr.var "out"]);
      coq:(cmd.call [] (zero (F:=F)) [expr_2nd_felem (expr.var "out")])
    ))).

  Instance spec_of_F_zero : spec_of (zero (F:=F)) := nullop_spec null_zero (F:=F).
  Instance spec_of_Fp2_zero : spec_of (zero (F:=Fp2)) := nullop_spec null_zero (F:=Fp2).

  Definition Fp2_one : bedrock2.Syntax.func :=
    (one (F:=Fp2), (["out"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (one (F:=F)) [expr.var "out"]);
      coq:(cmd.call [] (zero (F:=F)) [expr_2nd_felem (expr.var "out")])
    ))).

  Instance spec_of_F_one : spec_of (one (F:=F)) := nullop_spec null_one (F:=F).
  Instance spec_of_Fp2_one : spec_of (one (F:=Fp2)) := nullop_spec null_one (F:=Fp2).

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

  Ltac straightline' :=
    match goal with
    | _ => straightline
    | l := _ : map.rep |- _ => subst l
    | |- exists _, _ => eexists
    | |- _ /\ _ => split
    | |- felem_size_in_bytes _ mod _ = 0 => eapply felem_size_in_bytes_mod
    | |- map.get _ _ = _ => repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same
    end.

  Import Syntax BinInt String List.ListNotations.

  Lemma Fp2_zero_ok : program_logic_goal_for_function! Fp2_zero.
  Proof.
    enter' Fp2_zero.
    clear H0.
    cbv [nullop_spec].
    intros. unfold1_call_goal. cbv match beta delta [call_body].
    rewrite eqb_refl.
    cbv match beta delta [func].

    repeat straightline'.
    straightline_call.
    seprewrite_in Fp2_Fp_FElem H0.
    ecancel_assumption_impl.
    clear dependent mem0.

    repeat straightline'.
    straightline_call.
    ecancel_assumption_impl.
    clear dependent a0.

    repeat straightline'.
    seprewrite Fp2_Fp_FElem.
    ecancel_assumption_impl.
  Qed.

  Lemma Fp2_one_ok : program_logic_goal_for_function! Fp2_one.
  Proof.
    enter' Fp2_one.
    cbv [nullop_spec].
    intros. unfold1_call_goal. cbv match beta delta [call_body].
    rewrite eqb_refl.
    cbv match beta delta [func].

    repeat straightline'.
    straightline_call.
    seprewrite_in Fp2_Fp_FElem H1.
    ecancel_assumption_impl.
    clear dependent mem0.

    repeat straightline'.
    straightline_call.
    ecancel_assumption_impl.
    clear dependent a0.

    repeat straightline'.
    seprewrite Fp2_Fp_FElem.
    ecancel_assumption_impl.
  Qed.

  Lemma Fp2_select_znz_ok : program_logic_goal_for_function! Fp2_select_znz.
  Proof.
    enter' Fp2_select_znz.
    clear H0.
    cbv [spec_of_selectznz] in *.
    intros. unfold1_call_goal. cbv match beta delta [call_body].
    rewrite eqb_refl.
    cbv match beta delta [func].

    repeat straightline'.

    eapply FElem_from_bytes in H8 as [?].
    eapply FElem_from_bytes in H10 as [?].

    collect H0 H5.
    collect H6 Hnew.

    eassert (((_ ⋆ _) ⋆ _) mCombined0).
    {
      do 2 eexists; split; [eauto |]; split; [| apply H10].
      do 2 eexists; split; [eauto |]; split; [| apply H8].
      apply Hnew0.
    }
    simpl in H0.

    clear Hnew0.
    clear dependent mStack0.
    clear dependent mStack.

    straightline_call.
    1: {
      split.
      2: {
        seprewrite_in Fp2_Fp_FElem H0.
        ecancel_assumption.
      }
      eapply sep_assoc in H0.
      eapply sep_and_l_fwd in H0 as [].
      eapply sep_and_l_fwd in H5 as [].

      seprewrite_in Fp2_Fp_FElem H6.
      seprewrite_in Fp2_Fp_FElem H6.
      ecancel_assumption.
    }
    (* from now on, the mem will be a2, so clear previous mem *)
    clear dependent mCombined0.

    repeat straightline'.

    straightline_call.
    1: {
      sepsimpl.
      2: ecancel_assumption.

      eapply sep_assoc in H6.
      eapply sep_comm in H6.
      eapply (sep_assoc _ (FElem Fp2 _ _ _) _) in H6.
      eapply sep_and_l_fwd in H6 as [h1 h2].
      eapply sep_and_l_fwd in h2 as [h2 h3].
      seprewrite_in Fp2_Fp_FElem h3.
      ecancel_assumption.
    }
    clear dependent a2.

    repeat straightline'.

    straightline_call.
    1: {
      sepsimpl.
      2: {
        seprewrite_in Fp2_Fp_FElem H6.
        ecancel_assumption_impl.
      }

      eapply sep_assoc in H6.
      eapply sep_comm in H6.
      eapply (sep_assoc _ (FElem Fp2 _ _ _) _) in H6.
      eapply sep_and_l_fwd in H6 as [h1 h2].
      seprewrite_in Fp2_Fp_FElem h1.
      seprewrite_in Fp2_Fp_FElem h1.
      ecancel_assumption.
    }
    clear dependent a4.

    repeat straightline'.

    straightline_call.
    1: {
      sepsimpl.
      2: ecancel_assumption.

      eapply sep_assoc in H6.
      eapply sep_assoc in H6.
      eapply sep_assoc in H6.
      eapply sep_and_r_fwd in H6 as [h1 h2].
      seprewrite_in Fp2_Fp_FElem h1.
      ecancel_assumption.
    }
    clear dependent a2.

    repeat straightline'.

    straightline_call.
    1: {

      eapply sep_assoc in H6.
      eapply sep_assoc in H6.
      eapply sep_assoc in H6.
      eapply sep_and_r_fwd in H6 as [h1 h2].
      eapply sep_and_r_fwd in h2 as [h2 h3].

      repeat split.

      seprewrite_in Fp2_Fp_FElem h2.
      ecancel_assumption.
      ecancel_assumption.
      ecancel_assumption.
      assumption.
    }
    clear dependent a4.

    repeat straightline'.
    destruct (word.unsigned pc =? 1) eqn:eq.
    (*after destruct*)
    {
      straightline_call.
      1: {
        repeat split.
        ecancel_assumption.
        ecancel_assumption.
        ecancel_assumption.
        assumption.
      }
      clear dependent a2.

      repeat straightline. (*mStack is not in scope in the below proof; should otherwise go through. destruct sep hyp before introducing evars.*)

      rewrite eq in H6.

      eassert (h1 : (FElem _ _ a0 _  * _)%sep a4).
      {
        seprewrite Fp2_Fp_FElem. ecancel_assumption.
      }

      destruct h1 as [mq [mr [h1 [h2 h3]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      eassert (h4 : (FElem _ _ a _  * _)%sep mr).
      {
        seprewrite Fp2_Fp_FElem. ecancel_assumption.
      }
      (* clear H18. *)

      destruct h4 as [mq' [mr' [h4 [h5 h6]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      repeat straightline.
      split; auto.
      split; auto.
      seprewrite Fp2_Fp_FElem.
      ecancel_assumption.
    }
    (*other case for conditional*)
    {
      straightline_call.
      1: {
        repeat split.
        ecancel_assumption.
        ecancel_assumption.
        ecancel_assumption.
        assumption.
      }
      clear dependent a2.

      repeat straightline. (*mStack is not in scope in the below proof; should otherwise go through. destruct sep hyp before introducing evars.*)

      rewrite eq in H6.

      eassert (h1 : (FElem _ _ a0 _  * _)%sep a4).
      {
        seprewrite Fp2_Fp_FElem. ecancel_assumption.
      }

      destruct h1 as [mq [mr [h1 [h2 h3]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      eassert (h4 : (FElem _ _ a _  * _)%sep mr).
      {
        seprewrite Fp2_Fp_FElem. ecancel_assumption.
      }

      destruct h4 as [mq' [mr' [h4 [h5 h6]]]].

      eexists. eexists. split.
      1: {
        eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
      }
      split; [eapply map.split_comm; eauto| ].

      repeat straightline.
      split; auto.
      split; auto.
      seprewrite Fp2_Fp_FElem.
      ecancel_assumption.
    }
  Qed.

  Lemma Fp2_add_ok : program_logic_goal_for_function! Fp2_add.
  Proof.
    enter' Fp2_select_znz.
    clear H0.
    cbv [binop_spec] in *.
    intros. unfold1_call_goal.
    cbv match beta delta [call_body].
    unfold Fp2_add.
    rewrite eqb_refl.
    cbv match beta delta [func].

    repeat straightline'.

    eapply FElem_from_bytes in H7 as [?].
    eapply FElem_from_bytes in H9 as [?].

    collect H0 H5.
    collect H6 Hnew.

    eassert (((_ ⋆ _) ⋆ _) mCombined0).
    {
      do 2 eexists; split; [eauto |]; split; [| apply H9].
      do 2 eexists; split; [eauto |]; split; [| apply H7].
      apply Hnew0.
    }
    simpl in H0.

    clear Hnew0.
    clear dependent mStack0.
    clear dependent mStack.

    straightline_call.
    1: {
      split.
      2: {
        seprewrite_in Fp2_Fp_FElem H0.
        ecancel_assumption.
      }
      eapply sep_assoc in H0.
      eapply sep_and_l_fwd in H0 as [].
      eapply sep_and_l_fwd in H5 as [].

      seprewrite_in Fp2_Fp_FElem H5.
      seprewrite_in Fp2_Fp_FElem H5.
      ecancel_assumption.
    }
    (* from now on, the mem will be a2, so clear previous mem *)
    clear dependent mCombined0.

    repeat straightline'.

    straightline_call.
    1: {
      sepsimpl.
      2: ecancel_assumption.

      eapply sep_assoc in H6.
      eapply sep_comm in H6.
      eapply (sep_assoc _ (FElem Fp2 _ _ _) _) in H6.
      eapply sep_and_l_fwd in H6 as [h1 h2].
      eapply sep_and_l_fwd in h2 as [h2 h3].
      seprewrite_in Fp2_Fp_FElem h2.
      ecancel_assumption.
    }
    clear dependent a2.

    repeat straightline'.

    straightline_call.
    1: {
      sepsimpl.
      2: {
        seprewrite_in Fp2_Fp_FElem H6.
        ecancel_assumption_impl.
      }

      eapply sep_assoc in H6.
      eapply sep_comm in H6.
      eapply (sep_assoc _ (FElem Fp2 _ _ _) _) in H6.
      eapply sep_and_l_fwd in H6 as [h1 h2].
      eapply sep_and_l_fwd in h2 as [h2 h3].
      seprewrite_in Fp2_Fp_FElem h3.
      seprewrite_in Fp2_Fp_FElem h3.
      ecancel_assumption.
    }
    clear dependent a4.

    repeat straightline'.

    straightline_call.
    1: {
      sepsimpl.
      2: ecancel_assumption.

      eapply sep_assoc in H6.
      eapply sep_assoc in H6.
      eapply sep_assoc in H6.
      eapply sep_and_r_fwd in H6 as [h1 h2].
      eapply sep_and_r_fwd in h2 as [h2 h3].
      seprewrite_in Fp2_Fp_FElem h3.
      ecancel_assumption.
    }
    clear dependent a2.

    repeat straightline'.

    straightline_call.
    1: {

      eapply sep_assoc in H6.
      eapply sep_assoc in H6.
      eapply sep_assoc in H6.
      eapply sep_and_r_fwd in H6 as [h1 h2].
      eapply sep_and_r_fwd in h2 as [h2 h3].

      repeat split.

      seprewrite_in Fp2_Fp_FElem h2.
      cbv [bin_xbounds bin_add]. eexists. ecancel_assumption.
      cbv [bin_ybounds bin_add]. eexists. ecancel_assumption.
      seprewrite_in Fp2_Fp_FElem h1.
      ecancel_assumption.
    }
    clear dependent a4.

    repeat straightline'.

    straightline_call.

    1: {

        repeat split.
      cbv [bin_xbounds bin_add]. eexists. ecancel_assumption.
      cbv [bin_ybounds bin_add]. eexists. ecancel_assumption.
        ecancel_assumption.
    }
    clear dependent a2.

    repeat straightline.

    eassert (h1 : (FElem _ _ a0 _  * _)%sep a4).
    {
      seprewrite Fp2_Fp_FElem. ecancel_assumption.
    }

    destruct h1 as [mq [mr [h1 [h2 h3]]]].

    eexists. eexists. split.
    1: {
      eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
    }
    split; [eapply map.split_comm; eauto| ].

    eassert (h4 : (FElem _ _ a _  * _)%sep mr).
    {
      seprewrite Fp2_Fp_FElem. ecancel_assumption.
    }

    destruct h4 as [mq' [mr' [h4 [h5 h6]]]].

    eexists. eexists. split.
    1: {
      eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
    }
    split; [eapply map.split_comm; eauto| ].

    repeat straightline'.
    seprewrite Fp2_Fp_FElem.
    subst out0 x4 x5.
    simpl in *.
    ecancel_assumption.
  Qed.

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
    rewrite eqb_refl.
    cbv match beta delta [func].
    repeat straightline'.

    collect H0 H1.
    collect Hnew H2.

    eapply FElem_from_bytes in H12 as [].
    eapply FElem_from_bytes in H9 as [].
    eapply FElem_from_bytes in H5 as [].
    eapply FElem_from_bytes in H3 as [].

    eassert (((_ * _ * _ * _) * _)%sep mCombined2).
    {
      do 2 eexists; split; [eassumption | split; [| apply H0]].
      do 2 eexists; split; [eassumption | split; [| apply H1]].
      do 2 eexists; split; [eassumption | split; [| apply H2]].
      do 2 eexists; split; [eassumption | split; [| apply H3]].
      apply Hnew0.
    }
    clear dependent mStack.
    clear dependent mStack0.
    clear dependent mStack1.
    clear dependent mStack2.
    clear Hnew0.
    simpl in H5.

    straightline_call.
    1: {
      split.
      2: {
        seprewrite_in Fp2_Fp_FElem H5.
        ecancel_assumption_impl.
      }

      eapply sep_assoc in H5.
      eapply (sep_assoc _ (FElem _ _ a0 _) _)  in H5.
      eapply (sep_assoc _ (FElem _ _ a _) _)  in H5.
      eapply sep_and_l_fwd in H5 as [h1 h2].
      eapply sep_and_l_fwd in h1 as [h1 h3].

      seprewrite_in Fp2_Fp_FElem h1.
      seprewrite_in Fp2_Fp_FElem h1.
      ecancel_assumption.
    }
    clear dependent mCombined2.

    repeat straightline'.

    straightline_call.
    1: {
      split.
      2: ecancel_assumption.

      eassert (h1 : ((fun m : map.rep => _) ⋆ _) _). ecancel_assumption.

      eapply sep_and_l_fwd in h1 as [h1 h2].
      eapply sep_and_l_fwd in h1 as [h1 h3].

      seprewrite_in Fp2_Fp_FElem h1.
      ecancel_assumption.
    }
    clear dependent a4.

    repeat straightline'.

    straightline_call.
    1: {
      seprewrite_in Fp2_Fp_FElem H2.
      split.
      2: ecancel_assumption.

      eassert (h1 : ((fun m : map.rep => _) ⋆ _) _). ecancel_assumption.

      eapply sep_and_l_fwd in h1 as [h1 h2].
      eapply sep_and_l_fwd in h1 as [h1 h3].

      seprewrite_in Fp2_Fp_FElem h3.
      ecancel_assumption.
    }
    clear dependent a6.

    repeat straightline'.

    straightline_call.
    1: {
      split.
      2: ecancel_assumption.

      eassert (h1 : ((fun m : map.rep => _) ⋆ _) _). ecancel_assumption.

      eapply sep_and_l_fwd in h1 as [h1 h2].
      eapply sep_and_l_fwd in h1 as [h1 h3].

      seprewrite_in Fp2_Fp_FElem h3.
      ecancel_assumption.
    }
    clear dependent a4.
    repeat straightline'.

    straightline_call.
    1: {
      simpl in *.
      repeat split.
      3: ecancel_assumption.

      eexists. ecancel_assumption.
      eexists. ecancel_assumption.
    }
    clear dependent a6.

    repeat straightline'.

    straightline_call.
    1: {
      simpl in *.
      repeat split.
      3: ecancel_assumption.

      eexists. ecancel_assumption.
      eexists. ecancel_assumption.
    }
    clear dependent a4.

    repeat straightline'.

    straightline_call.
    1: {
      simpl in *.
      eassert (h1 : ((fun m : map.rep => _) ⋆ _) _). ecancel_assumption.

      eapply sep_and_l_fwd in h1 as [h1 h2].
      eapply sep_and_l_fwd in h1 as [h1 h3].
      repeat split.
      seprewrite_in Fp2_Fp_FElem h2.
      3: {
        seprewrite_in Fp2_Fp_FElem h2.
        ecancel_assumption. }

      eexists. seprewrite equiv_bounds_FElem. ecancel_assumption.
      eexists. seprewrite equiv_bounds_FElem. ecancel_assumption.
    }
    clear dependent a6.

    repeat straightline'.

    straightline_call.
    1: {
      simpl in *.
      repeat split.
      eexists. seprewrite equiv_bounds_FElem. ecancel_assumption.
      eexists. seprewrite equiv_bounds_FElem. ecancel_assumption.
      ecancel_assumption.
    }
    clear dependent a4.

    repeat straightline'.

    straightline_call.
    1: {
      simpl in *.
      repeat split.
      eexists. ecancel_assumption.
      eexists. ecancel_assumption.
      ecancel_assumption_impl.
    }
    clear dependent a6.

    repeat straightline'.

    straightline_call.
    1: {
      simpl in *.
      repeat split.
      eexists. ecancel_assumption.
      eexists. ecancel_assumption.
      ecancel_assumption_impl.
    }
    clear dependent a4.

    repeat straightline'.

    straightline_call.
    1: {
      simpl in *.
      repeat split.
      eexists. seprewrite equiv_bounds_FElem. ecancel_assumption.
      eexists. ecancel_assumption.
      ecancel_assumption_impl.
    }
    clear dependent a6.

    repeat straightline'.

    straightline_call.
    1: {
      simpl in *.
      repeat split.
      eexists. ecancel_assumption.
      eexists. ecancel_assumption.
      ecancel_assumption_impl.
    }
    clear dependent a4.
    sepsimpl.

    repeat straightline.

    let Hstack := (fresh "Hstack") in
    let Hsplit := (fresh "Hsplit") in
    let Hnew := (fresh "Hnew") in
    eassert (Hstack : (FElem _ _ a2 _ * _)%sep a6) by (seprewrite Fp2_Fp_FElem; ecancel_assumption);
    destruct Hstack as [? [? [Hsplit [Hstack' Hnew]]]];
    do 2 eexists; split; [eapply FElem_from_bytes; eexists; eapply drop_bounds_FElem; eauto| split; [eapply map.split_comm; eauto| ]].

    let Hstack := (fresh "Hstack") in
    let Hsplit := (fresh "Hsplit") in
    let Hnew := (fresh "Hnew") in
    eassert (Hstack : (FElem _ _ a1 _ * _)%sep x15) by (seprewrite Fp2_Fp_FElem; ecancel_assumption);
    destruct Hstack as [? [? [Hsplit [Hstack'' Hnew]]]];
    do 2 eexists; split; [eapply FElem_from_bytes; eexists; eapply drop_bounds_FElem; eauto| split; [eapply map.split_comm; eauto| ]].

    let Hstack := (fresh "Hstack") in
    let Hsplit := (fresh "Hsplit") in
    let Hnew := (fresh "Hnew") in
    eassert (Hstack : (FElem F _ a0 _ * _)%sep x17) by ecancel_assumption;
    destruct Hstack as [? [? [Hsplit [Hstack''' Hnew]]]];
    do 2 eexists; split; [eapply FElem_from_bytes; eexists; eapply drop_bounds_FElem; eauto| split; [eapply map.split_comm; eauto| ]].

    let Hstack := (fresh "Hstack") in
    let Hsplit := (fresh "Hsplit") in
    let Hnew := (fresh "Hnew") in
    eassert (Hstack : (FElem F _ a _ * _)%sep x19) by ecancel_assumption;
    destruct Hstack as [? [? [Hsplit [Hstack'''' Hnew]]]];
    do 2 eexists; split; [eapply FElem_from_bytes; eexists; eapply drop_bounds_FElem; eauto| split; [eapply map.split_comm; eauto| ]].

    repeat straightline'.
    simpl in *.
    subst x6 x7 x8 x9 x10 x11 x12 x13 out0.
    unfold mulp2.
    seprewrite Fp2_Fp_FElem.
    simpl.

    eassert (Quad_non_res M_pos = _).
    {
      cbv [Quad_non_res]. assert (Z.pos M_pos mod 4 =? 3 = true) by lia.
      rewrite H0.
      eauto.
    }
    (* rewrite H0. *)
    rewrite F_mul_assoc.
    rewrite <- mul_neg_1.
    rewrite <- mul_equiv.

    seprewrite equiv_bounds_FElem.
    seprewrite equiv_bounds_FElem.
    ecancel_assumption.

    apply M_pos_prime.
    apply M_pos_prime.

    assumption.
    apply M_pos_prime.
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
    enter' Fp2_sub.
    clear H0.
    cbv [binop_spec] in *.
    intros. unfold1_call_goal.
    cbv match beta delta [call_body].
    unfold Fp2_add.
    rewrite eqb_refl.
    cbv match beta delta [func].

    repeat straightline'.

    eapply FElem_from_bytes in H7 as [?].
    eapply FElem_from_bytes in H9 as [?].

    collect H0 H5.
    collect H6 Hnew.

    eassert (((_ ⋆ _) ⋆ _) mCombined0).
    {
      do 2 eexists; split; [eauto |]; split; [| apply H9].
      do 2 eexists; split; [eauto |]; split; [| apply H7].
      apply Hnew0.
    }
    simpl in H0.

    clear Hnew0.
    clear dependent mStack0.
    clear dependent mStack.

    straightline_call.
    1: {
      split.
      2: {
        seprewrite_in Fp2_Fp_FElem H0.
        ecancel_assumption.
      }
      eapply sep_assoc in H0.
      eapply sep_and_l_fwd in H0 as [].
      eapply sep_and_l_fwd in H5 as [].

      seprewrite_in Fp2_Fp_FElem H5.
      seprewrite_in Fp2_Fp_FElem H5.
      ecancel_assumption.
    }
    (* from now on, the mem will be a2, so clear previous mem *)
    clear dependent mCombined0.

    repeat straightline'.

    straightline_call.
    1: {
      sepsimpl.
      2: ecancel_assumption.

      eassert (((fun m => (_ /\ _)) ⋆ _) a2).
      ecancel_assumption.

      eapply sep_and_l_fwd in H0 as [h1 h2].
      eapply sep_and_l_fwd in h2 as [h2 h3].
      seprewrite_in Fp2_Fp_FElem h2.
      ecancel_assumption.
    }
    clear dependent a2.

    repeat straightline'.

    straightline_call.
    1: {
      sepsimpl.
      2: {
        seprewrite_in Fp2_Fp_FElem H6.
        ecancel_assumption_impl.
      }

      eassert (((fun m => (_ /\ _)) ⋆ _) a4).
      ecancel_assumption.
      eapply sep_and_l_fwd in H0 as [h1 h2].
      eapply sep_and_l_fwd in h2 as [h2 h3].
      seprewrite_in Fp2_Fp_FElem h3.
      seprewrite_in Fp2_Fp_FElem h3.
      ecancel_assumption.
    }
    clear dependent a4.

    repeat straightline'.

    straightline_call.
    1: {
      sepsimpl.
      2: ecancel_assumption.

      eassert (((fun m => (_ /\ _)) ⋆ _) a2).
      ecancel_assumption.
      eapply sep_and_l_fwd in H0 as [h1 h2].
      eapply sep_and_l_fwd in h2 as [h2 h3].
      seprewrite_in Fp2_Fp_FElem h3.
      ecancel_assumption.
    }
    clear dependent a2.

    repeat straightline'.

    straightline_call.
    1: {

      eassert (((fun m => (_ /\ _)) ⋆ _) a4).
      ecancel_assumption.
      eapply sep_and_l_fwd in H0 as [h1 h2].
      eapply sep_and_l_fwd in h2 as [h2 h3].

      repeat split.

      seprewrite_in Fp2_Fp_FElem h2.
      simpl. eexists. ecancel_assumption.
      simpl. eexists. ecancel_assumption.
      seprewrite_in Fp2_Fp_FElem h1.
      ecancel_assumption.
    }
    clear dependent a4.

    repeat straightline'.

    straightline_call.

    1: {

        repeat split.
      simpl. eexists. ecancel_assumption.
      simpl. eexists. ecancel_assumption.
        ecancel_assumption.
    }
    clear dependent a2.

    repeat straightline.

    eassert (h1 : (FElem _ _ a0 _  * _)%sep a4).
    {
      seprewrite Fp2_Fp_FElem. ecancel_assumption.
    }

    destruct h1 as [mq [mr [h1 [h2 h3]]]].

    eexists. eexists. split.
    1: {
      eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
    }
    split; [eapply map.split_comm; eauto| ].

    eassert (h4 : (FElem _ _ a _  * _)%sep mr).
    {
      seprewrite Fp2_Fp_FElem. ecancel_assumption.
    }

    destruct h4 as [mq' [mr' [h4 [h5 h6]]]].

    eexists. eexists. split.
    1: {
      eapply FElem_from_bytes. eexists. eapply drop_bounds_FElem. eauto.
    }
    split; [eapply map.split_comm; eauto| ].

    repeat straightline'.
    seprewrite Fp2_Fp_FElem.
    subst out0 x4 x5.
    simpl in *.
    ecancel_assumption.
  Qed.

  Ltac update_mem :=
    match goal with
    | Hsplit : map.split ?comb ?mem ?stack |- _ =>
        match goal with
          Hold_mem : ?p mem,
            Hstack : Memory.anybytes ?a (felem_size_in_bytes _) stack
          |- _ =>
            let x := fresh "x" in
            let Hmem := fresh "Hmem" in
            eapply FElem_from_bytes in Hstack as [x Hstack]
            ; eassert (Hnew_mem : (p ⋆ FElem _ None a x) comb) by (eexists; eauto)
            ; clear dependent mem
            ; clear dependent stack
            ; rename Hnew_mem into Hmem
        end
    end.

   Ltac collect2 H1 H2 := let Hnew := (fresh "Hnew") in
     eassert (Hnew : id (fun m => (_ m) /\ (_ m)) _) by (cbv [id]; repeat split; [eapply H1| eapply H2]); clear H1 H2.

  Ltac sep_and_fwd :=
    cbn [id] in *;
    match goal with
    | H : context[fun m => _] |- _ =>
        let Hnew1 := fresh "Hmem" in
        let Hnew2 := fresh "Hmem" in
        eassert (Hnew1 : ((fun m => _) ⋆ _) _) by ecancel_assumption;
        eapply sep_and_l_fwd in Hnew1 as [Hnew1 Hnew2];
        clear H
    end.

  Lemma Fp2_felem_copy_ok : program_logic_goal_for_function! Fp2_felem_copy.
  Proof.
    enter' Fp2_felem_copy.
    clear H0.
    cbv [spec_of_felem_copy] in *.
    intros. unfold1_call_goal.
    cbv match beta delta [call_body].
    (* unfold Fp2_felem_copy. *)
    rewrite eqb_refl.
    cbv match beta delta [func].

    destruct H0.
    collect2 H0 H3.
    repeat straightline'.
    update_mem.

    straightline_call.
    sepsimpl.
    {
      sep_and_fwd.
      seprewrite_in Fp2_Fp_FElem Hmem0.
      seprewrite_in Fp2_Fp_FElem Hmem0.
      seprewrite_in Fp2_Fp_FElem Hmem0.
      ecancel_assumption_impl.
    }
    seprewrite_in Fp2_Fp_FElem Hmem.
    ecancel_assumption_impl.
    clear dependent mCombined.

    repeat straightline'.
    straightline_call.
    sepsimpl.
    {
      sep_and_fwd.
      seprewrite_in Fp2_Fp_FElem Hmem.
      seprewrite_in Fp2_Fp_FElem Hmem.
      ecancel_assumption_impl.
    }
    (* seprewrite_in Fp2_Fp_FElem H4. *)
    ecancel_assumption_impl.
    clear dependent a1.

    repeat straightline'.
    straightline_call.
    sepsimpl.
    sep_and_fwd.
    seprewrite_in Fp2_Fp_FElem Hmem.
    seprewrite_in Fp2_Fp_FElem Hmem.
    ecancel_assumption_impl.

    sep_and_fwd.
    seprewrite_in Fp2_Fp_FElem Hmem0.
    ecancel_assumption_impl.
    clear dependent a3.

    repeat straightline'.
    straightline_call.
    sepsimpl.
    ecancel_assumption_impl.
    ecancel_assumption_impl.
    clear dependent a1.

    repeat straightline.

    eassert (h1 : (_ ⋆ (FElem _ _ a (fst x) ⋆ FElem _ _ (word.add a _) (snd x)))%sep a3).
    {
      ecancel_assumption.
    }
    destruct h1 as [mq [mr [h1 [h2 h3]]]].
    (* destruct h3 as [mq' [mr' [h3 [h4 h5]]]]. *)

    eexists. eexists.
    split; [|split].
    2: eassumption.

    eapply FElem_from_bytes.
    eexists. eapply drop_bounds_FElem. eapply Fp2_Fp_FElem. eassumption.

    repeat straightline'.

    seprewrite Fp2_Fp_FElem.
    ecancel_assumption_impl.
  Qed.
End Fp2.
