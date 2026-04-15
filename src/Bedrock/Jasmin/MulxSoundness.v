(** * MulxSoundness — scaffolding for [lower_mulx_pairs] soundness.
 *
 * Status (2026-04-15): Phase 3 progress — semantic foundation fixed
 * in [ExprBridge.v] (word.mulhuu in eval_jexpr) and [PolishProofs.v]
 * (jeval_mulx rule uses word.mulhuu for hi).  This file provides
 * the well-formedness predicate [wf_mulx_*] and the foundational
 * [cmd_to_list_sound] chain for lifting [jeval] (JCseq) to
 * [jeval_list] (list jasmin_cmd).
 *
 * Remaining (Phase 3 plan):
 *   - [cmd_touches_preserves_var] : if [cmd_touches x c = false] and
 *     [jeval e c e'] then [e' x = e x].
 *   - [jeval_list_unaffected] : lift to lists.
 *   - [scan_mulx_pairs_valid] : every match satisfies operand
 *     equivalence under def_map.
 *   - [rewrite_mulx_one_match_sound] : rewriting one match preserves
 *     [jeval_list].
 *   - [lower_mulx_pairs_list_correct] : full theorem.
 *   - Replace identity-case Qed in [PolishProofs.v].
 *)

Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Properties.
From Stdlib Require Import ZArith String Bool List Lia.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Crypto.Bedrock.Jasmin.Core.
Require Import Crypto.Bedrock.Jasmin.ExprBridge.

(* ================================================================ *)
(* Well-formedness predicates                                       *)
(* ================================================================ *)

Section Predicates.

  (** True if variable [x] appears as [JEvar x] in expression [e]. *)
  Fixpoint expr_reads (x : string) (e : jasmin_expr) : bool :=
    match e with
    | JEvar y => String.eqb x y
    | JElit _ => false
    | JEadd a b | JEsub a b | JEmul a b | JEmulhuu a b
    | JEand a b | JEor  a b | JExor a b
    | JEshr a b | JEshl a b | JEltu a b | JEeq a b =>
        expr_reads x a || expr_reads x b
    | JEload base _ => expr_reads x base
    end.

  (** True if command [c] reads or writes variable [x] anywhere.
      Recurs into JCseq/JCif/JCwhile/JCdecl. *)
  Fixpoint cmd_touches (x : string) (c : jasmin_cmd) : bool :=
    match c with
    | JCskip => false
    | JCseq c1 c2 => cmd_touches x c1 || cmd_touches x c2
    | JCset y e => String.eqb x y || expr_reads x e
    | JCstore base _ v => expr_reads x base || expr_reads x v
    | JCcall _ args => existsb (expr_reads x) args
    | JCif e ct cf => expr_reads x e || cmd_touches x ct || cmd_touches x cf
    | JCwhile e body => expr_reads x e || cmd_touches x body
    | JCdecl _ _ body => cmd_touches x body
    | JCadd_flags cf r a b =>
        String.eqb x cf || String.eqb x r
        || expr_reads x a || expr_reads x b
    | JCadcx co r a b ci =>
        String.eqb x co || String.eqb x r || String.eqb x ci
        || expr_reads x a || expr_reads x b
    | JCmulx h l a b =>
        String.eqb x h || String.eqb x l
        || expr_reads x a || expr_reads x b
    | JCsub_flags cf r a b =>
        String.eqb x cf || String.eqb x r
        || expr_reads x a || expr_reads x b
    | JCsbb co r a b ci =>
        String.eqb x co || String.eqb x r || String.eqb x ci
        || expr_reads x a || expr_reads x b
    end.

  (** No statement at positions strictly between [mul_idx] and
      [mulhuu_idx] touches [hi].  [n] is the running position. *)
  Fixpoint stmts_between_safe (hi : string)
      (mul_idx mulhuu_idx n : nat) (cs : list jasmin_cmd) : bool :=
    match cs with
    | nil => true
    | c :: rest =>
        let is_between := Nat.ltb mul_idx n && Nat.ltb n mulhuu_idx in
        (if is_between then negb (cmd_touches hi c) else true)
        && stmts_between_safe hi mul_idx mulhuu_idx (S n) rest
    end.

  (** Every pair returned by [scan_mulx_pairs] must satisfy the safety
      condition. *)
  Definition wf_mulx_list (cs : list jasmin_cmd) : bool :=
    forallb (fun m =>
               let '(mul_idx, mulhuu_idx, hi, _, _, _) := m in
               stmts_between_safe hi mul_idx mulhuu_idx 0 cs)
            (scan_mulx_pairs cs).

  Fixpoint wf_mulx_cmd (c : jasmin_cmd) : bool :=
    match c with
    | JCseq _ _ => wf_mulx_list (cmd_to_list c)
    | JCif _ ct cf => wf_mulx_cmd ct && wf_mulx_cmd cf
    | JCwhile _ body => wf_mulx_cmd body
    | JCdecl _ _ body => wf_mulx_cmd body
    | _ => true
    end.

End Predicates.

(* ================================================================ *)
(* List-level big-step semantics + cmd_to_list soundness            *)
(* ================================================================ *)

Section WithWordCmd.

  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {word_ok : word.ok word}.

  (** A variable environment.  Mirror of [PolishProofs.env]. *)
  Definition env := string -> word.

  Definition update (e : env) (x : string) (w : word) : env :=
    fun y => if String.eqb y x then w else e y.

  Lemma update_self : forall e x, update e x (e x) = e.
  Proof.
    intros. apply functional_extensionality. intros y.
    unfold update. destruct (String.eqb y x) eqn:H; [|reflexivity].
    apply String.eqb_eq in H. subst. reflexivity.
  Qed.

  (** Big-step relational semantics for [jasmin_cmd].  Mirror of
      [PolishProofs.jeval] so this file can prove its lemmas
      standalone; [PolishProofs.v] imports [MulxSoundness] and
      identifies the two (they are definitionally equal). *)
  Inductive jeval : env -> jasmin_cmd -> env -> Prop :=
  | jeval_skip : forall e, jeval e JCskip e
  | jeval_seq : forall e1 e2 e3 c1 c2,
      jeval e1 c1 e2 -> jeval e2 c2 e3 ->
      jeval e1 (JCseq c1 c2) e3
  | jeval_set : forall e x ex w,
      eval_jexpr e ex = Some w ->
      jeval e (JCset x ex) (update e x w)
  | jeval_decl : forall e x ty body e',
      jeval e body e' ->
      jeval e (JCdecl x ty body) e'
  | jeval_if_true : forall e econd ct cf w e',
      eval_jexpr e econd = Some w ->
      w <> word.of_Z 0 ->
      jeval e ct e' ->
      jeval e (JCif econd ct cf) e'
  | jeval_if_false : forall e econd ct cf e',
      eval_jexpr e econd = Some (word.of_Z 0) ->
      jeval e cf e' ->
      jeval e (JCif econd ct cf) e'
  | jeval_while_false : forall e econd body,
      eval_jexpr e econd = Some (word.of_Z 0) ->
      jeval e (JCwhile econd body) e
  | jeval_while_true : forall e e' e'' econd body w,
      eval_jexpr e econd = Some w ->
      w <> word.of_Z 0 ->
      jeval e body e' ->
      jeval e' (JCwhile econd body) e'' ->
      jeval e (JCwhile econd body) e''
  | jeval_store : forall e base off v vbase vv,
      eval_jexpr e base = Some vbase ->
      eval_jexpr e v = Some vv ->
      jeval e (JCstore base off v) e
  | jeval_call : forall e f args,
      jeval e (JCcall f args) e
  | jeval_add_flags : forall e cf r a b va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCadd_flags cf r a b)
        (update (update e cf (word.of_Z 0)) r (word.add va vb))
  | jeval_adcx : forall e co r a b ci va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCadcx co r a b ci)
        (update (update e co (word.of_Z 0)) r (word.add va vb))
  | jeval_mulx : forall e h l a b va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCmulx h l a b)
        (update (update e h (word.mulhuu va vb)) l (word.mul va vb))
  | jeval_sub_flags : forall e cf r a b va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCsub_flags cf r a b)
        (update (update e cf (word.of_Z 0)) r (word.sub va vb))
  | jeval_sbb : forall e co r a b ci va vb,
      eval_jexpr e a = Some va ->
      eval_jexpr e b = Some vb ->
      jeval e (JCsbb co r a b ci)
        (update (update e co (word.of_Z 0)) r (word.sub va vb))
  .

  (** List-level big-step evaluation. *)
  Inductive jeval_list : env -> list jasmin_cmd -> env -> Prop :=
  | jeval_list_nil  : forall e, jeval_list e nil e
  | jeval_list_cons : forall e e1 e' c cs,
      jeval e c e1 -> jeval_list e1 cs e' ->
      jeval_list e (c :: cs) e'.

  (** Splitting [jeval_list] at an append boundary. *)
  Lemma jeval_list_app :
    forall cs1 cs2 e e',
      jeval_list e (cs1 ++ cs2) e' <->
      exists em, jeval_list e cs1 em /\ jeval_list em cs2 e'.
  Proof.
    induction cs1 as [|c cs1 IH]; intros cs2 e e'; simpl.
    - split.
      + intros H. exists e. split; [constructor | exact H].
      + intros [em [Hl Hr]]. inversion Hl; subst. exact Hr.
    - split.
      + intros H. inversion H as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
        apply IH in Hcs as [em' [Hl Hr]].
        exists em'. split; [econstructor; eassumption | exact Hr].
      + intros [em [Hl Hr]].
        inversion Hl as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
        econstructor; [eassumption | apply IH; eauto].
  Qed.

  (** Helper for singleton-list cases: [jeval env1 c env2] iff
      [jeval_list env1 [c] env2]. *)
  Lemma jeval_singleton_iff : forall c env1 env2,
      jeval env1 c env2 <-> jeval_list env1 (c :: nil) env2.
  Proof.
    intros c env1 env2. split.
    - intros H. econstructor; [exact H | constructor].
    - intros H. inversion H as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
      inversion Hcs; subst. exact Hc.
  Qed.

  (** Flattening a JCseq-chain into a list preserves [jeval].
      All jasmin_cmd cases covered. *)
  Theorem cmd_to_list_sound :
    forall c env1 env2,
      jeval env1 c env2 <-> jeval_list env1 (cmd_to_list c) env2.
  Proof.
    induction c; intros env1 env2; simpl;
      try apply jeval_singleton_iff.
    - (* JCskip *)
      split.
      + intros H. inversion H; subst. constructor.
      + intros H. inversion H; subst. constructor.
    - (* JCseq *)
      split.
      + intros H. inversion H as [|e1' e2' e3' c1'' c2'' H1 H2|
                                  | | | | | | | | | | | |]; subst.
        apply IHc1 in H1. apply IHc2 in H2.
        apply jeval_list_app. eauto.
      + intros H. apply jeval_list_app in H as [em [Hl Hr]].
        apply IHc1 in Hl. apply IHc2 in Hr.
        econstructor; eassumption.
  Qed.

  (** The inverse direction: wrapping a list with [fold_right JCseq JCskip]. *)
  Theorem list_to_cmd_sound :
    forall cs e e',
      jeval_list e cs e' <-> jeval e (list_to_cmd cs) e'.
  Proof.
    induction cs as [|c cs IH]; intros e e'; unfold list_to_cmd; simpl.
    - split.
      + intros H. inversion H; subst. constructor.
      + intros H. inversion H; subst. constructor.
    - split.
      + intros H.
        inversion H as [| e0 e1 e'0 c0 cs0 Hc Hcs ]; subst.
        econstructor; [eassumption|].
        apply IH in Hcs. fold (list_to_cmd cs) in Hcs. exact Hcs.
      + intros H.
        inversion H; subst.
        econstructor; [eassumption|].
        match goal with
        | H : jeval _ _ _ |- _ =>
            let Hj := fresh in
            apply IH in H as Hj; exact Hj
        end.
  Qed.

  (* ================================================================ *)
  (* Remaining Phase 3 proof obligations (stated, proofs deferred)    *)
  (* ================================================================ *)

  (** Helper: [update e x v y = e y] when [y ≠ x]. *)
  Lemma update_other : forall e x v y,
    String.eqb y x = false -> update e x v y = e y.
  Proof.
    intros e x v y H. unfold update. rewrite H. reflexivity.
  Qed.

  (** If a command doesn't touch [x], evaluating it preserves [x]'s
      value.  Proof: structural induction on [jeval], using [update_other]
      to see through writes to other variables. *)
  Theorem cmd_touches_preserves_var :
    forall c e e' x,
      cmd_touches x c = false ->
      jeval e c e' ->
      e' x = e x.
  Proof.
    intros c e e' x Hnt H. revert x Hnt.
    induction H; intros y Hnt; simpl in Hnt.
    - (* JCskip *) reflexivity.
    - (* JCseq *)
      apply orb_false_iff in Hnt as [A B].
      specialize (IHjeval1 _ A).
      specialize (IHjeval2 _ B).
      congruence.
    - (* JCset *)
      apply orb_false_iff in Hnt as [A _].
      apply update_other. exact A.
    - (* JCdecl *) apply IHjeval. exact Hnt.
    - (* JCif_true *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [_ A].
      apply IHjeval. exact A.
    - (* JCif_false *)
      apply orb_false_iff in Hnt as [_ B].
      apply IHjeval. exact B.
    - (* JCwhile_false *) reflexivity.
    - (* JCwhile_true *)
      assert (Hnt' := Hnt).
      apply orb_false_iff in Hnt as [_ B].
      specialize (IHjeval1 _ B).
      specialize (IHjeval2 _ Hnt').
      congruence.
    - (* JCstore *) reflexivity.
    - (* JCcall *) reflexivity.
    - (* JCadd_flags *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [Acf Ar].
      rewrite update_other by exact Ar.
      apply update_other. exact Acf.
    - (* JCadcx *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [Aco Ar].
      rewrite update_other by exact Ar.
      apply update_other. exact Aco.
    - (* JCmulx *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [Ah Al].
      rewrite update_other by exact Al.
      apply update_other. exact Ah.
    - (* JCsub_flags *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [Acf Ar].
      rewrite update_other by exact Ar.
      apply update_other. exact Acf.
    - (* JCsbb *)
      apply orb_false_iff in Hnt as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [P _].
      apply orb_false_iff in P as [Aco Ar].
      rewrite update_other by exact Ar.
      apply update_other. exact Aco.
  Qed.

  (** All-statements version: if no statement in the list touches [x],
      then [x]'s value is preserved by [jeval_list]. *)
  Theorem jeval_list_unaffected :
    forall cs e e' x,
      forallb (fun c => negb (cmd_touches x c)) cs = true ->
      jeval_list e cs e' ->
      e' x = e x.
  Proof.
    induction cs as [|c cs IH]; intros e e' x Hall Hev.
    - inversion Hev; subst. reflexivity.
    - simpl in Hall. apply andb_prop in Hall as [Hc Hrest].
      apply Bool.negb_true_iff in Hc.
      inversion Hev as [| e0 e1 e'0 c0 cs0 Hec Hecs ]; subst.
      rewrite (IH _ _ x Hrest Hecs).
      apply cmd_touches_preserves_var with (c := c); assumption.
  Qed.

  (** Range lift: no statement strictly between [mul_idx] and [mulhuu_idx]
      touches [hi], so [hi]'s value is preserved across the subrange.
      Stated as a conjecture — the exact statement needs list-indexing
      machinery (nth, skipn) that's straightforward but adds ~40 lines. *)
  Conjecture jeval_list_unaffected_range :
    forall (cs : list jasmin_cmd) (mul_idx mulhuu_idx : nat)
           (hi : string) (e e' : env),
      stmts_between_safe hi mul_idx mulhuu_idx 0 cs = true ->
      jeval_list e cs e' ->
      (* Middle sub-range is hi-preserving.  Full statement requires
         skipn/firstn indexing; placeholder True for now. *)
      True.

  (** Every tuple [(mul_idx, mulhuu_idx, hi, lo, a, b)] from
      [scan_mulx_pairs cs] satisfies: at [mul_idx] the list has
      [JCset lo (JEmul a' b')], at [mulhuu_idx] it has
      [JCset hi (JEmulhuu a'' b'')], and [equiv_cp m_k a a'],
      [equiv_cp m_k b b'], [equiv_cp m_k a a''], [equiv_cp m_k b b'']
      under the running [def_map] [m_k].  Statement left as informal;
      the scan is traceable by induction on the scan_aux invariant. *)
  Conjecture scan_mulx_pairs_valid :
    forall (cs : list jasmin_cmd),
      (* see Phase 3c remaining plan in
         project_phase3_mulx_soundness.md *)
      True.

  (** Rewriting a single match preserves [jeval_list] under
      [wf_mulx_list]. *)
  Conjecture rewrite_mulx_one_match_sound :
    forall (cs : list jasmin_cmd) (mul_idx mulhuu_idx : nat)
           (hi lo : string) (a b : jasmin_expr) (e e' : env),
      stmts_between_safe hi mul_idx mulhuu_idx 0 cs = true ->
      jeval_list e cs e' ->
      (* let cs' := replace at mul_idx with JCmulx hi lo a b,
                   replace at mulhuu_idx with JCskip in cs *)
      (* jeval_list e cs' e' *)
      True.

  (** Full soundness: [lower_mulx_pairs] preserves [jeval_list]. *)
  Conjecture lower_mulx_pairs_list_correct :
    forall cs e e',
      wf_mulx_list cs = true ->
      jeval_list e cs e' ->
      jeval_list e (lower_mulx_pairs cs) e'.

End WithWordCmd.
