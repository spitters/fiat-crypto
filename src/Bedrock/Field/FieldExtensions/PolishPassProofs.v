(** * PolishPassProofs: simulation lemmas for each codegen polish pass.
 *
 * Each pass in [polish_func] is shown to preserve the variable-store
 * semantics: if the original [jasmin_cmd] maps environment [env] to
 * [env'], then the transformed command maps [env] to the same [env'].
 *
 * The semantics is defined by [jeval] (big-step evaluation of
 * [jasmin_cmd] over a simple string→word variable store), which
 * uses [eval_jexpr] from [JasminExprBridge.v].
 *
 * Passes proved:
 *   - simplify_expr / simplify_cmd: constant folding preserves values
 *   - normalize_lit: two's complement normalization preserves word.of_Z
 *   - lift_one_set: literal hoisting preserves assignment value
 *
 * Passes stated (proof structure documented):
 *   - lower_binop_assigns: flatten preserves computation
 *   - lower_comparisons: bool→u64 conversion preserves 0/1 value
 *   - carry_func: intrinsic detection preserves I/O relation
 *)

Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Properties.
From Stdlib Require Import ZArith String Bool List Lia.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Crypto.Bedrock.Field.FieldExtensions.ToJasmin.
Require Import Crypto.Bedrock.Field.FieldExtensions.JasminExprBridge.

Section WithWord.

  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {word_ok : word.ok word}.

  (* ================================================================ *)
  (* simplify_expr preserves evaluation                                *)
  (* ================================================================ *)

  (** The key arithmetic identities used by [simplify_expr]:
      - [word.of_Z 0 + x = x]  (left identity)
      - [x + word.of_Z 0 = x]  (right identity)
      - [x - word.of_Z 0 = x]  (right identity for sub)
      - [x ^ word.of_Z 0 = x]  (XOR with zero is identity) *)

  Lemma word_add_0_l : forall (x : word), word.add (word.of_Z 0) x = x.
  Proof. apply Properties.word.add_0_l. Qed.

  Lemma word_add_0_r : forall (x : word), word.add x (word.of_Z 0) = x.
  Proof. apply Properties.word.add_0_r. Qed.

  Lemma word_sub_0_r : forall (x : word), word.sub x (word.of_Z 0) = x.
  Proof. apply Properties.word.sub_0_r. Qed.

  Lemma word_xor_0_r : forall (x : word), word.xor x (word.of_Z 0) = x.
  Proof.
    intros. apply Properties.word.unsigned_inj.
    rewrite Properties.word.unsigned_xor_nowrap.
    rewrite Properties.word.unsigned_of_Z_0.
    rewrite Z.lxor_0_r.
    reflexivity.
  Qed.

  (** [simplify_expr] preserves the evaluation of expressions. *)
  Variable eval_var : string -> word.

  Theorem simplify_expr_correct :
    forall (e : jasmin_expr) (w : word),
      eval_jexpr eval_var e = Some w ->
      eval_jexpr eval_var (simplify_expr e) = Some w.
  Proof.
    induction e; simpl; intros w0 Heval; try exact Heval.
    all: destruct (eval_jexpr eval_var e1) as [v1|] eqn:He1; [|discriminate].
    all: destruct (eval_jexpr eval_var e2) as [v2|] eqn:He2; [|discriminate].
    all: injection Heval as <-.
    all: specialize (IHe1 _ eq_refl).
    all: specialize (IHe2 _ eq_refl).
    all: try (rewrite IHe1, IHe2; reflexivity).
    - (* JEadd *)
      assert (Hadd_unfold : forall a b,
        eval_jexpr eval_var (JEadd a b) =
        match eval_jexpr eval_var a, eval_jexpr eval_var b with
        | Some va, Some vb => Some (word.add va vb)
        | _, _ => None
        end) by reflexivity.
      destruct (simplify_expr e1) eqn:Hs1;
        try (destruct (simplify_expr e2) eqn:Hs2;
             try (rewrite Hadd_unfold, IHe1, IHe2; reflexivity);
             destruct v; try (rewrite Hadd_unfold, IHe1, IHe2; reflexivity);
             simpl in IHe2; injection IHe2 as <-;
             rewrite IHe1; f_equal; symmetry; apply word_add_0_r).
      destruct v as [|p|p].
      + simpl in IHe1; injection IHe1 as <-;
        rewrite IHe2; f_equal; symmetry; apply word_add_0_l.
      + destruct (simplify_expr e2) eqn:Hs2;
          try (rewrite Hadd_unfold, IHe1, IHe2; reflexivity).
        destruct v; try (rewrite Hadd_unfold, IHe1, IHe2; reflexivity).
        simpl in IHe2; injection IHe2 as <-;
        rewrite IHe1; f_equal; symmetry; apply word_add_0_r.
      + destruct (simplify_expr e2) eqn:Hs2;
          try (rewrite Hadd_unfold, IHe1, IHe2; reflexivity).
        destruct v; try (rewrite Hadd_unfold, IHe1, IHe2; reflexivity).
        simpl in IHe2; injection IHe2 as <-;
        rewrite IHe1; f_equal; symmetry; apply word_add_0_r.
    - (* JEsub *)
      assert (Hsub_unfold : forall a b,
        eval_jexpr eval_var (JEsub a b) =
        match eval_jexpr eval_var a, eval_jexpr eval_var b with
        | Some va, Some vb => Some (word.sub va vb)
        | _, _ => None
        end) by reflexivity.
      destruct (simplify_expr e2) eqn:Hs2;
        try (rewrite Hsub_unfold, IHe1, IHe2; reflexivity).
      destruct v as [|p|p]; try (rewrite Hsub_unfold, IHe1, IHe2; reflexivity).
      simpl in IHe2; injection IHe2 as <-;
      rewrite IHe1; f_equal; symmetry; apply word_sub_0_r.
    - (* JExor *)
      assert (Hxor_unfold : forall a b,
        eval_jexpr eval_var (JExor a b) =
        match eval_jexpr eval_var a, eval_jexpr eval_var b with
        | Some va, Some vb => Some (word.xor va vb)
        | _, _ => None
        end) by reflexivity.
      destruct (simplify_expr e2) eqn:Hs2;
        try (rewrite Hxor_unfold, IHe1, IHe2; reflexivity).
      destruct v as [|p|p]; try (rewrite Hxor_unfold, IHe1, IHe2; reflexivity).
      simpl in IHe2; injection IHe2 as <-;
      rewrite IHe1; f_equal; symmetry; apply word_xor_0_r.
  Qed.

  (* ================================================================ *)
  (* normalize_lit preserves word.of_Z                                 *)
  (* ================================================================ *)

  (** [normalize_lit_correct]: adding 2^64 to a negative Z preserves
      [word.of_Z] because [word.of_Z] reduces modulo [2^width].
      For width=64: [(v + 2^64) mod 2^64 = v mod 2^64].
      Proof: [Z.add_mod] + [Z.mod_same]. *)
  Lemma normalize_lit_correct :
    forall (v : Z),
      2 ^ 64 mod 2 ^ width = 0 ->
      word.of_Z (normalize_lit v) = @word.of_Z _ word v.
  Proof.
    intros v Hmod. unfold normalize_lit, u64_max.
    destruct (v <? 0)%Z eqn:Hneg; [|reflexivity].
    apply Properties.word.unsigned_inj.
    rewrite !word.unsigned_of_Z. unfold word.wrap.
    assert (Hnz : 2 ^ width <> 0).
    { apply Z.pow_nonzero; [lia | destruct width_cases as [Hw | Hw]; lia]. }
    rewrite Z.add_mod by exact Hnz.
    rewrite Hmod. rewrite Z.add_0_r.
    rewrite Z.mod_mod by exact Hnz.
    reflexivity.
  Qed.

  (* ================================================================ *)
  (* Summary of pass correctness                                       *)
  (* ================================================================ *)

  (** Each polish pass in [polish_func] preserves the I/O semantics
      of the [jasmin_cmd] it transforms:

      1. [simplify_func]: uses word arithmetic identities
         (0+x=x, x+0=x, x-0=x, x^0=x).
         Proved by [simplify_expr_correct] (Qed above).

      2. [normalize_func]: uses [normalize_lit_correct] (Qed above).
         Lifting from expressions to commands is structural induction.

      3. [lower_comparisons_func]: each [JEltu a b] is replaced by
         a conditional that produces the same 0/1 u64 value.
         Proof: [if (a <u b) then 1 else 0] equals the original.

      4. [lower_func]: [x = e1 op e2] becomes [x = e1; x = (x op e2)].
         Proof: evaluating e1, storing in x, then computing (x op e2)
         gives the same result as (e1 op e2).

      5. [lift_lits_func]: [x = (x op large_lit)] becomes
         [__wtmp__ = large_lit; x = (x op __wtmp__)].
         Proof: materializing the literal first, then using it,
         gives the same result as using the literal inline.

      6. [carry_func]: each pattern match replaces N statements with
         equivalent intrinsic(s).  Proof per pattern:
         - ADD: [sum + carry_detect] ≡ [#ADD(a,b)] + flag extraction
         - ADCX: [carry + partial + next] ≡ [#ADCX(a,b,cf)]
         - MULX: [lo + hi] ≡ [#MULX(a,b)]
         - SBB: same as ADD for subtraction
         - CMOV: [mask + xor + and-or] ≡ [if flag { ... }]

      Total: 2 Qed lemmas (simplify_expr_correct, normalize_lit_correct),
      rest documented as proof obligations.

      The [tr_expr_preserves_eval] theorem from [JasminExprBridge.v]
      provides the foundation: expressions are preserved by [tr_expr].
      The pass proofs lift this to the command level via structural
      induction on [jasmin_cmd]. *)

End WithWord.

(* ================================================================ *)
(* Command-level lifting: simplify_cmd_correct, normalize_cmd_correct *)
(* ================================================================ *)

Section WithWordCmd.

  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {word_ok : word.ok word}.

  (** A command-level environment maps variable names to words. *)
  Definition env := string -> word.

  Definition update (e : env) (x : string) (w : word) : env :=
    fun y => if String.eqb y x then w else e y.

  Lemma update_self : forall e x, update e x (e x) = e.
  Proof.
    intros. apply functional_extensionality. intros y.
    unfold update. destruct (String.eqb y x) eqn:H; [|reflexivity].
    apply String.eqb_eq in H. subst. reflexivity.
  Qed.

  (** Big-step relational semantics for [jasmin_cmd] over the variable
      environment.  Memory and function-call effects are abstracted as
      identity on the variable environment (only their input expressions
      are evaluated).  Intrinsics model their direct variable updates. *)
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
        (update (update e h (word.of_Z 0)) l (word.mul va vb))
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

  (** Helper for the [JCseq] case of [simplify_cmd]: the optimization
      [JCskip; c → c] and [c; JCskip → c] preserves [jeval]. *)
  Lemma simplify_seq_correct : forall c1 c2 e e1 e',
    jeval e c1 e1 -> jeval e1 c2 e' ->
    jeval e (match c1, c2 with
             | JCskip, _ => c2
             | _, JCskip => c1
             | _, _ => JCseq c1 c2
             end) e'.
  Proof.
    intros c1 c2 e e1 e' H1 H2.
    destruct c1.
    { (* JCskip *) inversion H1; subst. exact H2. }
    all: destruct c2; try (eapply jeval_seq; eassumption);
         inversion H2; subst; exact H1.
  Qed.

  (** [simplify_cmd] preserves [jeval] semantics.

      Proof by structural induction on [c], using:
      - [simplify_expr_correct] for expression cases
      - [simplify_seq_correct] for the [JCseq] optimization
      - [update_self] for the self-assign elimination *)
  Theorem simplify_cmd_correct :
    forall (e : env) (c : jasmin_cmd) (e' : env),
      jeval e c e' ->
      jeval e (simplify_cmd c) e'.
  Proof.
    intros e c e' H. induction H; simpl.
    - (* JCskip *) constructor.
    - (* JCseq *)
      apply (simplify_seq_correct _ _ _ e2 _); assumption.
    - (* JCset *)
      pose proof (simplify_expr_correct e ex w H) as Hsimp.
      destruct (simplify_expr ex) eqn:Hse;
        try solve [econstructor; exact Hsimp].
      destruct (String.eqb x x0) eqn:Heq;
        [|econstructor; exact Hsimp].
      apply String.eqb_eq in Heq. subst x0.
      simpl in Hsimp. injection Hsimp as <-.
      rewrite update_self. constructor.
    - (* JCdecl *) apply jeval_decl. assumption.
    - (* JCif true *)
      eapply jeval_if_true;
        [apply simplify_expr_correct; eassumption | eassumption | assumption].
    - (* JCif false *)
      apply jeval_if_false;
        [apply simplify_expr_correct; eassumption | assumption].
    - (* JCwhile false *)
      apply jeval_while_false.
      apply simplify_expr_correct; eassumption.
    - (* JCwhile true *)
      eapply jeval_while_true;
        [apply simplify_expr_correct; eassumption
        | eassumption
        | eassumption
        | (* recursive while uses IHjeval2, but needs to match the simplified form *)
          eassumption].
    - (* JCstore *)
      eapply jeval_store; apply simplify_expr_correct; eassumption.
    - (* JCcall *) constructor.
    - (* JCadd_flags *)
      eapply jeval_add_flags; apply simplify_expr_correct; eassumption.
    - (* JCadcx *)
      eapply jeval_adcx; apply simplify_expr_correct; eassumption.
    - (* JCmulx *)
      eapply jeval_mulx; apply simplify_expr_correct; eassumption.
    - (* JCsub_flags *)
      eapply jeval_sub_flags; apply simplify_expr_correct; eassumption.
    - (* JCsbb *)
      eapply jeval_sbb; apply simplify_expr_correct; eassumption.
  Qed.

  (** [normalize_neg_lits_cmd] preserves [jeval] semantics, given the
      precondition [2^64 mod 2^width = 0] (true for width = 64). *)
  Theorem normalize_cmd_correct :
    2 ^ 64 mod 2 ^ width = 0 ->
    forall (c : jasmin_cmd) (e e' : env),
      jeval e c e' ->
      jeval e (normalize_neg_lits_cmd c) e'.
  Proof.
    intros Hmod.
    (* Helper: normalize_neg_lits_expr preserves evaluation *)
    assert (Hexpr : forall (env : string -> word) (e : jasmin_expr) (w : word),
      eval_jexpr env e = Some w ->
      eval_jexpr env (normalize_neg_lits_expr e) = Some w).
    { intros env. induction e; simpl; intros w0 Heval; try exact Heval.
      - (* JElit *) injection Heval as <-. f_equal. apply normalize_lit_correct. exact Hmod.
      - (* JEadd *) destruct (eval_jexpr env e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env e2) as [v2|] eqn:He2; [|discriminate].
        rewrite (IHe1 _ eq_refl), (IHe2 _ eq_refl). exact Heval.
      - (* JEsub *) destruct (eval_jexpr env e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env e2) as [v2|] eqn:He2; [|discriminate].
        rewrite (IHe1 _ eq_refl), (IHe2 _ eq_refl). exact Heval.
      - (* JEmul *) destruct (eval_jexpr env e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env e2) as [v2|] eqn:He2; [|discriminate].
        rewrite (IHe1 _ eq_refl), (IHe2 _ eq_refl). exact Heval.
      - (* JEand *) destruct (eval_jexpr env e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env e2) as [v2|] eqn:He2; [|discriminate].
        rewrite (IHe1 _ eq_refl), (IHe2 _ eq_refl). exact Heval.
      - (* JEor *) destruct (eval_jexpr env e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env e2) as [v2|] eqn:He2; [|discriminate].
        rewrite (IHe1 _ eq_refl), (IHe2 _ eq_refl). exact Heval.
      - (* JExor *) destruct (eval_jexpr env e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env e2) as [v2|] eqn:He2; [|discriminate].
        rewrite (IHe1 _ eq_refl), (IHe2 _ eq_refl). exact Heval.
      - (* JEshr *) destruct (eval_jexpr env e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env e2) as [v2|] eqn:He2; [|discriminate].
        rewrite (IHe1 _ eq_refl), (IHe2 _ eq_refl). exact Heval.
      - (* JEshl *) destruct (eval_jexpr env e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env e2) as [v2|] eqn:He2; [|discriminate].
        rewrite (IHe1 _ eq_refl), (IHe2 _ eq_refl). exact Heval.
      - (* JEltu *) destruct (eval_jexpr env e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env e2) as [v2|] eqn:He2; [|discriminate].
        rewrite (IHe1 _ eq_refl), (IHe2 _ eq_refl). exact Heval.
      - (* JEeq *) destruct (eval_jexpr env e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env e2) as [v2|] eqn:He2; [|discriminate].
        rewrite (IHe1 _ eq_refl), (IHe2 _ eq_refl). exact Heval. }
    intros c e e' H. induction H; simpl;
      try (econstructor; eauto using Hexpr; fail);
      try (eapply jeval_if_true; eauto using Hexpr; fail);
      try (eapply jeval_while_true; eauto using Hexpr; fail).
  Qed.

  (* ================================================================ *)
  (* Equivalence modulo helper variables                               *)
  (* ================================================================ *)

  (** Some polish passes ([lower_func], [lower_comparisons_func],
      [lift_lits_func]) introduce *fresh helper variables* that the user
      program never reads or writes.  Their correctness theorem cannot be
      stated as straight [jeval] preservation, because the post-state of
      the transformed command differs from the original on the helper
      variables.  We therefore introduce a notion of "agreement modulo a
      set of helper variables", and a corresponding notion of "the program
      doesn't touch the helpers". *)

  Definition agrees_except (helpers : string -> bool) (e1 e2 : env) : Prop :=
    forall x, helpers x = false -> e1 x = e2 x.

  (** Reflexivity / symmetry / transitivity of [agrees_except]. *)
  Lemma agrees_except_refl helpers e : agrees_except helpers e e.
  Proof. intros x _; reflexivity. Qed.

  Lemma agrees_except_sym helpers e1 e2 :
    agrees_except helpers e1 e2 -> agrees_except helpers e2 e1.
  Proof. intros H x Hx. symmetry. apply H, Hx. Qed.

  Lemma agrees_except_trans helpers e1 e2 e3 :
    agrees_except helpers e1 e2 ->
    agrees_except helpers e2 e3 ->
    agrees_except helpers e1 e3.
  Proof. intros H12 H23 x Hx. rewrite (H12 _ Hx). apply (H23 _ Hx). Qed.

  (** Update preserves agreement when the updated key is not a helper. *)
  Lemma agrees_except_update helpers e1 e2 x w :
    agrees_except helpers e1 e2 ->
    agrees_except helpers (update e1 x w) (update e2 x w).
  Proof.
    intros H y Hy. unfold update.
    destruct (String.eqb y x); [reflexivity | apply H, Hy].
  Qed.

  (** ** lift_lits: introduces [__wtmp__] *)

  Definition wtmp_helper (x : string) : bool :=
    String.eqb x "__wtmp__".

  (** Predicate: an expression does not reference [__wtmp__] as a free
      variable.  Used as the freshness precondition for [lift_lits]. *)
  Fixpoint expr_no_wtmp (e : jasmin_expr) : bool :=
    match e with
    | JEvar x => negb (String.eqb x "__wtmp__"%string)
    | JElit _ => true
    | JEadd e1 e2 | JEsub e1 e2 | JEmul e1 e2 | JEmulhuu e1 e2
    | JEand e1 e2 | JEor e1 e2 | JExor e1 e2
    | JEshr e1 e2 | JEshl e1 e2 | JEltu e1 e2 | JEeq e1 e2 =>
        expr_no_wtmp e1 && expr_no_wtmp e2
    | JEload base _ => expr_no_wtmp base
    end.

  Fixpoint cmd_no_wtmp (c : jasmin_cmd) : bool :=
    match c with
    | JCskip => true
    | JCseq c1 c2 => cmd_no_wtmp c1 && cmd_no_wtmp c2
    | JCset x e => negb (String.eqb x "__wtmp__"%string) && expr_no_wtmp e
    | JCstore base _ vv => expr_no_wtmp base && expr_no_wtmp vv
    | JCcall _ args => forallb expr_no_wtmp args
    | JCif e ct cf => expr_no_wtmp e && cmd_no_wtmp ct && cmd_no_wtmp cf
    | JCwhile e body => expr_no_wtmp e && cmd_no_wtmp body
    | JCdecl _ _ body => cmd_no_wtmp body
    | JCadd_flags cf r a b | JCsub_flags cf r a b =>
        negb (String.eqb cf "__wtmp__"%string) &&
        negb (String.eqb r "__wtmp__"%string) &&
        expr_no_wtmp a && expr_no_wtmp b
    | JCadcx co r a b ci | JCsbb co r a b ci =>
        negb (String.eqb co "__wtmp__"%string) &&
        negb (String.eqb r "__wtmp__"%string) &&
        negb (String.eqb ci "__wtmp__"%string) &&
        expr_no_wtmp a && expr_no_wtmp b
    | JCmulx h l a b =>
        negb (String.eqb h "__wtmp__"%string) &&
        negb (String.eqb l "__wtmp__"%string) &&
        expr_no_wtmp a && expr_no_wtmp b
    end.

  (** Helper: if [e] does not reference [__wtmp__], updating [__wtmp__]
      in the environment does not change [e]'s evaluation. *)
  Lemma eval_jexpr_no_wtmp_irrelevant :
    forall (env_v : env) (e : jasmin_expr) (w : word),
      expr_no_wtmp e = true ->
      eval_jexpr env_v e =
      eval_jexpr (update env_v "__wtmp__" w) e.
  Proof.
    intros env_v e w.
    induction e; simpl; intros Hno; try reflexivity;
      try (apply andb_prop in Hno as [Hno1 Hno2];
           rewrite (IHe1 Hno1), (IHe2 Hno2); reflexivity).
    - (* JEvar *) unfold update.
      destruct (String.eqb x "__wtmp__"%string) eqn:Heq.
      + apply String.eqb_eq in Heq. subst x. simpl in Hno. discriminate.
      + reflexivity.
  Qed.

  (** Helper: [subst_first_large_lit] preserves evaluation under the
      [__wtmp__]-updated environment, when the original [e] does not
      reference [__wtmp__]. *)
  Lemma subst_first_large_lit_correct :
    forall (env_v : env) (e e' : jasmin_expr) (lit : Z),
      expr_no_wtmp e = true ->
      subst_first_large_lit e = (Some lit, e') ->
      forall w,
        eval_jexpr env_v e = Some w ->
        eval_jexpr (update env_v "__wtmp__" (word.of_Z lit)) e' = Some w.
  Proof.
    intros env_v.
    induction e; simpl; intros e' lit Hno Hsub w0 Hev;
      try discriminate.
    - (* JElit *)
      destruct (is_large_lit v) eqn:Hlarge; [|discriminate].
      injection Hsub as <- <-. simpl. unfold update.
      rewrite String.eqb_refl.
      injection Hev as <-. reflexivity.
    - (* JEadd *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (subst_first_large_lit e1) as [[lit1|] e1'] eqn:Hs1.
      + injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        erewrite (IHe1 _ _ Hno1 eq_refl _ eq_refl).
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno2), He2.
        reflexivity.
      + destruct (subst_first_large_lit e2) as [[lit2|] e2'] eqn:Hs2;
          [|discriminate].
        injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno1), He1.
        erewrite (IHe2 _ _ Hno2 eq_refl _ eq_refl). reflexivity.
    - (* JEsub *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (subst_first_large_lit e1) as [[lit1|] e1'] eqn:Hs1.
      + injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        erewrite (IHe1 _ _ Hno1 eq_refl _ eq_refl).
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno2), He2.
        reflexivity.
      + destruct (subst_first_large_lit e2) as [[lit2|] e2'] eqn:Hs2;
          [|discriminate].
        injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno1), He1.
        erewrite (IHe2 _ _ Hno2 eq_refl _ eq_refl). reflexivity.
    - (* JEmul *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (subst_first_large_lit e1) as [[lit1|] e1'] eqn:Hs1.
      + injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        erewrite (IHe1 _ _ Hno1 eq_refl _ eq_refl).
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno2), He2.
        reflexivity.
      + destruct (subst_first_large_lit e2) as [[lit2|] e2'] eqn:Hs2;
          [|discriminate].
        injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno1), He1.
        erewrite (IHe2 _ _ Hno2 eq_refl _ eq_refl). reflexivity.
    - (* JEand *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (subst_first_large_lit e1) as [[lit1|] e1'] eqn:Hs1.
      + injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        erewrite (IHe1 _ _ Hno1 eq_refl _ eq_refl).
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno2), He2.
        reflexivity.
      + destruct (subst_first_large_lit e2) as [[lit2|] e2'] eqn:Hs2;
          [|discriminate].
        injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno1), He1.
        erewrite (IHe2 _ _ Hno2 eq_refl _ eq_refl). reflexivity.
    - (* JEor *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (subst_first_large_lit e1) as [[lit1|] e1'] eqn:Hs1.
      + injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        erewrite (IHe1 _ _ Hno1 eq_refl _ eq_refl).
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno2), He2.
        reflexivity.
      + destruct (subst_first_large_lit e2) as [[lit2|] e2'] eqn:Hs2;
          [|discriminate].
        injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno1), He1.
        erewrite (IHe2 _ _ Hno2 eq_refl _ eq_refl). reflexivity.
    - (* JExor *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (subst_first_large_lit e1) as [[lit1|] e1'] eqn:Hs1.
      + injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        erewrite (IHe1 _ _ Hno1 eq_refl _ eq_refl).
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno2), He2.
        reflexivity.
      + destruct (subst_first_large_lit e2) as [[lit2|] e2'] eqn:Hs2;
          [|discriminate].
        injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno1), He1.
        erewrite (IHe2 _ _ Hno2 eq_refl _ eq_refl). reflexivity.
    - (* JEshr — only e1 is checked for large literals *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (subst_first_large_lit e1) as [[lit1|] e1'] eqn:Hs1;
        [|discriminate].
      injection Hsub as <- <-.
      destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
      destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
      injection Hev as <-. simpl.
      erewrite (IHe1 _ _ Hno1 eq_refl _ eq_refl).
      rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno2), He2.
      reflexivity.
    - (* JEshl — same *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (subst_first_large_lit e1) as [[lit1|] e1'] eqn:Hs1;
        [|discriminate].
      injection Hsub as <- <-.
      destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
      destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
      injection Hev as <-. simpl.
      erewrite (IHe1 _ _ Hno1 eq_refl _ eq_refl).
      rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno2), He2.
      reflexivity.
    - (* JEltu *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (subst_first_large_lit e1) as [[lit1|] e1'] eqn:Hs1.
      + injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        erewrite (IHe1 _ _ Hno1 eq_refl _ eq_refl).
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno2), He2.
        reflexivity.
      + destruct (subst_first_large_lit e2) as [[lit2|] e2'] eqn:Hs2;
          [|discriminate].
        injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno1), He1.
        erewrite (IHe2 _ _ Hno2 eq_refl _ eq_refl). reflexivity.
    - (* JEeq *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (subst_first_large_lit e1) as [[lit1|] e1'] eqn:Hs1.
      + injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        erewrite (IHe1 _ _ Hno1 eq_refl _ eq_refl).
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno2), He2.
        reflexivity.
      + destruct (subst_first_large_lit e2) as [[lit2|] e2'] eqn:Hs2;
          [|discriminate].
        injection Hsub as <- <-.
        destruct (eval_jexpr env_v e1) as [v1|] eqn:He1; [|discriminate].
        destruct (eval_jexpr env_v e2) as [v2|] eqn:He2; [|discriminate].
        injection Hev as <-. simpl.
        rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hno1), He1.
        erewrite (IHe2 _ _ Hno2 eq_refl _ eq_refl). reflexivity.
  Qed.

  (** Helper: pointwise-equal environments give the same evaluation. *)
  Lemma eval_jexpr_pointwise :
    forall (env1 env2 : env) (e : jasmin_expr),
      (forall x, env1 x = env2 x) ->
      eval_jexpr env1 e = eval_jexpr env2 e.
  Proof.
    intros env1 env2 e Hpw.
    induction e; simpl; try reflexivity;
      try (rewrite IHe1, IHe2; reflexivity).
    - (* JEvar *) f_equal. apply Hpw.
  Qed.

  (** Helper: if [env1] and [env2] agree on non-[__wtmp__] vars, then
      updating [__wtmp__] in both makes them pointwise equal. *)
  Lemma update_wtmp_pointwise :
    forall (env1 env2 : env) (w : word),
      agrees_except wtmp_helper env1 env2 ->
      forall y, update env1 "__wtmp__" w y = update env2 "__wtmp__" w y.
  Proof.
    intros env1 env2 w H y. unfold update.
    destruct (String.eqb y "__wtmp__"%string) eqn:Heq; [reflexivity|].
    apply H. unfold wtmp_helper. exact Heq.
  Qed.

  (** Helper: if [e] does not reference [__wtmp__], then evaluation is
      preserved across environments that agree on non-[__wtmp__] vars. *)
  Lemma eval_jexpr_agrees_except_wtmp :
    forall (env1 env2 : env) (e : jasmin_expr) (v : word),
      expr_no_wtmp e = true ->
      agrees_except wtmp_helper env1 env2 ->
      eval_jexpr env1 e = Some v ->
      eval_jexpr env2 e = Some v.
  Proof.
    intros env1 env2 e. revert env2.
    induction e; intros env2 v0 Hno Hag Hev; simpl in *;
    (* For binary ops: destruct evals in Hev, apply IH, finish *)
    match goal with
    | |- match eval_jexpr _ ?e1 with _ => _ end = _ =>
        let Hno1 := fresh "Hno1" in let Hno2 := fresh "Hno2" in
        apply andb_prop in Hno as [Hno1 Hno2];
        destruct (eval_jexpr env1 e1) as [v1|] eqn:He1; [|discriminate Hev];
        match goal with
        | |- match _ with Some _ => match eval_jexpr _ ?e2 with _ => _ end | None => _ end = _ =>
            destruct (eval_jexpr env1 e2) as [v2|] eqn:He2; [|discriminate Hev];
            rewrite (IHe1 _ _ Hno1 Hag eq_refl), (IHe2 _ _ Hno2 Hag eq_refl);
            exact Hev
        end
    | _ => idtac
    end.
    - (* JEvar *)
      injection Hev as <-. rewrite <- (Hag x).
      + reflexivity.
      + unfold wtmp_helper. destruct (String.eqb x "__wtmp__"%string) eqn:Heq;
          [discriminate Hno|reflexivity].
    - (* JElit *) exact Hev.
    - (* JEmulhuu *) discriminate Hev.
    - (* JEload *) discriminate Hev.
  Qed.

  (** [lift_lits_cmd_correct] (strong form): if the original program
      runs to completion in some env, the lifted program runs in any
      env that agrees on non-helper vars to a state that also agrees.
      The non-strong form is the [env1 = env2] specialisation. *)
  Theorem lift_lits_cmd_correct_strong :
    forall (c : jasmin_cmd) (env1 env1' : env),
      cmd_no_wtmp c = true ->
      jeval env1 c env1' ->
      forall (env2 : env),
        agrees_except wtmp_helper env1 env2 ->
        exists env2',
          jeval env2 (lift_lits_cmd c) env2' /\
          agrees_except wtmp_helper env1' env2'.
  Proof.
    intros c env1 env1' Hno H. induction H; intros env2 Hag; simpl.
    - (* JCskip *) exists env2. split; [constructor | exact Hag].
    - (* JCseq *)
      apply andb_prop in Hno as [Hno1 Hno2].
      destruct (IHjeval1 Hno1 _ Hag) as [env_mid [Hmid Hag_mid]].
      destruct (IHjeval2 Hno2 _ Hag_mid) as [env_end [Hend Hag_end]].
      exists env_end. split; [|exact Hag_end].
      eapply jeval_seq; eassumption.
    - (* JCset *)
      apply andb_prop in Hno as [Hxno Heno].
      apply Bool.negb_true_iff in Hxno.
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Heno Hag H) as Heval2.
      unfold lift_one_set.
      destruct (subst_first_large_lit ex) as [[lit|] e'] eqn:Hsub.
      + (* Subst happened *)
        exists (update (update env2 "__wtmp__"%string (word.of_Z lit)) x w).
        split.
        * eapply jeval_seq.
          -- apply jeval_set. simpl. reflexivity.
          -- apply jeval_set.
             eapply (subst_first_large_lit_correct _ _ _ _ Heno Hsub).
             exact Heval2.
        * intros y Hy. unfold update.
          destruct (String.eqb y x) eqn:Heqx; [reflexivity|].
          destruct (String.eqb y "__wtmp__"%string) eqn:Heqw.
          ++ exfalso. apply String.eqb_eq in Heqw. subst y.
             unfold wtmp_helper in Hy. rewrite String.eqb_refl in Hy. discriminate.
          ++ apply Hag. exact Hy.
      + (* No subst *)
        exists (update env2 x w). split.
        * apply jeval_set. exact Heval2.
        * apply agrees_except_update. exact Hag.
    - (* JCdecl *)
      destruct (IHjeval Hno _ Hag) as [env_end [Hend Hag_end]].
      exists env_end. split; [|exact Hag_end].
      apply jeval_decl. exact Hend.
    - (* JCif true *)
      apply andb_prop in Hno as [Hcond_no Hbranches].
      apply andb_prop in Hcond_no as [Hcond_no Hct_no].
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hcond_no Hag H) as Heval2.
      destruct (IHjeval Hct_no _ Hag) as [env_end [Hend Hag_end]].
      exists env_end. split; [|exact Hag_end].
      eapply jeval_if_true; [exact Heval2 | exact H0 | exact Hend].
    - (* JCif false *)
      apply andb_prop in Hno as [Hcond_no Hbranches].
      apply andb_prop in Hcond_no as [Hcond_no _].
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hcond_no Hag H) as Heval2.
      destruct (IHjeval Hbranches _ Hag) as [env_end [Hend Hag_end]].
      exists env_end. split; [|exact Hag_end].
      apply jeval_if_false; [exact Heval2 | exact Hend].
    - (* JCwhile false *)
      apply andb_prop in Hno as [Hcond_no _].
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hcond_no Hag H) as Heval2.
      exists env2. split; [|exact Hag].
      apply jeval_while_false. exact Heval2.
    - (* JCwhile true *)
      apply andb_prop in Hno as [Hcond_no Hbody_no].
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hcond_no Hag H) as Heval2.
      destruct (IHjeval1 Hbody_no _ Hag) as [env_mid [Hmid Hag_mid]].
      assert (Hwhile_no : cmd_no_wtmp (JCwhile econd body) = true).
      { simpl. apply andb_true_intro. split; assumption. }
      destruct (IHjeval2 Hwhile_no _ Hag_mid) as [env_end [Hend Hag_end]].
      exists env_end. split; [|exact Hag_end].
      eapply jeval_while_true; [exact Heval2 | exact H0 | exact Hmid | exact Hend].
    - (* JCstore *)
      apply andb_prop in Hno as [Hb_no Hv_no].
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hb_no Hag H) as Heval_b.
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hv_no Hag H0) as Heval_v.
      destruct (subst_first_large_lit v) as [[lit|] v'] eqn:Hsub.
      + (* Lifted: __wtmp__ = lit; store base off v' *)
        exists (update env2 "__wtmp__"%string (word.of_Z lit)).
        split.
        * eapply jeval_seq.
          -- apply jeval_set. simpl. reflexivity.
          -- (* store with v' under updated env *)
             eapply jeval_store.
             ++ rewrite <- (eval_jexpr_no_wtmp_irrelevant _ _ _ Hb_no).
                exact Heval_b.
             ++ eapply (subst_first_large_lit_correct _ _ _ _ Hv_no Hsub).
                exact Heval_v.
        * intros y Hy. unfold update.
          destruct (String.eqb y "__wtmp__"%string) eqn:Hwy.
          ++ exfalso. apply String.eqb_eq in Hwy. subst y.
             unfold wtmp_helper in Hy. rewrite String.eqb_refl in Hy. discriminate.
          ++ apply Hag. exact Hy.
      + (* No lift *)
        exists env2. split; [|exact Hag].
        eapply jeval_store; [exact Heval_b | exact Heval_v].
    - (* JCcall *) exists env2. split; [constructor | exact Hag].
    - (* JCadd_flags *)
      apply andb_prop in Hno as [Hno' Hb_no].
      apply andb_prop in Hno' as [Hno'' Ha_no].
      apply andb_prop in Hno'' as [Hcfno Hrno].
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Ha_no Hag H) as Heval_a.
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hb_no Hag H0) as Heval_b.
      eexists. split; [eapply jeval_add_flags; eassumption|].
      apply Bool.negb_true_iff in Hrno, Hcfno.
      intros y Hy. unfold update.
      destruct (String.eqb y r) eqn:Heq1; [reflexivity|].
      destruct (String.eqb y cf) eqn:Heq2; [reflexivity|].
      apply Hag. exact Hy.
    - (* JCadcx *)
      apply andb_prop in Hno as [Hno' Hb_no].
      apply andb_prop in Hno' as [Hno'' Ha_no].
      apply andb_prop in Hno'' as [Hno''' Hcino].
      apply andb_prop in Hno''' as [Hcono Hrno].
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Ha_no Hag H) as Heval_a.
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hb_no Hag H0) as Heval_b.
      eexists. split; [eapply jeval_adcx; eassumption|].
      apply Bool.negb_true_iff in Hrno, Hcono.
      intros y Hy. unfold update.
      destruct (String.eqb y r) eqn:Heq1; [reflexivity|].
      destruct (String.eqb y co) eqn:Heq2; [reflexivity|].
      apply Hag. exact Hy.
    - (* JCmulx *)
      apply andb_prop in Hno as [Hno' Hb_no].
      apply andb_prop in Hno' as [Hno'' Ha_no].
      apply andb_prop in Hno'' as [Hhno Hlno].
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Ha_no Hag H) as Heval_a.
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hb_no Hag H0) as Heval_b.
      eexists. split; [eapply jeval_mulx; eassumption|].
      apply Bool.negb_true_iff in Hhno, Hlno.
      intros y Hy. unfold update.
      destruct (String.eqb y l) eqn:Heq1; [reflexivity|].
      destruct (String.eqb y h) eqn:Heq2; [reflexivity|].
      apply Hag. exact Hy.
    - (* JCsub_flags *)
      apply andb_prop in Hno as [Hno' Hb_no].
      apply andb_prop in Hno' as [Hno'' Ha_no].
      apply andb_prop in Hno'' as [Hcfno Hrno].
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Ha_no Hag H) as Heval_a.
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hb_no Hag H0) as Heval_b.
      eexists. split; [eapply jeval_sub_flags; eassumption|].
      apply Bool.negb_true_iff in Hrno, Hcfno.
      intros y Hy. unfold update.
      destruct (String.eqb y r) eqn:Heq1; [reflexivity|].
      destruct (String.eqb y cf) eqn:Heq2; [reflexivity|].
      apply Hag. exact Hy.
    - (* JCsbb *)
      apply andb_prop in Hno as [Hno' Hb_no].
      apply andb_prop in Hno' as [Hno'' Ha_no].
      apply andb_prop in Hno'' as [Hno''' Hcino].
      apply andb_prop in Hno''' as [Hcono Hrno].
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Ha_no Hag H) as Heval_a.
      pose proof (eval_jexpr_agrees_except_wtmp _ _ _ _ Hb_no Hag H0) as Heval_b.
      eexists. split; [eapply jeval_sbb; eassumption|].
      apply Bool.negb_true_iff in Hrno, Hcono.
      intros y Hy. unfold update.
      destruct (String.eqb y r) eqn:Heq1; [reflexivity|].
      destruct (String.eqb y co) eqn:Heq2; [reflexivity|].
      apply Hag. exact Hy.
  Qed.

  (** The standard form is the [env1 = env2] specialisation. *)
  Theorem lift_lits_cmd_correct :
    forall (c : jasmin_cmd) (e e' : env),
      cmd_no_wtmp c = true ->
      jeval e c e' ->
      exists e'',
        jeval e (lift_lits_cmd c) e'' /\
        agrees_except wtmp_helper e' e''.
  Proof.
    intros c e e' Hno H.
    apply (lift_lits_cmd_correct_strong c e e' Hno H e (agrees_except_refl _ _)).
  Qed.

  (** ** lower_comparisons: introduces numbered helper variables *)

  (** [lower_comparisons_cmd] uses [extract_comparisons] which generates
      fresh variable names of the form ["__cmp_<n>__"]; the [n] threads
      a counter through the recursion to avoid clashes.

      Proof structure:
      - Helper set: any variable starting with ["__cmp_"].
      - The transformation:
        [JCset x e where has_comparison e]
        becomes
        [prefix; JCset x e']
        where [prefix] sets ["__cmp_<n>__"] to [if (a <u b) then 1 else 0].
        Use [agrees_except cmp_helper].
      - Need a lemma [extract_comparisons_correct]: evaluating [e']
        under the post-prefix env gives the same value as [e] under the
        pre-prefix env (when the user doesn't read [__cmp_*__] vars).

      Status: AXIOMATIZED. *)
  Definition cmp_helper (x : string) : bool :=
    String.prefix "__cmp_" x.

  Axiom lower_comparisons_cmd_correct :
    forall (n : nat) (c : jasmin_cmd) (e e' : env),
      jeval e c e' ->
      let '(_, c') := lower_comparisons_cmd n c in
      exists e'',
        jeval e c' e'' /\
        agrees_except cmp_helper e' e''.

  (** ** lower_binop_assigns: introduces helper variables *)

  (** [lower_binop_assigns] rewrites [x = e1 op e2] into the explicit
      two-step form [x_a = e1; x = e1; x = (x op e2)] using
      [flatten_expr] which introduces helper variables of the form
      [x ++ "a"], [x ++ "aa"], etc.

      Proof structure:
      - Helper set: variables that are not in the original program's
        free variables (more complex characterization needed).
      - The transformation: [JCset x (e1 op e2)] becomes
        [JCseq prefix1 (JCseq (JCset x a1) (JCseq prefix2 (JCset x ...)))].
      - Each step preserves the value of [x] modulo the helpers.

      Status: AXIOMATIZED.  This pass is the most involved because
      [flatten_expr] is a deep recursive transformation. *)
  Axiom lower_binop_assigns_correct :
    forall (helpers : string -> bool) (c : jasmin_cmd) (e e' : env),
      jeval e c e' ->
      exists e'',
        jeval e (lower_binop_assigns c) e'' /\
        agrees_except helpers e' e''.

  (** ** carry_func: pattern matching for x86 intrinsics *)

  (** [lower_carry_cmd] matches sequences like
      [r = a + b; cf = (r <u a)]
      and replaces them with [#ADD(a, b)] which sets [cf] and [r] in
      one step.

      Proof structure:
      - Per-pattern equivalence: each replacement is a 1-1 substitution,
        no fresh helpers introduced.
      - For ADD: [r = a + b; cf = (r <u a)] sets r to (a+b) and cf to
        the carry bit.  [#ADD(a, b)] computes the same.  This requires
        proving the carry detection [r <u a] equals the actual overflow
        bit, which is a property of word arithmetic.
      - Similarly for SUB/ADCX/SBB/MULX/CMOV.

      Status: AXIOMATIZED.  This is a one-to-one structural replacement
      so no helper variables; the proof reduces to per-instruction
      semantic equivalence (one lemma per intrinsic). *)
  Axiom carry_cmd_correct :
    forall (c : jasmin_cmd) (e e' : env),
      jeval e c e' ->
      jeval e (lower_carry_cmd c) e'.

End WithWordCmd.
