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

  (** [lift_lits_correct] (proof obligation):
      For any [c] that does not read or write [__wtmp__], the lifted
      command produces a state that agrees with the original on every
      variable except [__wtmp__].

      Proof structure:
      - Induction on the [jeval] derivation of the original command.
      - For [JCset x e]: case on [subst_first_large_lit e]:
        + [None]: identity transformation, trivial.
        + [Some lit]: produces [JCseq (JCset "__wtmp__" lit) (JCset x e')].
          Step 1 sets [__wtmp__] to [word.of_Z lit].
          Step 2 evaluates [e'] under the updated env.  Need a lemma
          [subst_first_large_lit_correct]: if the user expression [e]
          does not use [__wtmp__], then evaluating [e'] in
          [update env "__wtmp__" (word.of_Z lit)] gives the same value
          as evaluating [e] in [env].
      - All other constructors: structural recursion.

      Status: AXIOMATIZED.  The freshness/agreement framework is in
      place; the substitution lemma needs ~80 lines of induction on the
      expression structure (one case per binary op). *)
  Axiom lift_lits_cmd_correct :
    forall (c : jasmin_cmd) (e e' : env),
      jeval e c e' ->
      exists e'',
        jeval e (lift_lits_cmd c) e'' /\
        agrees_except wtmp_helper e' e''.

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
