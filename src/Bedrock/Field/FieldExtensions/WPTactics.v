(** * Shared WP proof tactics for field extension operations.

    Provides reusable Ltac tactics that automate the mechanical parts
    of bedrock2 weakest-precondition proofs for Fp6/Fp12/... operations.

    Each field extension WP proof follows a 4-phase structure:
      SETUP -> PER-CALL (xN) -> STACK DEALLOCATION -> POSTCONDITION
    The per-call phase is 90%+ mechanical and is the main target of
    these tactics.

    Usage pattern for a binop sub-call:
    <<
      exists [ptr_out; ptr_x; ptr_y]. split. { solve_dexprs. }
      eapply Semantics.weaken_call.
      1: { eapply (HFop ptr_out ptr_x ptr_y val_out val_x val_y _ tr).
           wp_binop_precond solve_bounds. }
      (* ... intros pattern for postcondition ... *)
    >>

    Usage pattern for a unop sub-call:
    <<
      exists [ptr_out; ptr_x]. split. { solve_dexprs. }
      eapply Semantics.weaken_call.
      1: { eapply (HFop ptr_out ptr_x val_out val_x _ tr).
           wp_unop_precond solve_bounds. }
      (* ... intros pattern for postcondition ... *)
    >>
*)

Require Import Rupicola.Lib.Api.
Require Import bedrock2.Semantics.
Require Import bedrock2.WeakestPrecondition.

(** ** ecancel_assumption_with_copy

    Like [ecancel_assumption] but first copies the sep hypothesis so it
    survives for subsequent calls.  [ecancel_assumption] is destructive:
    it clears the hypothesis it matches.  In WP proofs we typically need
    the same master sep fact for 2-3 obligations per call. *)

Ltac ecancel_assumption_with_copy :=
  match goal with
  | Hsep : (_ * _)%sep _ |- (_ * _)%sep _ =>
    let H' := fresh "Hcopy" in
    pose proof Hsep as H'; ecancel_assumption
  end.

(** ** wp_binop_precond

    Solves the 5-part binop precondition after [eapply (HF ...)]:
      bounds_x /\ bounds_y /\ (exists Rx, sep) /\ (exists Ry, sep) /\ sep

    The [solve_bounds_tac] argument should handle bounds goals
    (typically [assumption] or a [first [...]] combinator).

    NOTE: The call hypothesis must be applied with explicit pointer and
    value arguments (not bare [eapply HF]) so that [ecancel_assumption]
    can match concrete FElem addresses against the sep hypothesis. *)

Ltac wp_binop_precond solve_bounds_tac :=
  split; [solve_bounds_tac |];
  split; [solve_bounds_tac |];
  split;
  [ eexists; ecancel_assumption_with_copy
  | split;
    [ eexists; ecancel_assumption_with_copy
    | ecancel_assumption_with_copy ] ].

(** ** wp_unop_precond

    Solves the 3-part unop precondition after [eapply (HF ...)]:
      bounds_x /\ (exists Rx, sep) /\ sep *)

Ltac wp_unop_precond solve_bounds_tac :=
  split; [solve_bounds_tac |];
  split;
  [ eexists; ecancel_assumption_with_copy
  | ecancel_assumption_with_copy ].

(** ** wp_destruct_sep

    Recursively destructs a nested [(_ * _)%sep _] hypothesis into
    individual map hypotheses.  Each layer produces:
      [m1], [m2], [Heq : _ = putmany m1 m2], [Hd : disjoint m1 m2],
      [H1 : P1 m1], and recurses on the rest. *)

Ltac wp_destruct_sep H :=
  lazymatch type of H with
  | (_ * _)%sep _ =>
    let m1 := fresh "m" in let m2 := fresh "m" in
    let Heq := fresh "Heq" in let Hd := fresh "Hd" in
    let H1 := fresh "Hf" in let H2 := fresh "Hrest" in
    destruct H as [m1 [m2 [[Heq Hd] [H1 H2]]]];
    subst; try wp_destruct_sep H2
  | _ => idtac
  end.

(** ** split_all_disjointness

    Splits all compound [map.disjoint (map.putmany ...) ...] hypotheses
    into atomic pairwise disjointness facts. *)

Ltac split_all_disjointness :=
  repeat match goal with
  | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hdj" in let H2 := fresh "Hdj" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
  | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
      let H1 := fresh "Hdj" in let H2 := fresh "Hdj" in
      destruct (proj1 (map.disjoint_putmany_l a b c) H) as [H1 H2]; clear H
  end.

(** ** map_disjoint_auto

    Solves [map.disjoint] goals by decomposing putmany and searching
    hypotheses (including symmetric matches). *)

Ltac map_disjoint_auto :=
  lazymatch goal with
  | |- map.disjoint (map.putmany _ _) _ =>
      apply map.disjoint_putmany_l; split; map_disjoint_auto
  | |- map.disjoint _ (map.putmany _ _) =>
      apply map.disjoint_putmany_r; split; map_disjoint_auto
  | |- map.disjoint ?a ?b =>
      first [ assumption
            | (unfold map.disjoint; intros ?k ?v1 ?v2 ?Hg1 ?Hg2;
               match goal with H : map.disjoint _ _ |- _ => exact (H k v2 v1 Hg2 Hg1) end) ]
  end.

(** ** wp_call_setup

    Common setup after [repeat straightline] produces the goal for a function call.
    Solves the [dexprs] part and prepares for [Semantics.weaken_call]. *)

Ltac solve_dexprs :=
  cbv [dexprs list_map list_map_body
       WeakestPrecondition.expr WeakestPrecondition.expr_body];
  repeat first
    [ exact eq_refl
    | eexists; split;
      [ repeat (first [ apply map.get_put_same
                      | rewrite map.get_put_diff by congruence ]); try exact eq_refl | ]
    | straightline ].

(** ** wp_post_call

    Process the postcondition after a [Semantics.weaken_call]:
    intros the postcondition, provides locals, and straightlines. *)

(** ** build_sep

    Constructs a nested separation logic fact from individual predicates
    on disjoint sub-maps.  Given a goal of the form:

      (P0 * (P1 * ... * (Pn-1 * Pn))) (putmany m0 (putmany m1 ... (putmany mn-1 mn)))

    with hypotheses [H0 : P0 m0], [H1 : P1 m1], ..., [Hn : Pn mn] and
    pairwise [map.disjoint mi mj], solves the goal by constructing the
    nested existential witnesses and proving disjointness/equality/predicate
    obligations automatically.

    Handles bedrock2's [(P * Q)%sep m] which unfolds to
    [exists m1 m2, m = putmany m1 m2 /\ disjoint m1 m2 /\ P m1 /\ Q m2]
    as well as the [exists m1 m2, putmany m1 m2 = m /\ ...] variant.

    Usage: after [split_all_disjointness] derives pairwise disjointness,
    [build_sep] solves the sep goal in one call.

    Complexity: O(n^2) in the number of conjuncts (from disjointness checks),
    versus O(2^n) for [sauto]. Handles 9+ conjuncts instantly. *)

Ltac build_sep :=
  lazymatch goal with
  | |- (_ * _)%sep _ =>
    lazymatch goal with
    | |- (_ * _)%sep (map.putmany ?m1 ?m2) =>
      exists m1, m2;
      split; [split; [reflexivity | map_disjoint_auto] |];
      split; [first [eassumption | assumption] | build_sep]
    | |- (_ * _)%sep ?m =>
      first [eassumption | assumption]
    end
  | |- ?P ?m => first [eassumption | assumption]
  end.

Ltac wp_post_call locals_term :=
  let t := fresh "t" in let m := fresh "m" in let rets := fresh "rets" in
  intros t m rets;
  let H := fresh "H" in intro H;
  lazymatch type of H with
  | _ /\ _ =>
    let Hrets := fresh "Hrets" in let Htr := fresh "Htr" in
    destruct H as [Hrets [Htr H]];
    subst rets; try (symmetry in Htr; subst t);
    cbv [map.putmany_of_list_zip];
    exists locals_term;
    split; [ exact eq_refl | ];
    repeat straightline
  end.

(** ** solve_bounds_auto

    Solves bounds goals of the form [bounded_by ?b ?x] by trying
    [assumption] first, then [relax_bounds] (tight->loose) from
    any [FieldRepresentation_ok] in scope. *)

Ltac solve_bounds_auto :=
  first
  [ assumption
  | (* Try to find a relax_bounds-like hypothesis or instance.
       For BLS12 where tight=loose, [assumption] suffices.
       For other fields, override this tactic locally. *)
    match goal with
    | H : ?P ?b1 ?x |- ?P ?b2 ?x =>
      (* Same predicate, different bounds — try direct match *)
      exact H
    end ].

(** ** wp_postcall_auto

    Processes the postcondition after [Semantics.weaken_call] returns.
    Handles the common pattern:
      intros t m rets [Hrets [Htr <postcond>]].
      subst rets. subst t.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

    For binop/unop specs, [<postcond>] is
      [exists out, feval out = ... /\ bounded_by ... /\ sep].
    This tactic just does the intros, subst, and locals update.
    It does NOT straightline further (to avoid entering the next call). *)

Ltac wp_postcall_auto :=
  let t := fresh "t" in let m := fresh "m" in let rets := fresh "rets" in
  let H := fresh "Hpost" in
  intros t m rets H;
  lazymatch type of H with
  | ?A /\ ?B =>
    let Hrets := fresh "Hrets" in let Hrest := fresh "Hrest" in
    destruct H as [Hrets Hrest];
    subst rets;
    lazymatch type of Hrest with
    | ?C /\ ?D =>
      let Htr := fresh "Htr" in let Hrem := fresh "Hrem" in
      destruct Hrest as [Htr Hrem];
      first [ symmetry in Htr; subst t | subst t | idtac ];
      cbv [map.putmany_of_list_zip];
      (try (eexists; split; [ exact eq_refl | ]))
    | _ =>
      first [ subst t | idtac ];
      cbv [map.putmany_of_list_zip];
      (try (eexists; split; [ exact eq_refl | ]))
    end
  end.

(** ** wp_call

    Processes one function call end-to-end: argument evaluation via
    [straightline], [Semantics.weaken_call] with automatic spec
    instantiation, and postcondition processing.

    Usage:
      [wp_call HSpec]
    where [HSpec : spec_of_SomeOp functions] (binop, unop, copy, or
    from_word).

    The tactic:
    1. Runs [repeat straightline] to process cmd.seq and evaluate args
    2. Applies [Semantics.weaken_call]
    3. In the callee obligation: unfolds the spec, eapplies [HSpec],
       and solves the precondition (bounds + sep) automatically
    4. In the continuation: destructs the postcondition and prepares
       for the next call

    NOTE: For [felem_copy] specs, the precondition has a different
    shape (two sep conditions). [wp_call] tries the copy pattern as
    a fallback. For [from_word], the precondition is just a sep. *)

Ltac wp_call spec_hyp :=
  (* Step 1: process cmd.seq + cmd.call arg evaluation *)
  repeat straightline;
  (* Step 2: weaken_call *)
  eapply Semantics.weaken_call;
  [ (* Step 3: build the callee call.
       [eapply spec_hyp] unfolds the spec instance and unifies
       pointer/value arguments from the goal. The remaining
       subgoals are the precondition parts. We detect the shape
       (binop 5-part, unop 3-part, from_word 1-part, copy 2-part)
       by trying each solver in order. *)
    let H := fresh "Hcallee" in
    pose proof spec_hyp as H;
    eapply H;
    first
    [ (* binop_spec: bounded_x /\ bounded_y /\ (exists Rx, sep) /\ (exists Ry, sep) /\ sep *)
      wp_binop_precond solve_bounds_auto
    | (* unop_spec: bounded_x /\ (exists Rx, sep) /\ sep *)
      wp_unop_precond solve_bounds_auto
    | (* from_word: (FElem pout out * R) mem *)
      ecancel_assumption_with_copy
    | (* felem_copy: two sep conditions *)
      split; ecancel_assumption_with_copy
    | (* custom fnspec — try to solve conjunction tree *)
      repeat (first
        [ solve_bounds_auto
        | ecancel_assumption_with_copy
        | split ])
    ]
  | (* Step 4: process postcondition *)
    wp_postcall_auto
  ].

(* normalize_offsets: must be defined LOCALLY in each proof file
   because it references CubicFieldExtensions/DodecicFieldExtensions
   definitions that would create circular imports if placed here.
   See BLS12_PairingHelpers.v for the template. *)

(** ** wp_stackalloc

    Handles one level of [stackalloc] in a WP proof:
    1. Proves alignment via [Z_mod_mult]
    2. Intros the stack pointer, stack memory, combined memory
    3. Converts [anybytes] to an [FElem] via [FElem_from_bytes]

    After [wp_stackalloc], the context has:
    - [a_NAME : word] — the stack pointer
    - [NAME_val : felem] — the initial (junk) felem value
    - [NAME_felem : FElem a_NAME NAME_val mStack]
    - [mComb : mem] with [map.split mComb mPrev mStack]

    The [FieldParams] and [FieldRepr] arguments specify which field
    level the FElem lives at (Fp, Fp2, Fp6, Fp12).

    Usage:
      [wp_stackalloc FieldParams FieldRepr] *)

(* wp_stackalloc: handles one level of stackalloc.
   Must be defined locally in proof files since it references
   AbstractField.FElem_from_bytes.

   Template:
   Ltac wp_stackalloc FldParams FldRepr :=
     split; [ apply Z_mod_mult | ];
     let a := fresh "a" in let mStack := fresh "mStack" in
     let mComb := fresh "mComb" in let Hany := fresh "Hany" in
     let Hsplit := fresh "Hsplit" in
     intros a mStack mComb Hany Hsplit;
     let Hfb := fresh "Hfb" in
     pose proof (AbstractField.FElem_from_bytes (field_parameters:=FldParams)
       (field_representation:=FldRepr) a) as Hfb;
     unfold AbstractField.Placeholder in Hfb;
     let v := fresh "stkval" in let Hfe := fresh "Hfelem" in
     pose proof (proj1 (Hfb mStack) Hany) as [v Hfe]; clear Hfb. *)

(** ** wp_from_word_pair

    Handles the common pattern of zeroing an Fp2 slot via two
    consecutive [from_word(ptr, 0)] + [from_word(ptr+off, 0)] calls.

    Precondition: the sep hypothesis has [FElem_Fp2 p x] at the front
    (or findable by ecancel).

    The tactic:
    1. Splits [FElem_Fp2] into two [FElem_Fp] halves
    2. Processes the first [from_word] call
    3. Processes the second [from_word] call
    4. Joins the two [FElem_Fp] halves back into [FElem_Fp2]

    Usage:
      [wp_from_word_pair HFfromword Fp2_split_lemma Fp_join_lemma]
    where [Fp2_split_lemma] is [FElem_Fp2_split_in_sep] and
    [Fp_join_lemma] is [FElem_Fp_join_in_sep] from the proof file.

    NOTE: This tactic assumes the sep is in the right shape. If
    the target Fp2 is not at the front, rearrange first. *)

Ltac wp_from_word_pair HFfromword split_lemma join_lemma len_tac :=
  (* Split Fp2 into Fp halves *)
  match goal with
  | Hsep : (_ * _)%sep _ |- _ =>
    apply split_lemma in Hsep
  end;
  (* First from_word call (fst half) *)
  wp_call HFfromword;
  (* Second from_word call (snd half) *)
  wp_call HFfromword;
  (* Join back into Fp2 — need length witnesses *)
  match goal with
  | Hsep : (_ * _)%sep _ |- _ =>
    eapply join_lemma in Hsep; [ | len_tac | len_tac ]
  end.
