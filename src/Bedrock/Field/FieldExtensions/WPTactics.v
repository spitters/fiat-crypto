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
