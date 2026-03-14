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
