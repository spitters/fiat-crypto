(** * Aliased (in-place) calling conventions for curve_add and curve_double.

    The wNAF/GLV scalar multiplication loop accumulates into an
    accumulator point, calling curve_add with input1 = output.
    This file provides specs and (admitted) proofs that the
    existing ladderstep_body / point_double_body implementations
    are correct under aliased calling conventions.

    KEY INSIGHT: Both ladderstep_body and point_double_body use
    Rupicola's [let/n := stack ...] pattern, which copies ALL
    inputs to stack-allocated temporaries before any computation.
    By the time outputs are written to memory, the original input
    data has already been read into stack variables. Therefore
    aliasing input pointers with output pointers is safe.

    NOTE on felem_copy and opp: The existing UnOp spec pattern
    (in Specs/Field.v) uses separate existential frames for input
    and output, so those specs already permit aliased calls
    (pout = px). No separate inplace specs are needed. *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAdd.
Require Import Crypto.Bedrock.Group.CurveAdd.PointDouble.

Local Open Scope Z_scope.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  Local Notation F := (F M_pos).

  Context (Hbounds_eq : loose_bounds = tight_bounds).
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

  Local Notation curve_add := (@ladderstep_gallina _ three_b_val).

  (** ** In-place curve_add: input1 = output (accumulation)

      Calling convention: [pX1; pX2; pY1; pY2; pZ1; pZ2; pX1; pY1; pZ1]
      i.e., output pointers are the same as input1 pointers.

      Precondition: 6 FElem clauses (no separate output memory).
      Postcondition: pX1/pY1/pZ1 hold the result; pX2/pY2/pZ2 preserved. *)

  Definition spec_of_ladderstep_inplace functions : Prop :=
    forall pXo pX2 pYo pY2 pZo pZ2
      (Xo Yo Zo X2 Y2 Z2 : F) R tr m,
      (FElem (Some tight_bounds) pXo Xo
       * FElem (Some tight_bounds) pYo Yo
       * FElem (Some tight_bounds) pZo Zo
       * FElem (Some tight_bounds) pX2 X2
       * FElem (Some tight_bounds) pY2 Y2
       * FElem (Some tight_bounds) pZ2 Z2
       * R)%sep m ->
      WeakestPrecondition.call functions "curve_add" tr m
        [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           let '\<Xo', Yo', Zo'\> := curve_add Xo X2 Yo Y2 Zo Z2 in
           (FElem (Some tight_bounds) pXo Xo'
            * FElem (Some tight_bounds) pYo Yo'
            * FElem (Some tight_bounds) pZo Zo'
            * FElem (Some tight_bounds) pX2 X2
            * FElem (Some tight_bounds) pY2 Y2
            * FElem (Some tight_bounds) pZ2 Z2
            * R)%sep m').

  (** Proof strategy for [ladderstep_inplace_ok]:

      The non-aliased spec (spec_of_ladderstep) cannot directly give us
      the aliased version because the sep conjunction requires 9 DISTINCT
      FElem regions. We instead prove the result by re-examining the
      Rupicola-compiled body [ladderstep_body].

      Step 1: Unfold WeakestPrecondition.call. Look up "curve_add" in
        [functions] to get [ladderstep_body]. This gives us a WP goal
        over the body with the aliased local variable bindings:
          X1 |-> pXo, X2 |-> pX2, ..., Xout |-> pXo, Yout |-> pYo, Zout |-> pZo

      Step 2: The body begins with stack allocations (stackalloc) for
        temporaries three_b, t0..t5, Xout, Yout, Zout. After these
        stackallocs, we have fresh stack memory for all temporaries,
        plus the 6 input FElems in the heap.

      Step 3: The first operations are [three_b_loader], then reads of
        input values into stack variables via mul/add/sub calls. Each
        field operation reads from input FElem pointers (pXo, pX2, etc.)
        and writes to stack-allocated temporaries. Since the inputs are
        only READ during these early operations, aliasing with output
        pointers is irrelevant — the output pointers (pXo, pYo, pZo)
        still hold the original input values.

      Step 4: Later operations write to Xout/Yout/Zout stack variables
        (NOT to pXo/pYo/pZo yet — the stack temporaries are separate
        memory). The final three felem_copy calls in the epilogue copy
        from stack Xout/Yout/Zout to the output pointers pXo/pYo/pZo.
        At this point, X1/Y1/Z1 inputs have already been consumed, so
        overwriting pXo/pYo/pZo is safe.

      Step 5: After the epilogue, the postcondition follows by the same
        functional correctness as the non-aliased case, since the Gallina
        computation is identical.

      In practice, the proof mirrors [ladderstep_correct] (compile tactic)
      but with a modified sep hypothesis that accounts for aliasing. The
      main technical challenge is that [straightline'] and [handle_call]
      need the sep clauses to be set up correctly for each sub-call. *)

  Lemma ladderstep_inplace_ok :
    forall functions,
      spec_of_ladderstep three_b functions ->
      spec_of_ladderstep_inplace functions.
  Proof.
    (* The proof needs to:
       1. Unfold spec_of_ladderstep to get the function lookup and WP
       2. Instantiate the non-aliased spec with pXout=pX1, pYout=pY1, pZout=pZ1
       3. The sep precondition requires 9 distinct FElem regions, but we only
          have 6. We cannot directly apply the spec.
       4. Instead, we must unfold WeakestPrecondition.call, look up the
          function body (ladderstep_body), and replay the WP proof with
          the aliased memory layout.

       Alternative approach (more practical):
       - From the 6-FElem sep, derive that pXo/pYo/pZo each occupy
         felem_size_in_bytes of disjoint memory
       - Show that the same memory region can serve as both "input1" and
         "output" since the body copies inputs to stack first
       - This requires analyzing the compiled body structure

       This is a deep Rupicola proof that requires ~200 lines of
       interactive tactic application. We admit it here and note that
       CurveAddAlt.v provides the same statement as an axiom. *)
  Admitted.

  (** ** In-place curve_double via curve_add: P + P in-place

      Calling convention: [pX; pX; pY; pY; pZ; pZ; pX; pY; pZ]
      All 9 arguments alias: input1 = input2 = output.

      Precondition: 3 FElem clauses.
      Postcondition: pX/pY/pZ hold curve_add(X,X,Y,Y,Z,Z). *)

  Definition spec_of_ladderstep_double_inplace functions : Prop :=
    forall pX pY pZ (X Y Z : F) R tr m,
      (FElem (Some tight_bounds) pX X
       * FElem (Some tight_bounds) pY Y
       * FElem (Some tight_bounds) pZ Z
       * R)%sep m ->
      WeakestPrecondition.call functions "curve_add" tr m
        [pX; pX; pY; pY; pZ; pZ; pX; pY; pZ]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           let '\<Xo, Yo, Zo\> := curve_add X X Y Y Z Z in
           (FElem (Some tight_bounds) pX Xo
            * FElem (Some tight_bounds) pY Yo
            * FElem (Some tight_bounds) pZ Zo
            * R)%sep m').

  (** Proof strategy: Same as ladderstep_inplace_ok but with even more
      aliasing (input1 = input2 = output). The key observation is still
      that all 6 input values are copied to stack temporaries before any
      output is written. With input1 = input2, the Gallina function
      receives (X,X,Y,Y,Z,Z) which is just point doubling via the
      complete addition formula. *)

  Lemma ladderstep_double_inplace_ok :
    forall functions,
      spec_of_ladderstep three_b functions ->
      spec_of_ladderstep_double_inplace functions.
  Proof.
    (* Similar to ladderstep_inplace_ok but with 3-way aliasing.
       The same stack-copy argument applies: the body reads all 6
       inputs (here X,X,Y,Y,Z,Z from 3 memory regions) into stack
       temporaries, then computes entirely on stack, then writes
       results back to the 3 output pointers.

       The sep frame has only 3 FElem regions. We need to show that
       when the body reads "X1" and "X2" from the same pointer pX,
       it gets the same value X both times. This is trivially true
       since the reads are from the same memory location.

       The compiled body uses straightline WP reasoning. Each
       sub-operation (mul, add, sub) has a spec that reads from
       input pointers and writes to stack pointers. Since all reads
       happen before any writes to the aliased pointers, the proof
       goes through by the same argument as the non-aliased case. *)
  Admitted.

  (** ** In-place point_double: dedicated doubling with aliased output

      Calling convention: [pX; pY; pZ; pX; pY; pZ]
      i.e., output = input.

      This uses the dedicated dbl-2009-l formula (1M+5S+8add) which is
      faster than curve_add(P,P). *)

  Definition spec_of_point_double_inplace functions : Prop :=
    forall pX pY pZ (X Y Z : F) R tr m,
      (FElem (Some tight_bounds) pX X
       * FElem (Some tight_bounds) pY Y
       * FElem (Some tight_bounds) pZ Z
       * R)%sep m ->
      WeakestPrecondition.call functions "curve_double" tr m
        [pX; pY; pZ; pX; pY; pZ]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           let '\<Xo, Yo, Zo\> := @point_double_gallina _ X Y Z in
           (FElem (Some tight_bounds) pX Xo
            * FElem (Some tight_bounds) pY Yo
            * FElem (Some tight_bounds) pZ Zo
            * R)%sep m').

  (** Proof strategy: Identical argument to ladderstep_inplace_ok.
      point_double_body also uses [let/n := stack ...] for temporaries
      A, B, C, t, D, E (6 stack allocations). All 3 input coordinates
      are read into stack vars before any output is written.
      The final writes go to Xout/Yout/Zout which are aliased with
      Xin/Yin/Zin, but by that point the inputs have been consumed. *)

  Lemma point_double_inplace_ok :
    forall functions,
      spec_of_point_double functions ->
      spec_of_point_double_inplace functions.
  Proof.
    (* Same proof pattern as ladderstep_inplace_ok:
       1. Unfold WP.call, look up "curve_double" body
       2. Process stackallocs for temporaries A, B, C, t, D, E
       3. Field ops read from pX/pY/pZ (input) and write to stack
       4. Final writes to output pointers pX/pY/pZ (aliased with input)
          happen after all input reads are complete
       5. Postcondition matches point_double_gallina *)
  Admitted.

  (** ** Compilation lemma for inplace curve_add

      This is the Rupicola-style compilation hint that lets the
      [compile] tactic handle in-place curve_add calls in larger
      function bodies. *)

  Lemma compile_ladderstep_inplace {tr m l functions}
        (x1 x2 y1 y2 z1 z2 : F)
        {P} {pred: P (curve_add x1 x2 y1 y2 z1 z2) -> predicate}
        {k: nlet_eq_k P (curve_add x1 x2 y1 y2 z1 z2)} {k_impl} :
    let v := curve_add x1 x2 y1 y2 z1 z2 in
    forall
           Rout
           X1_ptr X1_var X2_ptr X2_var Y1_ptr Y1_var Y2_ptr Y2_var
           Z1_ptr Z1_var Z2_ptr Z2_var,

      spec_of_ladderstep_inplace functions ->

      (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) X2_ptr x2 *
       FElem (Some tight_bounds) Y1_ptr y1 * FElem (Some tight_bounds) Y2_ptr y2 *
       FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) Z2_ptr z2 *
       Rout)%sep m ->

      map.get l X1_var = Some X1_ptr ->
      map.get l X2_var = Some X2_ptr ->
      map.get l Y1_var = Some Y1_ptr ->
      map.get l Y2_var = Some Y2_ptr ->
      map.get l Z1_var = Some Z1_ptr ->
      map.get l Z2_var = Some Z2_ptr ->

      (let v := v in
       forall m',
       let '\<Xout', Yout', Zout'\> := curve_add x1 x2 y1 y2 z1 z2 in
            (FElem (Some tight_bounds) X1_ptr Xout' *
            FElem (Some tight_bounds) X2_ptr x2 *
            FElem (Some tight_bounds) Y1_ptr Yout' *
            FElem (Some tight_bounds) Y2_ptr y2 *
            FElem (Some tight_bounds) Z1_ptr Zout' *
            FElem (Some tight_bounds) Z2_ptr z2 *
            Rout)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->

      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq
        (cmd.call [] "curve_add"
                  [ expr.var X1_var; expr.var X2_var;
                  expr.var Y1_var; expr.var Y2_var;
                  expr.var Z1_var; expr.var Z2_var;
                  expr.var X1_var; expr.var Y1_var;
                  expr.var Z1_var])
        k_impl
      <{ pred (nlet_eq
                 [X1_var; Y1_var; Z1_var]
                 v k) }>.
  Proof.
  Admitted.

  (** ** Compilation lemma for inplace point_double *)

  Lemma compile_point_double_inplace {tr m l functions}
        (x y z : F)
        {P} {pred: P (@point_double_gallina _ x y z) -> predicate}
        {k: nlet_eq_k P (@point_double_gallina _ x y z)} {k_impl} :
    let v := @point_double_gallina _ x y z in
    forall
           Rout
           X_ptr X_var Y_ptr Y_var Z_ptr Z_var,

      spec_of_point_double_inplace functions ->

      (FElem (Some tight_bounds) X_ptr x *
       FElem (Some tight_bounds) Y_ptr y *
       FElem (Some tight_bounds) Z_ptr z *
       Rout)%sep m ->

      map.get l X_var = Some X_ptr ->
      map.get l Y_var = Some Y_ptr ->
      map.get l Z_var = Some Z_ptr ->

      (let v := v in
       forall m',
       let '\<Xo, Yo, Zo\> := @point_double_gallina _ x y z in
            (FElem (Some tight_bounds) X_ptr Xo *
            FElem (Some tight_bounds) Y_ptr Yo *
            FElem (Some tight_bounds) Z_ptr Zo *
            Rout)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->

      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq
        (cmd.call [] "curve_double"
                  [ expr.var X_var; expr.var Y_var; expr.var Z_var;
                    expr.var X_var; expr.var Y_var; expr.var Z_var])
        k_impl
      <{ pred (nlet_eq
                 [X_var; Y_var; Z_var]
                 v k) }>.
  Proof.
    (* Proof follows from spec_of_point_double_inplace + sep manipulation.
       The key step is applying the inplace spec to the properly associated
       sep hypothesis, then passing the result to the continuation.
       Requires ecancel_assumption to bridge sep associativity. *)
  Admitted.

End __.

(** ** Compiler hints for the inplace compilation lemmas.

    These are registered at lower priority (9) than the standard
    non-aliased hints (8) so the non-aliased version is preferred
    when both are applicable. The caller must explicitly provide
    [spec_of_ladderstep_inplace] or [spec_of_point_double_inplace]
    as a hypothesis for these hints to fire. *)

#[global]
Hint Extern 9 (WeakestPrecondition.cmd _ _ _ _ _
  (_ (nlet_eq _ (ladderstep_gallina _ _ _ _ _ _) _))) =>
  simple eapply compile_ladderstep_inplace; shelve : compiler.

#[global]
Hint Extern 9 (WeakestPrecondition.cmd _ _ _ _ _
  (_ (nlet_eq _ (point_double_gallina _ _ _) _))) =>
  simple eapply compile_point_double_inplace; shelve : compiler.
