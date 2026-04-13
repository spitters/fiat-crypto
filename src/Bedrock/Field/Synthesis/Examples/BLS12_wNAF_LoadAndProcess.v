(** * Per-digit "load digit + process_one_digit" WP proof (task D).
    See [WNAF_GLV_STATUS.md] for full verification chain status.

    Proves [HLoadAndProcess_P]: given a digit array, table, and
    accumulator FElems, the bedrock2 sequence

      d1 := load(digits_k1[iter]);
      process_one_digit(d1, table_P, aux, out)

    establishes the postcondition where the output accumulator is
    conditionally updated: if d=0 then unchanged, else
    curve_add(old_out)(digit_point d table).

    The proof steps through:
    1. cmd.set "d1" (memory load) — uses Hdigit_load1
    2. cmd.cond d1:
       - d1 = 0: cmd.skip, output unchanged
       - d1 /= 0:
         a. cmd.cond d1 < 0: set lookup_d = abs(d1)
         b. cmd.set tab_idx, tab_off (table offset computation)
         c. 3x felem_copy (table point -> aux)
         d. cmd.cond d1 < 0: opp(auxy) (conditional negate)
         e. curve_add(out, aux, out) (in-place addition) *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import bedrock2.Scalars.
Require Import bedrock2.Array.
From coqutil.Tactics Require Import letexists.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section LoadAndProcess.
  (* === Same context as ProcessDigits.v Section ProcessDigits === *)
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.
  Context {field_parameters_ok : FieldParameters_ok}
          {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z :=
    (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  Context (curve_add_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
  Context (curve_add_id_r :
    forall x y z, curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z)).
  Context (curve_add_id_l :
    forall x y z, curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z)).
  Context (curve_add_assoc :
    forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm :
    forall P Q, curve_add P Q = curve_add Q P).

  Variable functions : map.rep (map := Semantics.env).

  (* --- Function call specs (identical to ProcessDigits.v) --- *)

  Context (HCurveAddInplace :
    forall pXo pX2 pYo pY2 pZo pZ2
      (X Y Z X2' Y2' Z2' : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pXo X ⋆ FElem (Some tight_bounds) pYo Y
     ⋆ FElem (Some tight_bounds) pZo Z ⋆ FElem (Some tight_bounds) pX2 X2'
     ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
     ⋆ R0) m0 ->
    WeakestPrecondition.call functions curve_add_name tr0 m0
      [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
      (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
        let '(Xo', Yo', Zo') := curve_add (X, Y, Z) (X2', Y2', Z2') in
        (FElem (Some tight_bounds) pXo Xo' ⋆ FElem (Some tight_bounds) pYo Yo'
         ⋆ FElem (Some tight_bounds) pZo Zo' ⋆ FElem (Some tight_bounds) pX2 X2'
         ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
         ⋆ R0) m'))).

  Context (HFelemCopy :
    forall pDst pSrc (v : F) (old : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pSrc v
     ⋆ FElem (Some tight_bounds) pDst old ⋆ R0) m0 ->
    Semantics.call functions felem_copy tr0 m0 [pDst; pSrc]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pSrc v
         ⋆ FElem (Some tight_bounds) pDst v ⋆ R0) m')).

  (** opp: negates field element; opp(dst, src) writes F.opp(src) to dst.
      In process_one_digit, called as opp(auxy, auxy) — aliased.
      We declare both a non-aliased version (matching ProcessDigits.v)
      and note that the aliased call requires an additional hypothesis
      or a separate proof that opp supports aliasing. *)
  Context (HOpp :
    forall pOut pIn (Y : F) (Yold : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pIn Y
     ⋆ FElem (Some tight_bounds) pOut Yold ⋆ R0) m0 ->
    Semantics.call functions opp tr0 m0 [pOut; pIn]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pIn Y
         ⋆ FElem (Some tight_bounds) pOut (F.opp Y) ⋆ R0) m')).

  (** In-place opp: opp(p, p) negates the element at p. *)
  Context (HOppInplace :
    forall p (Y : F) R0 tr0 m0,
    (FElem (Some tight_bounds) p Y ⋆ R0) m0 ->
    Semantics.call functions opp tr0 m0 [p; p]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) p (F.opp Y) ⋆ R0) m')).

  (* --- Digit and table data --- *)

  Context (dk1 : list Z).
  Context (Hlen1 : length dk1 = 129%nat).
  Context (Hdigits_bounded1 :
    forall i, (i < 129)%nat -> -7 <= nth i dk1 0 <= 7).

  (** Bounds on felem_size_in_bytes needed for offset computation to fit
      in a word without overflow. For BLS12 with felem_size=48 and
      width=64, 12*48=576 << 2^64. *)
  Context (Hfs_pos : 0 < felem_size_in_bytes).
  Context (Hfs_small : 12 * felem_size_in_bytes < 2 ^ width).

  Local Ltac cancel_impl_step :=
    let RHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps _) (seps ?RHS) => RHS end in
    let jy := index_and_element_of RHS in
    let j := lazymatch jy with (?i, _) => i end in
    let y := lazymatch jy with (_, ?y) => y end in
    assert_fails (idtac; let y := rdelta_var y in is_evar y);
    let LHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
    let i := find_syntactic_unify_deltavar LHS y in
    cancel_seps_at_indices_by_implication i j;
    [exact (impl1_refl _)|].

  Local Ltac ecancel_fast :=
    cancel;
    lazymatch goal with
    | |- Lift1Prop.impl1 _ _ =>
      repeat cancel_impl_step;
      repeat ecancel_step_by_implication;
      cbv [seps]; exact impl1_refl
    | |- Lift1Prop.iff1 _ _ =>
      ecancel_steps_at O;
      ecancel_done
    end.

  Local Ltac ecancel_assumption_fast :=
    multimatch goal with
    | |- ?PG ?m1 =>
      multimatch goal with
      | H: _ ?m2 |- _ =>
        syntactic_unify_deltavar m1 m2;
        let H' := fresh "Hcopy" in
        pose proof H as H';
        cbv beta iota zeta in H';
        lazymatch type of H' with
        | (_ * _)%sep _ =>
          refine (Morphisms.subrelation_refl
                    Lift1Prop.impl1 _ _ _ _ H');
          clear H';
          ecancel_fast
        end
      end
    end.
  Local Ltac ecancel_assumption ::= ecancel_assumption_fast.

  (* ================================================================== *)
  (** ** Word-level computation of tab_off = idx * 3 * felem_size        *)
  (* ================================================================== *)

  (** For digits with [1 <= |d| <= 7], the bedrock2 computation of
      [tab_off = ((|d|-1) >>u 1) * (3 * felem_size)] gives a word
      equal to [word.of_Z (((|d|-1)/2) * (3 * felem_size))]. *)
  Lemma tab_off_compute :
    forall (abs_d : Z),
    1 <= abs_d <= 7 ->
    @word.mul _ word
      (word.sru (word.sub (word.of_Z abs_d) (word.of_Z 1)) (word.of_Z 1))
      (word.of_Z (3 * felem_size_in_bytes))
    = word.of_Z (((abs_d - 1) / 2) * (3 * felem_size_in_bytes)).
  Proof.
    intros abs_d Habs_d.
    assert (Hw_min : 8 <= width) by (destruct width_cases as [->| ->]; lia).
    apply word.unsigned_inj.
    rewrite word.unsigned_mul, word.unsigned_of_Z, word.unsigned_of_Z.
    rewrite word.unsigned_sru_shamtZ by lia.
    rewrite word.unsigned_sub, word.unsigned_of_Z, word.unsigned_of_Z.
    cbv [word.wrap].
    assert (H2 : 2 ^ width > 0)
      by (apply Z.lt_gt; apply Z.pow_pos_nonneg; lia).
    rewrite (Z.mod_small abs_d) by lia.
    rewrite (Z.mod_small 1) by lia.
    rewrite (Z.mod_small (abs_d - 1)) by lia.
    rewrite (Z.mod_small (3 * felem_size_in_bytes)) by lia.
    replace (Z.shiftr (abs_d - 1) 1) with ((abs_d - 1) / 2)
      by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    reflexivity.
  Qed.

  (** Normalization lemma: merge a nested word.add (word.add p (of_Z x)) (of_Z y)
      into a single word.add p (of_Z (x + y)). Used to normalize table entry
      addresses so they match the bedrock2 computed addresses. *)
  Lemma word_add_of_Z_assoc :
    forall (p : word) (x y : Z),
    @word.add _ word (word.add p (word.of_Z x)) (word.of_Z y)
    = word.add p (word.of_Z (x + y)).
  Proof.
    intros. rewrite <- word.add_assoc by assumption.
    rewrite <- word.ring_morph_add by assumption. reflexivity.
  Qed.

  Context (table_P_entries : list (F * F * F)).
  Context (Htable_P_len : length table_P_entries = 4%nat).

  (** Digit load hypothesis *)
  Context (Hdigit_load1 : forall (n : nat) (base : word) (m : mem) R,
    (n < length dk1)%nat ->
    (@DigitArray _ word mem base dk1 ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk1 0))).

  (* --- Phi-side digit and table data --- *)

  Context (dk2 : list Z).
  Context (Hlen2 : length dk2 = 129%nat).
  Context (Hdigits_bounded2 :
    forall i, (i < 129)%nat -> -7 <= nth i dk2 0 <= 7).

  Context (table_Phi_entries : list (F * F * F)).
  Context (Htable_Phi_len : length table_Phi_entries = 4%nat).

  Context (Hdigit_load2 : forall (n : nat) (base : word) (m : mem) R,
    (n < length dk2)%nat ->
    (@DigitArray _ word mem base dk2 ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk2 0))).

  (* ================================================================== *)
  (** ** Table decomposition lemma                                       *)
  (* ================================================================== *)

  (** When Table4 holds 4 entries, we can split off the entry at index
      [idx] = (|d|-1)/2 and get the FElem predicates for that point. *)

  (** Auxiliary: the word-level table offset computation matches
      [table_point_addr]. For digit d != 0 with abs_d in {1,3,5,7},
      idx = (abs_d - 1) / 2 in {0,1,2,3}, and
      tab_off = idx * 3 * felem_size_in_bytes
      equals the Z-level offset of table_point_addr. *)

  (* ================================================================== *)
  (** ** WP automation tactics for process_one_digit                      *)
  (* ================================================================== *)

  (** Resolve a single map.get from a chain of map.put.
      Tries map.get_put_same first; if that fails, rewrites
      with map.get_put_diff and looks for an assumption. *)
  Local Ltac solve_mapget :=
    first [ apply map.get_put_same
          | rewrite map.get_put_diff by congruence; eassumption
          | rewrite map.get_put_diff by congruence; solve_mapget ].

  (** Evaluate a DEXPR for a single expression.
      Handles: var lookups, literal, binop, and their compositions. *)
  Local Ltac wp_dexpr :=
    cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal
         dlet.dlet];
    repeat (first
      [ eexists; split; [solve_mapget|]
      | eexists; split; [reflexivity|]
      | cbn [Semantics.interp_binop]; reflexivity
      | reflexivity ]).

  (** Process one cmd.set: unfold WP, solve DEXPR, bind result. *)
  Local Ltac wp_cmd_set :=
    cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body];
    eexists; split; [wp_dexpr|]; cbv [dlet.dlet].

  (** Process the dexprs (argument list) for a function call.
      Handles [dexprs m l [e1; e2; ...] args]. *)
  Local Ltac wp_dexprs :=
    cbv [WeakestPrecondition.dexprs
         WeakestPrecondition.dexpr
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal
         dlet.dlet list_map list_map_body];
    (* Reduce partially-unfolded expr fixpoints and binop interp *)
    repeat (first
      [ cbn beta iota delta [Semantics.interp_binop]
      | exact (conj eq_refl eq_refl)
      | split; [ (eexists; split; [solve_mapget|]; try (cbn [Semantics.interp_binop]; reflexivity)) | ]
      | split; [ reflexivity | ]
      | eexists; split; [solve_mapget|]
      | reflexivity ]);
    (* Close any remaining let-bound arg list equation *)
    try exact eq_refl.

  (** Process a full bedrock2 cmd.call: peel cmd.seq + dexprs + weaken_call.
      [spec] is the hypothesis (e.g., HFelemCopy, HCurveAddInplace).
      Handles cmd.seq nesting and the full pattern:
        WP (cmd.seq (cmd.call ...) rest) post *)
  (** Solve a dexprs goal by stepping through the list. *)
  Local Ltac solve_dexprs_goal :=
    lazymatch goal with
    | |- dexprs _ _ _ _ => wp_dexprs
    | _ =>
      (* Partially unfolded dexprs — try straightline then manual *)
      repeat straightline;
      try wp_dexprs;
      (* If still stuck, provide witnesses manually *)
      repeat (first
        [ eexists; split; [solve_mapget|]
        | split; [reflexivity|]
        | cbn [Semantics.interp_binop]; reflexivity
        | reflexivity ])
    end.

  (** wp_call uses letexists (not eexists) to prevent evar leakage
      between chained calls. Based on gcall_explicit from
      BLS12_GLV_ScalarMultBedrock.v. *)
  (** eval_dexprs_here: resolve dexprs using the gcall_explicit pattern.
      Unlike wp_dexprs which cbv-unfolds first, this works on the
      standard WeakestPrecondition.cmd form. *)
  Local Ltac eval_dexprs_here :=
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.dexpr
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first
      [ exact eq_refl
      | eexists; split; [solve_mapget |]
      | eexists; split; [exact eq_refl |] ]).

  (** wp_call: gcall_explicit-style tactic adapted for our specs.
      Uses unfold1_cmd_goal + letexists + eval_dexprs_here to avoid
      evar scoping issues between chained calls. *)
  Local Ltac wp_call spec :=
    (* Peel cmd.seq *)
    repeat match goal with
    | |- WeakestPrecondition.cmd _ (cmd.seq _ _) _ _ _ _ =>
        unfold1_cmd_goal; cbv beta match delta [cmd_body]
    end;
    (* Process cmd.call — may already be unfolded *)
    match goal with
    | |- WeakestPrecondition.cmd _ _ _ _ _ _ =>
        unfold1_cmd_goal; cbv beta match delta [cmd_body]
    | _ => idtac
    end;
    letexists; split; [solve [eval_dexprs_here] |];
    eapply Semantics.weaken_call;
    [ eapply spec; ecancel_assumption
    | intros ? ? ? ?;
      repeat match goal with
      | H : _ /\ _ |- _ => destruct H
      | H : _ = _ |- _ => first [ subst | idtac ]
      end;
      cbv [map.putmany_of_list_zip];
      repeat match goal with
      | |- exists _, Some ?x = Some _ /\ _ =>
          eexists; split; [exact eq_refl|]
      | |- exists _, _ = _ /\ _ =>
          eexists; split; [exact eq_refl|]
      end;
      match goal with
      | |- WeakestPrecondition.cmd _ _ _ _ _ _ =>
          unfold1_cmd_goal; cbv beta match delta [cmd_body]
      | _ => idtac
      end ].

  (** Close the postcondition: existentials, eq, sep, map.get chain. *)
  Local Ltac wp_postcond :=
    repeat eexists;
    repeat (split;
      [ first [ ecancel_assumption | reflexivity
              | solve_mapget
              | intros; solve_mapget ]
      | ]).

  (** Unfold Table4 into 12 individual FElems in a sep hypothesis. *)
  Local Ltac unfold_Table4_in H :=
    unfold Table4, TablePoint, table_point_addr, felem_addr in H.

  (** Advance through one Semantics.call step in the unfolded call form.
      The goal should look like [exists args, dexprs ... /\ Semantics.call ...].
      Parameters:
      - [spec]: the function spec hypothesis (e.g., HFelemCopy, HOpp).
      Assumes there is a hypothesis [Hsep : (_ ⋆ _)%sep m] in context that
      matches the call's precondition via ecancel, and optionally a
      hypothesis [H : v = word.of_Z _] where [v] appears in the args list
      (e.g. the [Hv2_eq] equation for tab_off).
      After this tactic:
      - The old [Hsep] is replaced with the new post-state sep predicate.
      - The return values / trace have been substituted.
      - The map.putmany_of_list_zip step for return bindings has been closed. *)
  (** Derive False from `word.unsigned (if word.lts x y then ... else ...) = 0`
      (or `<> 0`) when we have context about x,y via `d < 0` or `0 < d`
      hypotheses. Works via case analysis on word.lts. *)
  Local Ltac kill_lts_contradiction Hc :=
    cbn [Semantics.interp_binop] in Hc;
    unfold encode_digit in Hc;
    lazymatch type of Hc with
    | context[if word.lts ?a ?b then _ else _] =>
      let Elt := fresh "Elt" in
      destruct (word.lts a b) eqn:Elt;
      [ (* lts is true *)
        first
          [ rewrite word.unsigned_of_Z_1 in Hc; congruence
          | apply Hc; rewrite word.unsigned_of_Z_1; congruence
          | rewrite word.signed_lts in Elt;
            rewrite word.signed_of_Z in Elt;
            rewrite word.signed_of_Z in Elt;
            unfold word.swrap in Elt;
            destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia ]
      | (* lts is false *)
        first
          [ rewrite word.unsigned_of_Z_0 in Hc; congruence
          | apply Hc; rewrite word.unsigned_of_Z_0; reflexivity
          | rewrite word.signed_lts in Elt;
            rewrite word.signed_of_Z in Elt;
            rewrite word.signed_of_Z in Elt;
            unfold word.swrap in Elt;
            destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia ] ]
    end.

  (** Handle an inner `cmd.cond` dispatch when we already know `d < 0`.
      The goal has shape `exists v, DEXPR m l (lts d1 0) v /\ (v≠0 -> ...) /\ (v=0 -> ...)`.
      Evaluates the DEXPR, takes the then-branch (since d<0 makes lts true),
      and closes the unreachable else-branch. *)
  Local Ltac wp_inner_cond_dneg :=
    letexists; split; [solve [eval_dexprs_here] |];
    split;
    [ intro
    | let Hc := fresh "Hc" in
      intro Hc; exfalso; kill_lts_contradiction Hc ].

  (** Same for d > 0 (dispatch to else-branch since lts is false). *)
  Local Ltac wp_inner_cond_dpos :=
    letexists; split; [solve [eval_dexprs_here] |];
    split;
    [ let Hc := fresh "Hc" in
      intro Hc; exfalso; kill_lts_contradiction Hc
    | intro ].

  (** Normalize `K*fs + L*fs` expressions to `(K+L)*fs`, and `K*fs + fs`
      to `(K+1)*fs`, for specific K,L values that appear in table
      addresses. Uses explicit `replace` with `lia` to rewrite in the
      current goal (or a named hypothesis). *)
  Local Ltac normalize_fs_sum_in_goal :=
    repeat first
      [ replace (3 * felem_size_in_bytes + felem_size_in_bytes)
           with (4 * felem_size_in_bytes) by lia
      | replace (3 * felem_size_in_bytes + 2 * felem_size_in_bytes)
           with (5 * felem_size_in_bytes) by lia
      | replace (6 * felem_size_in_bytes + felem_size_in_bytes)
           with (7 * felem_size_in_bytes) by lia
      | replace (6 * felem_size_in_bytes + 2 * felem_size_in_bytes)
           with (8 * felem_size_in_bytes) by lia
      | replace (9 * felem_size_in_bytes + felem_size_in_bytes)
           with (10 * felem_size_in_bytes) by lia
      | replace (9 * felem_size_in_bytes + 2 * felem_size_in_bytes)
           with (11 * felem_size_in_bytes) by lia ].

  (** Normalize Table4 addresses in a hypothesis: unfold to individual
      FElems, merge nested word.add, and rewrite the 12 concrete offsets
      K*(3*fs) + L*fs to canonical (3K+L)*fs form. *)
  Local Ltac normalize_table4_addrs_in H :=
    unfold Table4, TablePoint, table_point_addr, felem_addr in H;
    rewrite !word_add_of_Z_assoc in H;
    replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 in H by lia;
    replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes in H by lia;
    replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) in H by lia;
    replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) in H by lia;
    replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) in H by lia;
    replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) in H by lia;
    replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) in H by lia;
    replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) in H by lia;
    replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) in H by lia;
    replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) in H by lia;
    replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) in H by lia;
    replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) in H by lia.

  (** Same as [normalize_table4_addrs_in] but operating on the goal. *)
  Local Ltac normalize_table4_addrs_in_goal :=
    unfold Table4, TablePoint, table_point_addr, felem_addr;
    rewrite !word_add_of_Z_assoc;
    replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia;
    replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia;
    replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia;
    replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia;
    replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia;
    replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia;
    replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia;
    replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia;
    replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia;
    replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia;
    replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia;
    replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.

  Local Ltac wp_direct_call spec :=
    letexists; split; [solve [eval_dexprs_here] |];
    (repeat match goal with
            | x := _ : list word.rep |- _ => subst x
            end);
    cbn [Semantics.interp_binop];
    (try match goal with
         | H : ?v = word.of_Z _ |- _ => is_var v; rewrite H
         end);
    rewrite ?(word.add_0_l (word_ok := word_ok));
    rewrite <- ?(word.ring_morph_add (word_ok := word_ok));
    normalize_fs_sum_in_goal;
    rewrite ?word_add_of_Z_assoc;
    rewrite ?Z.add_0_l;
    eapply Semantics.weaken_call;
    [ eapply spec; ecancel_assumption
    | let t := fresh "t_new" in let mn := fresh "m_new" in
      let r := fresh "rets_new" in
      let Hnew := fresh "Hsep_tmp" in
      intros t mn r [? [? Hnew]]; subst r; subst t;
      cbv [map.putmany_of_list_zip]; eexists; split; [reflexivity|];
      cbv beta;
      cbn [Semantics.interp_binop] in Hnew;
      (try match goal with
           | H : ?v = word.of_Z _ |- _ => is_var v; rewrite H in Hnew
           end);
      rewrite ?(word.add_0_l (word_ok := word_ok)) in Hnew;
      rewrite <- ?(word.ring_morph_add (word_ok := word_ok)) in Hnew;
      rewrite ?word_add_of_Z_assoc in Hnew;
      rewrite ?Z.add_0_l in Hnew;
      match goal with
      | H : _ |- _ =>
        match type of H with
        | (_ ⋆ _)%sep _ =>
          tryif constr_eq H Hnew then fail else clear H
        end
      end;
      rename Hnew into Hsep ].

  (* ================================================================== *)
  (** ** Main theorem: HLoadAndProcess_P                                 *)
  (* ================================================================== *)

  Theorem load_and_process_P_ok :
    forall n pOx pOy pOz pAx pAy pAz pTP pDK1
      (Ox Oy Oz Ax Ay Az : F) R0 tr0 m0 l0,
    (n < 129)%nat ->
    (FElem (Some tight_bounds) pOx Ox ⋆ FElem (Some tight_bounds) pOy Oy
     ⋆ FElem (Some tight_bounds) pOz Oz ⋆ FElem (Some tight_bounds) pAx Ax
     ⋆ FElem (Some tight_bounds) pAy Ay ⋆ FElem (Some tight_bounds) pAz Az
     ⋆ DigitArray pDK1 dk1 ⋆ Table4 pTP table_P_entries ⋆ R0) m0 ->
    map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
    map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
    map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
    map.get l0 "table_P" = Some pTP ->
    map.get l0 "digits_k1" = Some pDK1 ->
    map.get l0 "iter" = Some (word.of_Z (Z.of_nat n)) ->
    WeakestPrecondition.cmd functions
      (cmd.seq
        (cmd.set "d1" (expr.load access_size.word
          (expr.op bopname.add (expr.var "digits_k1")
            (expr.op bopname.mul (expr.var "iter")
              (expr.literal (Memory.bytes_per_word 64))))))
        (process_one_digit curve_add_name felem_copy opp felem_size_in_bytes
          "d1" "table_P" "auxx" "auxy" "auxz" "outx" "outy" "outz"))
      tr0 m0 l0
      (fun t' m' l' =>
        exists Ox' Oy' Oz' Ax' Ay' Az',
        let d := nth n dk1 0 in
        (Ox',Oy',Oz') = (if d =? 0 then (Ox,Oy,Oz)
          else curve_add (Ox,Oy,Oz) (digit_point d table_P_entries))
        /\ (FElem (Some tight_bounds) pOx Ox' ⋆ FElem (Some tight_bounds) pOy Oy'
            ⋆ FElem (Some tight_bounds) pOz Oz' ⋆ FElem (Some tight_bounds) pAx Ax'
            ⋆ FElem (Some tight_bounds) pAy Ay' ⋆ FElem (Some tight_bounds) pAz Az'
            ⋆ DigitArray pDK1 dk1 ⋆ Table4 pTP table_P_entries ⋆ R0) m'
        /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
        /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
        /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
        /\ map.get l' "table_P" = Some pTP
        /\ map.get l' "digits_k1" = Some pDK1
        /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
        /\ (forall k v, k <> "d1" -> k <> "lookup_d" -> k <> "tab_idx" ->
              k <> "tab_off" -> map.get l0 k = Some v -> map.get l' k = Some v)
        /\ tr0 = t').
  Proof.
    intros n pOx pOy pOz pAx pAy pAz pTP pDK1
      Ox Oy Oz Ax Ay Az R0 tr0 m0 l0
      Hn Hsep Hlox Hloy Hloz Hlax Hlay Hlaz Hltp Hldk Hliter.

    (* === Step 1: cmd.set "d1" := load(digits_k1 + iter * word_size) === *)
    cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
    eexists. split.
    1: { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
              WeakestPrecondition.get dlet.dlet].
         eexists. split. 1: exact Hldk.
         eexists. split. 1: exact Hliter.
         cbn [Semantics.interp_binop].
         pose proof (Hdigit_load1 n pDK1 m0 _ ltac:(rewrite Hlen1; lia)
                       ltac:(ecancel_assumption)) as Hld.
         cbv [expr expr_body literal dlet.dlet load].
         rewrite Hld. eexists. split; reflexivity. }

    (* === Step 2: process_one_digit, evaluate cmd.cond on "d1" === *)
    cbv [dlet.dlet].
    set (d := nth n dk1 0). set (l1 := map.put l0 "d1" (encode_digit d)).
    unfold process_one_digit.
    cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
    eexists. split.
    1: { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
              WeakestPrecondition.get dlet.dlet].
         eexists. split. 1: subst l1; apply map.get_put_same. reflexivity. }

    split.
    2: { (* === Step 3: d = 0 case (cmd.skip / ELSE branch) === *)
         intros Hd0eq.
         exists Ox, Oy, Oz, Ax, Ay, Az.
         assert (Hdz : d = 0).
         { unfold encode_digit in Hd0eq.
           pose proof (Hdigits_bounded1 n Hn) as Hdb. fold d in Hdb.
           rewrite word.unsigned_of_Z in Hd0eq. unfold word.wrap in Hd0eq.
           destruct width_cases as [Hw|Hw]; subst;
             rewrite Z.mod_small in Hd0eq by lia; lia. }
         rewrite Hdz. simpl.
         repeat (split; [try (exact Hsep); try reflexivity|]); try reflexivity.
         all: try (subst l1; rewrite map.get_put_diff by congruence; assumption).
         all: try (subst l1; intros k v Hk1 Hk2 Hk3 Hk4 Hgk;
                   rewrite map.get_put_diff by auto; exact Hgk). }

    + (* === Step 4: d ≠ 0 case (THEN branch) === *)
      intros Hdne.
      pose proof (Hdigits_bounded1 n Hn) as Hdb. fold d in Hdb.
      assert (Hd_ne : d <> 0).
      { intro Heq. apply Hdne. unfold encode_digit. rewrite Heq.
        rewrite word.unsigned_of_Z_0. reflexivity. }
      (* Inner cmd.cond on lts d1 0 — goals already unfolded by cbn *)
      subst l1.
      letexists; split; [solve [eval_dexprs_here] |].
      split.
      -- (* d < 0 branch *)
         intro Hlts.
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         (* Unfold Table4 via destructing the 4 entries and their tuples. *)
         destruct table_P_entries as [|e0 [|e1 [|e2 [|e3 [|??]]]]];
           try (simpl in Htable_P_len; discriminate).
         subst v. cbn [Semantics.interp_binop] in *.
         (* Derive d < 0 from the lts condition. *)
         assert (Hdneg : d < 0).
         { unfold encode_digit in Hlts.
           destruct (word.lts (word.of_Z d) (word.of_Z 0)) eqn:E.
           { rewrite word.signed_lts in E.
             rewrite word.signed_of_Z in E. rewrite word.signed_of_Z in E.
             unfold word.swrap in E.
             destruct width_cases as [Hw|Hw]; rewrite Hw in E; lia. }
           { exfalso. apply Hlts. rewrite word.unsigned_of_Z_0. reflexivity. } }
         clear Hlts Hdne.
         (* v0 = word.sub 0 (word.of_Z d) = word.of_Z (-d) = word.of_Z |d|. *)
         assert (Hv0_eq : v0 = word.of_Z (Z.abs d)).
         { subst v0. unfold encode_digit. rewrite <- word.ring_morph_sub.
           f_equal. lia. }
         (* Apply tab_off_compute to simplify v2 to a concrete offset. *)
         assert (Hv2_eq : v2 = word.of_Z (((Z.abs d - 1) / 2)
                                          * (3 * felem_size_in_bytes))).
         { subst v2. subst v1. rewrite Hv0_eq. apply tab_off_compute. lia. }
         (* Case split on the table index. *)
         set (idx := (Z.abs d - 1) / 2) in Hv2_eq.
         assert (Hidx : idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3)
           by (subst idx; lia).
         (* Normalize Hsep addresses and unfold Table4 entries. *)
         destruct e0 as [[X0 Y0] Z0]. destruct e1 as [[X1 Y1] Z1].
         destruct e2 as [[X2 Y2] Z2]. destruct e3 as [[X3 Y3] Z3].
         unfold Table4, TablePoint, table_point_addr, felem_addr in Hsep.
         rewrite !word_add_of_Z_assoc in Hsep.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with 0 in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with felem_size_in_bytes in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (2 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (3 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (4 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (5 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (6 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (7 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (8 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (9 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (10 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (11 * felem_size_in_bytes) in Hsep by lia.
         destruct Hidx as [Hi|[Hi|[Hi|Hi]]]; rewrite Hi in Hv2_eq;
           (* Normalize (0|1|2|3) * (3 * felem_size_in_bytes) to concrete form *)
           first
             [ replace (0 * (3 * felem_size_in_bytes))
                  with 0 in Hv2_eq by lia
             | replace (1 * (3 * felem_size_in_bytes))
                  with (3 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (2 * (3 * felem_size_in_bytes))
                  with (6 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (3 * (3 * felem_size_in_bytes))
                  with (9 * felem_size_in_bytes) in Hv2_eq by lia ];
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy.
         (* 4 idx subgoals remaining *)
         { (* idx = 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X0, F.opp Y0, Z0))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X0, (F.opp Y0), Z0.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
         { (* idx = 1 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X1, F.opp Y1, Z1))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X1, (F.opp Y1), Z1.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
         { (* idx = 2 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X2, F.opp Y2, Z2))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X2, (F.opp Y2), Z2.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
         { (* idx = 3 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X3, F.opp Y3, Z3))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X3, (F.opp Y3), Z3.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
      -- (* d >= 0 branch *)
         intro Hge.
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         destruct table_P_entries as [|e0 [|e1 [|e2 [|e3 [|??]]]]];
           try (simpl in Htable_P_len; discriminate).
         subst v. cbn [Semantics.interp_binop] in *.
         (* Derive d > 0 from Hge (d is not < 0) and Hd_ne (d ≠ 0). *)
         assert (Hdpos : 0 < d).
         { unfold encode_digit in Hge.
           destruct (word.lts (word.of_Z d) (word.of_Z 0)) eqn:E.
           { exfalso. rewrite word.unsigned_of_Z in Hge.
             unfold word.wrap in Hge.
             destruct width_cases as [Hw|Hw]; rewrite Hw in Hge;
               cbv in Hge; discriminate. }
           { rewrite word.signed_lts in E.
             rewrite word.signed_of_Z in E. rewrite word.signed_of_Z in E.
             unfold word.swrap in E.
             destruct width_cases as [Hw|Hw]; rewrite Hw in E; lia. } }
         clear Hge Hdne.
         (* v0 = encode_digit d = word.of_Z d = word.of_Z |d| since d > 0. *)
         assert (Hv0_eq : v0 = word.of_Z (Z.abs d)).
         { subst v0. unfold encode_digit. f_equal. lia. }
         assert (Hv2_eq : v2 = word.of_Z (((Z.abs d - 1) / 2)
                                          * (3 * felem_size_in_bytes))).
         { subst v2. subst v1. rewrite Hv0_eq. apply tab_off_compute. lia. }
         set (idx := (Z.abs d - 1) / 2) in Hv2_eq.
         assert (Hidx : idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3)
           by (subst idx; lia).
         destruct e0 as [[X0 Y0] Z0]. destruct e1 as [[X1 Y1] Z1].
         destruct e2 as [[X2 Y2] Z2]. destruct e3 as [[X3 Y3] Z3].
         unfold Table4, TablePoint, table_point_addr, felem_addr in Hsep.
         rewrite !word_add_of_Z_assoc in Hsep.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with 0 in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with felem_size_in_bytes in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (2 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (3 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (4 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (5 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (6 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (7 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (8 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (9 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (10 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (11 * felem_size_in_bytes) in Hsep by lia.
         destruct Hidx as [Hi|[Hi|[Hi|Hi]]]; rewrite Hi in Hv2_eq;
           first
             [ replace (0 * (3 * felem_size_in_bytes))
                  with 0 in Hv2_eq by lia
             | replace (1 * (3 * felem_size_in_bytes))
                  with (3 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (2 * (3 * felem_size_in_bytes))
                  with (6 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (3 * (3 * felem_size_in_bytes))
                  with (9 * felem_size_in_bytes) in Hv2_eq by lia ];
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy.
         { (* idx = 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X0, Y0, Z0))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X0, Y0, Z0.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
         { (* idx = 1 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X1, Y1, Z1))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X1, Y1, Z1.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
         { (* idx = 2 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X2, Y2, Z2))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X2, Y2, Z2.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
         { (* idx = 3 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X3, Y3, Z3))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X3, Y3, Z3.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
  Qed.

  Theorem load_and_process_Phi_ok :
    forall n pOx pOy pOz pAx pAy pAz pTPhi pDK2
      (Ox Oy Oz Ax Ay Az : F) R0 tr0 m0 l0,
    (n < 129)%nat ->
    (FElem (Some tight_bounds) pOx Ox ⋆ FElem (Some tight_bounds) pOy Oy
     ⋆ FElem (Some tight_bounds) pOz Oz ⋆ FElem (Some tight_bounds) pAx Ax
     ⋆ FElem (Some tight_bounds) pAy Ay ⋆ FElem (Some tight_bounds) pAz Az
     ⋆ DigitArray pDK2 dk2 ⋆ Table4 pTPhi table_Phi_entries ⋆ R0) m0 ->
    map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
    map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
    map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
    map.get l0 "table_Phi" = Some pTPhi ->
    map.get l0 "digits_k2" = Some pDK2 ->
    map.get l0 "iter" = Some (word.of_Z (Z.of_nat n)) ->
    WeakestPrecondition.cmd functions
      (cmd.seq
        (cmd.set "d2" (expr.load access_size.word
          (expr.op bopname.add (expr.var "digits_k2")
            (expr.op bopname.mul (expr.var "iter")
              (expr.literal (Memory.bytes_per_word 64))))))
        (process_one_digit curve_add_name felem_copy opp felem_size_in_bytes
          "d2" "table_Phi" "auxx" "auxy" "auxz" "outx" "outy" "outz"))
      tr0 m0 l0
      (fun t' m' l' =>
        exists Ox' Oy' Oz' Ax' Ay' Az',
        let d := nth n dk2 0 in
        (Ox',Oy',Oz') = (if d =? 0 then (Ox,Oy,Oz)
          else curve_add (Ox,Oy,Oz) (digit_point d table_Phi_entries))
        /\ (FElem (Some tight_bounds) pOx Ox' ⋆ FElem (Some tight_bounds) pOy Oy'
            ⋆ FElem (Some tight_bounds) pOz Oz' ⋆ FElem (Some tight_bounds) pAx Ax'
            ⋆ FElem (Some tight_bounds) pAy Ay' ⋆ FElem (Some tight_bounds) pAz Az'
            ⋆ DigitArray pDK2 dk2 ⋆ Table4 pTPhi table_Phi_entries ⋆ R0) m'
        /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
        /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
        /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
        /\ map.get l' "table_Phi" = Some pTPhi
        /\ map.get l' "digits_k2" = Some pDK2
        /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
        /\ (forall k v, k <> "d2" -> k <> "lookup_d" -> k <> "tab_idx" ->
              k <> "tab_off" -> map.get l0 k = Some v -> map.get l' k = Some v)
        /\ tr0 = t').
  Proof.
    intros n pOx pOy pOz pAx pAy pAz pTPhi pDK2
      Ox Oy Oz Ax Ay Az R0 tr0 m0 l0
      Hn Hsep Hlox Hloy Hloz Hlax Hlay Hlaz Hltp Hldk Hliter.

    (* === Step 1: cmd.set "d2" := load(digits_k1 + iter * word_size) === *)
    cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
    eexists. split.
    1: { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
              WeakestPrecondition.get dlet.dlet].
         eexists. split. 1: exact Hldk.
         eexists. split. 1: exact Hliter.
         cbn [Semantics.interp_binop].
         pose proof (Hdigit_load2 n pDK2 m0 _ ltac:(rewrite Hlen2; lia)
                       ltac:(ecancel_assumption)) as Hld.
         cbv [expr expr_body literal dlet.dlet load].
         rewrite Hld. eexists. split; reflexivity. }

    (* === Step 2: process_one_digit, evaluate cmd.cond on "d2" === *)
    cbv [dlet.dlet].
    set (d := nth n dk2 0). set (l1 := map.put l0 "d2" (encode_digit d)).
    unfold process_one_digit.
    cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
    eexists. split.
    1: { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
              WeakestPrecondition.get dlet.dlet].
         eexists. split. 1: subst l1; apply map.get_put_same. reflexivity. }

    split.
    2: { (* === Step 3: d = 0 case (cmd.skip / ELSE branch) === *)
         intros Hd0eq.
         exists Ox, Oy, Oz, Ax, Ay, Az.
         assert (Hdz : d = 0).
         { unfold encode_digit in Hd0eq.
           pose proof (Hdigits_bounded2 n Hn) as Hdb. fold d in Hdb.
           rewrite word.unsigned_of_Z in Hd0eq. unfold word.wrap in Hd0eq.
           destruct width_cases as [Hw|Hw]; subst;
             rewrite Z.mod_small in Hd0eq by lia; lia. }
         rewrite Hdz. simpl.
         repeat (split; [try (exact Hsep); try reflexivity|]); try reflexivity.
         all: try (subst l1; rewrite map.get_put_diff by congruence; assumption).
         all: try (subst l1; intros k v Hk1 Hk2 Hk3 Hk4 Hgk;
                   rewrite map.get_put_diff by auto; exact Hgk). }

    + (* === Step 4: d ≠ 0 case (THEN branch) === *)
      intros Hdne.
      pose proof (Hdigits_bounded2 n Hn) as Hdb. fold d in Hdb.
      assert (Hd_ne : d <> 0).
      { intro Heq. apply Hdne. unfold encode_digit. rewrite Heq.
        rewrite word.unsigned_of_Z_0. reflexivity. }
      (* Inner cmd.cond on lts d1 0 — goals already unfolded by cbn *)
      subst l1.
      letexists; split; [solve [eval_dexprs_here] |].
      split.
      -- (* d < 0 branch *)
         intro Hlts.
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         (* Unfold Table4 via destructing the 4 entries and their tuples. *)
         destruct table_Phi_entries as [|e0 [|e1 [|e2 [|e3 [|??]]]]];
           try (simpl in Htable_Phi_len; discriminate).
         subst v. cbn [Semantics.interp_binop] in *.
         (* Derive d < 0 from the lts condition. *)
         assert (Hdneg : d < 0).
         { unfold encode_digit in Hlts.
           destruct (word.lts (word.of_Z d) (word.of_Z 0)) eqn:E.
           { rewrite word.signed_lts in E.
             rewrite word.signed_of_Z in E. rewrite word.signed_of_Z in E.
             unfold word.swrap in E.
             destruct width_cases as [Hw|Hw]; rewrite Hw in E; lia. }
           { exfalso. apply Hlts. rewrite word.unsigned_of_Z_0. reflexivity. } }
         clear Hlts Hdne.
         (* v0 = word.sub 0 (word.of_Z d) = word.of_Z (-d) = word.of_Z |d|. *)
         assert (Hv0_eq : v0 = word.of_Z (Z.abs d)).
         { subst v0. unfold encode_digit. rewrite <- word.ring_morph_sub.
           f_equal. lia. }
         (* Apply tab_off_compute to simplify v2 to a concrete offset. *)
         assert (Hv2_eq : v2 = word.of_Z (((Z.abs d - 1) / 2)
                                          * (3 * felem_size_in_bytes))).
         { subst v2. subst v1. rewrite Hv0_eq. apply tab_off_compute. lia. }
         (* Case split on the table index. *)
         set (idx := (Z.abs d - 1) / 2) in Hv2_eq.
         assert (Hidx : idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3)
           by (subst idx; lia).
         (* Normalize Hsep addresses and unfold Table4 entries. *)
         destruct e0 as [[X0 Y0] Z0]. destruct e1 as [[X1 Y1] Z1].
         destruct e2 as [[X2 Y2] Z2]. destruct e3 as [[X3 Y3] Z3].
         unfold Table4, TablePoint, table_point_addr, felem_addr in Hsep.
         rewrite !word_add_of_Z_assoc in Hsep.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with 0 in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with felem_size_in_bytes in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (2 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (3 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (4 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (5 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (6 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (7 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (8 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (9 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (10 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (11 * felem_size_in_bytes) in Hsep by lia.
         destruct Hidx as [Hi|[Hi|[Hi|Hi]]]; rewrite Hi in Hv2_eq;
           (* Normalize (0|1|2|3) * (3 * felem_size_in_bytes) to concrete form *)
           first
             [ replace (0 * (3 * felem_size_in_bytes))
                  with 0 in Hv2_eq by lia
             | replace (1 * (3 * felem_size_in_bytes))
                  with (3 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (2 * (3 * felem_size_in_bytes))
                  with (6 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (3 * (3 * felem_size_in_bytes))
                  with (9 * felem_size_in_bytes) in Hv2_eq by lia ];
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy.
         (* 4 idx subgoals remaining *)
         { (* idx = 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X0, F.opp Y0, Z0))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X0, (F.opp Y0), Z0.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
         { (* idx = 1 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X1, F.opp Y1, Z1))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X1, (F.opp Y1), Z1.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
         { (* idx = 2 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X2, F.opp Y2, Z2))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X2, (F.opp Y2), Z2.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
         { (* idx = 3 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros _.
             wp_direct_call HOppInplace.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X3, F.opp Y3, Z3))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X3, (F.opp Y3), Z3.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = true) as -> by (apply Z.ltb_lt; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. }
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.unsigned_of_Z_1 in Hcontra. congruence.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia. } }
      -- (* d >= 0 branch *)
         intro Hge.
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         letexists; split; [solve [eval_dexprs_here] |].
         cbv beta zeta match delta [dlet.dlet].
         destruct table_Phi_entries as [|e0 [|e1 [|e2 [|e3 [|??]]]]];
           try (simpl in Htable_Phi_len; discriminate).
         subst v. cbn [Semantics.interp_binop] in *.
         (* Derive d > 0 from Hge (d is not < 0) and Hd_ne (d ≠ 0). *)
         assert (Hdpos : 0 < d).
         { unfold encode_digit in Hge.
           destruct (word.lts (word.of_Z d) (word.of_Z 0)) eqn:E.
           { exfalso. rewrite word.unsigned_of_Z in Hge.
             unfold word.wrap in Hge.
             destruct width_cases as [Hw|Hw]; rewrite Hw in Hge;
               cbv in Hge; discriminate. }
           { rewrite word.signed_lts in E.
             rewrite word.signed_of_Z in E. rewrite word.signed_of_Z in E.
             unfold word.swrap in E.
             destruct width_cases as [Hw|Hw]; rewrite Hw in E; lia. } }
         clear Hge Hdne.
         (* v0 = encode_digit d = word.of_Z d = word.of_Z |d| since d > 0. *)
         assert (Hv0_eq : v0 = word.of_Z (Z.abs d)).
         { subst v0. unfold encode_digit. f_equal. lia. }
         assert (Hv2_eq : v2 = word.of_Z (((Z.abs d - 1) / 2)
                                          * (3 * felem_size_in_bytes))).
         { subst v2. subst v1. rewrite Hv0_eq. apply tab_off_compute. lia. }
         set (idx := (Z.abs d - 1) / 2) in Hv2_eq.
         assert (Hidx : idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3)
           by (subst idx; lia).
         destruct e0 as [[X0 Y0] Z0]. destruct e1 as [[X1 Y1] Z1].
         destruct e2 as [[X2 Y2] Z2]. destruct e3 as [[X3 Y3] Z3].
         unfold Table4, TablePoint, table_point_addr, felem_addr in Hsep.
         rewrite !word_add_of_Z_assoc in Hsep.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with 0 in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with felem_size_in_bytes in Hsep by lia.
         replace (Z.of_nat 0 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (2 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (3 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (4 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 1 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (5 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (6 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (7 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 2 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (8 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 0 * felem_size_in_bytes)
            with (9 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 1 * felem_size_in_bytes)
            with (10 * felem_size_in_bytes) in Hsep by lia.
         replace (Z.of_nat 3 * (3 * felem_size_in_bytes) +
                  Z.of_nat 2 * felem_size_in_bytes)
            with (11 * felem_size_in_bytes) in Hsep by lia.
         destruct Hidx as [Hi|[Hi|[Hi|Hi]]]; rewrite Hi in Hv2_eq;
           first
             [ replace (0 * (3 * felem_size_in_bytes))
                  with 0 in Hv2_eq by lia
             | replace (1 * (3 * felem_size_in_bytes))
                  with (3 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (2 * (3 * felem_size_in_bytes))
                  with (6 * felem_size_in_bytes) in Hv2_eq by lia
             | replace (3 * (3 * felem_size_in_bytes))
                  with (9 * felem_size_in_bytes) in Hv2_eq by lia ];
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy;
           wp_direct_call HFelemCopy.
         { (* idx = 0 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X0, Y0, Z0))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X0, Y0, Z0.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
         { (* idx = 1 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X1, Y1, Z1))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X1, Y1, Z1.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
         { (* idx = 2 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X2, Y2, Z2))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X2, Y2, Z2.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
         { (* idx = 3 *)
           letexists; split; [eval_dexprs_here|].
           split.
           { intros Hcontra. exfalso. subst v.
             cbn [Semantics.interp_binop] in Hcontra.
             unfold encode_digit in Hcontra.
             destruct (@word.lts _ word (word.of_Z d) (word.of_Z 0)) eqn:Elt.
             - rewrite word.signed_lts in Elt.
               rewrite word.signed_of_Z in Elt. rewrite word.signed_of_Z in Elt.
               unfold word.swrap in Elt.
               destruct width_cases as [Hw|Hw]; rewrite Hw in Elt; lia.
             - apply Hcontra. rewrite word.unsigned_of_Z_0. reflexivity. }
           { intros _.
             wp_direct_call HCurveAddInplace.
             destruct (curve_add (Ox, Oy, Oz) (X3, Y3, Z3))
               as [[Xo' Yo'] Zo'] eqn:Hca.
             cbn zeta in Hsep.
             exists Xo', Yo', Zo', X3, Y3, Z3.
             destruct (d =? 0) eqn:Edz; [apply Z.eqb_eq in Edz; lia|].
             simpl.
             split; [|split].
             - rewrite <- Hca. f_equal.
               unfold digit_point. rewrite Edz.
               unfold idx in Hi. rewrite Hi. simpl.
               assert ((d <? 0) = false) as -> by (apply Z.ltb_ge; lia).
               reflexivity.
             - unfold Table4, TablePoint, table_point_addr, felem_addr.
               rewrite !word_add_of_Z_assoc.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with 0 by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with felem_size_in_bytes by lia.
               replace (Z.of_nat 0 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (2 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (3 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (4 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 1 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (5 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (6 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (7 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 2 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (8 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 0 * felem_size_in_bytes) with (9 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 1 * felem_size_in_bytes) with (10 * felem_size_in_bytes) by lia.
               replace (Z.of_nat 3 * (3 * felem_size_in_bytes) + Z.of_nat 2 * felem_size_in_bytes) with (11 * felem_size_in_bytes) by lia.
               ecancel_assumption.
             - repeat split; try solve_mapget; try reflexivity.
               intros k v' Hk1 Hk2 Hk3 Hk4 Hgk.
               repeat (rewrite map.get_put_diff by auto).
               exact Hgk. } }
  Qed.

End LoadAndProcess.
