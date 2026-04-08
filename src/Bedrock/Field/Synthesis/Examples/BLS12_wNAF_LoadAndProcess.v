(** * Per-digit "load digit + process_one_digit" WP proof (task D).

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

    (* ============================================================ *)
    (* Proof outline (to be filled interactively with MCP):         *)
    (*                                                              *)
    (* Step 1: cmd.set "d1" := load(digits_k1 + iter * word_size)  *)
    (*   Unfold cmd.seq, evaluate expr (load from digit array).     *)
    (*   Uses Hdigit_load1 to resolve the memory load.              *)
    (*   After: l1 = map.put l0 "d1" (encode_digit d)              *)
    (*                                                              *)
    (* Step 2: cmd.cond on d1 (branch on d = 0 vs d != 0)          *)
    (*                                                              *)
    (* Case d = 0: ELSE branch (cmd.skip)                           *)
    (*   Output unchanged. Instantiate existentials with Ox/Oy/Oz.  *)
    (*   Show all map.get preserved via map.get_put_diff.           *)
    (*                                                              *)
    (* Case d != 0: THEN branch (table lookup + cond negate + add) *)
    (*   Phase A: abs value + table offset (3x cmd.set)             *)
    (*   Phase B: 3x felem_copy (table -> aux) using HFelemCopy    *)
    (*   Phase C: cond negate auxy if d < 0 using HOppInplace      *)
    (*   Phase D: curve_add(out, aux, out) using HCurveAddInplace  *)
    (*   Phase E: close postcondition with ecancel_assumption       *)
    (* ============================================================ *)
  Admitted.

End LoadAndProcess.
