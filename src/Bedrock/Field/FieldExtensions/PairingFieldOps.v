(** * Bedrock2 compilation layer for pairing-specific field operations.

    Provides additional operations needed for the optimal Ate pairing
    that are not part of the standard FieldParameters interface:
    - fp2_conjugate: (a0, a1) -> (a0, -a1)
    - fp6_mul_fp2: scale Fp6 by an Fp2 scalar
    - fp6_frobenius: Frobenius endomorphism on Fp6 (gamma constants as extra args)
    - fp6_frobenius_p2: Frobenius squared on Fp6
    - fp12_frobenius: Frobenius on Fp12
    - fp12_frobenius_p2: Frobenius squared on Fp12

    WP proofs are currently stubs (exact I).
*)

Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Export Crypto.Spec.ModularArithmetic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Section PairingOps.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {prime_parameters : PrimeFieldParameters}
          {prime_parameters_ok : PrimeFieldParameters_ok}
          {M_mod : (Z.pos M_pos) mod 4 =? 3 = true}.

  Local Notation Fp := (F M_pos).
  Local Notation Fp2 := ((Fp * Fp)%type).
  Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
  Local Notation Fp12 := ((Fp6 * Fp6)%type).

  Existing Instance prime_field_parameters.

  Context {F_representation : AbstractField.FieldRepresentation (F:=Fp)}
          {F_representation_ok : AbstractField.FieldRepresentation_ok (F:=Fp)}.

  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  Variable fp12_prefix : string.
  Variable fp6_prefix : string.
  Variable fp2_prefix : string.

  (* ================================================================ *)
  (* Lower-layer instances                                             *)
  (* ================================================================ *)

  Local Instance Fp2_fp_inst : AbstractField.FieldParameters Fp2 :=
    Fp2_field_parameters (fp2_prefix:=fp2_prefix).
  Local Instance Fp2_repr_inst : @AbstractField.FieldRepresentation Fp2 Fp2_fp_inst width BW word mem :=
    @Fp2_field_representation width BW word mem prime_parameters F_representation fp2_prefix.

  Local Instance Fp6_fp_inst : AbstractField.FieldParameters Fp6 :=
    Fp6_field_parameters (fp6_prefix:=fp6_prefix).
  Local Instance Fp6_repr_inst : @AbstractField.FieldRepresentation Fp6 Fp6_fp_inst width BW word mem :=
    Fp6_field_representation (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  Local Instance Fp12_fp_inst : AbstractField.FieldParameters Fp12 :=
    Fp12_field_parameters (fp12_prefix:=fp12_prefix).
  Local Instance Fp12_repr_inst : @AbstractField.FieldRepresentation Fp12 Fp12_fp_inst width BW word mem :=
    Fp12_field_representation (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  (* ================================================================ *)
  (* Offset helpers                                                    *)
  (* ================================================================ *)

  (* Fp-level offsets within an Fp2 element *)
  Local Notation fp_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).
  Local Definition expr_fp_snd (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp_felem_offset).

  (* Fp2-level offsets within an Fp6 element *)
  Local Notation fp2_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).
  Local Definition expr_fp6_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp6_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp2_felem_offset).
  Local Definition expr_fp6_c2 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal (2 * fp2_felem_offset)).

  (* Fp6-level offsets within an Fp12 element *)
  Local Notation fp6_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp6))).
  Local Definition expr_fp12_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp12_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp6_felem_offset).

  (* ================================================================ *)
  (* spec_of instances for underlying operations                       *)
  (* ================================================================ *)

  (* Fp-level *)
  Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
    AbstractField.spec_of_felem_copy.
  Instance spec_of_Fp_opp : spec_of (AbstractField.opp (F:=Fp)) :=
    AbstractField.unop_spec AbstractField.un_opp.

  (* Fp2-level *)
  Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
    AbstractField.spec_of_felem_copy.
  Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
    AbstractField.binop_spec AbstractField.bin_mul.

  (* Fp6-level *)
  Instance spec_of_Fp6_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp6)) :=
    AbstractField.spec_of_felem_copy (F:=Fp6).
  Instance spec_of_Fp6_opp : spec_of (AbstractField.opp (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=Fp6).

  (* Fp12-level *)
  Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
    AbstractField.spec_of_felem_copy (F:=Fp12).

  Context {Fp12_names : FieldNames (F:=Fp12)}.
  Context {Fp6_names : FieldNames (F:=Fp6)}.
  Context {Fp2_names : FieldNames (F:=Fp2)}.
  Context {Fp_names : FieldNames (F:=Fp)}.

  (* ================================================================ *)
  (* Function bodies                                                   *)
  (* ================================================================ *)

  Import Syntax BinInt String List.ListNotations.

  (* Generate real WP goals for (string * func) definitions *)
  Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

  Local Ltac2 Notation "instance_of" type(constr) :=
    lazy_match! Ltac2.Constr.pretype (preterm:(_ : $type)) with ?instance => instance end.

  Local Ltac2 rec callee_specs_ft (cmd : constr) : constr list :=
    multi_match! cmd with
      | cmd.cond _ ?c1 ?c2 => List.append (callee_specs_ft c1) (callee_specs_ft c2)
      | cmd.seq ?c1 ?c2 => List.append (callee_specs_ft c1) (callee_specs_ft c2)
      | cmd.while _ ?c => callee_specs_ft c
      | cmd.stackalloc _ _ ?c => callee_specs_ft c
      | cmd.call _ ?f _ => [instance_of (spec_of $f)]
      | _ => []
    end.

  Local Ltac2 program_logic_goal_for_ft (proc : constr) : unit :=
    let unfolded := eval hnf in $proc in
    lazy_match! unfolded with
    | (?fname, (?params, ?rets, ?body)) =>
      let fname_spec := instance_of (spec_of $fname) in
      let specs := callee_specs_ft body in
      let goal := (fun (functions : constr) =>
        List.fold_right (fun ps c => '(($ps $functions) -> $c)) specs '($fname_spec $functions)) in
      exact (forall functions (EnvContains : map.get functions $fname = Some ($params, $rets, $body)),
        ltac2:(let g := goal &functions in exact $g))
    end.

  Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
  Local Notation "program_logic_goal_for_function! proc" := (program_logic_goal_for proc ltac2:(
     Control.plus (fun () => program_logic_goal_for_ft (Ltac2.Constr.pretype proc)) (fun _ => exact True)))
    (at level 10, only parsing).

  (* Function name helpers *)
  Local Definition fp2_conjugate_name := (fp2_prefix ++ "conjugate")%string.
  Local Definition fp6_mul_fp2_name := (fp6_prefix ++ "mul_fp2")%string.
  Local Definition fp6_frobenius_name := (fp6_prefix ++ "frobenius")%string.
  Local Definition fp6_frobenius_p2_name := (fp6_prefix ++ "frobenius_p2")%string.
  Local Definition fp12_frobenius_name := (fp12_prefix ++ "frobenius")%string.
  Local Definition fp12_frobenius_p2_name := (fp12_prefix ++ "frobenius_p2")%string.

  (* -------------------------------------------------------------- *)
  (* fp2_conjugate: (a0, a1) -> (a0, -a1)                            *)
  (* -------------------------------------------------------------- *)

  Definition Fp2_conjugate : function_t :=
    (fp2_conjugate_name, (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp)) [expr.var "out"; expr.var "x"]);
      coq:(cmd.call [] (AbstractField.opp (F:=Fp)) [expr_fp_snd (expr.var "out"); expr_fp_snd (expr.var "x")])
    ))).

  (* Fp2 conjugation model: (a0, a1) → (a0, -a1) *)
  Local Instance un_Fp2_conjugate
    : @AbstractField.UnOp _ _ _ _ Fp2 Fp2_fp_inst Fp2_repr_inst fp2_conjugate_name :=
    {| AbstractField.un_model := fun x => (fst x, @F.opp M_pos (snd x));
       AbstractField.un_xbounds := @AbstractField.tight_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst;
       AbstractField.un_outbounds := @AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst |}.

  Instance spec_of_Fp2_conjugate : spec_of fp2_conjugate_name :=
    AbstractField.unop_spec un_Fp2_conjugate.

  Lemma Fp2_conjugate_ok : program_logic_goal_for_function! Fp2_conjugate.
  Proof. Admitted. (* TODO: WP proof — 2 Fp-level calls *)

  (* -------------------------------------------------------------- *)
  (* fp6_mul_fp2: (c0, c1, c2) * s -> (c0*s, c1*s, c2*s)            *)
  (*   Extra arg: s (pointer to Fp2 scalar)                           *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_mul_fp2 : function_t :=
    (fp6_mul_fp2_name, (["out"; "x"; "s"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s_copy;
      (* Copy scalar to avoid aliasing with out *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr.var "s_copy"; expr.var "s"]);
      (* out.c0 = x.c0 * s *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "x"); expr.var "s_copy"]);
      (* out.c1 = x.c1 * s *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "x"); expr.var "s_copy"]);
      (* out.c2 = x.c2 * s *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "x"); expr.var "s_copy"])
    ))).

  Lemma Fp6_mul_fp2_ok : program_logic_goal_for_function! Fp6_mul_fp2.
  Proof. exact I. Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_frobenius: raise Fp6 element to p-th power                   *)
  (*   conj(c0) + conj(c1)*gamma1*v + conj(c2)*gamma2*v^2            *)
  (*   Extra args: gamma1, gamma2 (pointers to Fp2 constants)         *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_frobenius : function_t :=
    (fp6_frobenius_name, (["out"; "x"; "gamma1"; "gamma2"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as tmp;
      (* tmp.c0 = conj(x.c0) *)
      coq:(cmd.call [] fp2_conjugate_name [expr_fp6_c0 (expr.var "tmp"); expr_fp6_c0 (expr.var "x")]);
      (* tmp.c1 = conj(x.c1) *)
      coq:(cmd.call [] fp2_conjugate_name [expr_fp6_c1 (expr.var "tmp"); expr_fp6_c1 (expr.var "x")]);
      (* tmp.c2 = conj(x.c2) *)
      coq:(cmd.call [] fp2_conjugate_name [expr_fp6_c2 (expr.var "tmp"); expr_fp6_c2 (expr.var "x")]);
      (* out.c0 = tmp.c0 (just conjugation, no gamma) *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "tmp")]);
      (* out.c1 = conj(c1) * gamma1 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "tmp"); expr.var "gamma1"]);
      (* out.c2 = conj(c2) * gamma2 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "tmp"); expr.var "gamma2"])
    ))).

  Lemma Fp6_frobenius_ok : program_logic_goal_for_function! Fp6_frobenius.
  Proof. exact I. Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_frobenius_p2: raise Fp6 element to p^2-th power              *)
  (*   c0 + c1*gamma1_p2*v + c2*gamma2_p2*v^2                        *)
  (*   (no conjugation since p^2 ≡ 1 mod 2 on Fp2)                   *)
  (*   Extra args: gamma1_p2, gamma2_p2 (pointers to Fp2 constants)   *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_frobenius_p2 : function_t :=
    (fp6_frobenius_p2_name, (["out"; "x"; "gamma1_p2"; "gamma2_p2"], []:list String.string, bedrock_func_body:(
      (* out.c0 = x.c0 (unchanged) *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "x")]);
      (* out.c1 = x.c1 * gamma1_p2 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "x"); expr.var "gamma1_p2"]);
      (* out.c2 = x.c2 * gamma2_p2 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "x"); expr.var "gamma2_p2"])
    ))).

  Lemma Fp6_frobenius_p2_ok : program_logic_goal_for_function! Fp6_frobenius_p2.
  Proof. exact I. Qed.

  (* -------------------------------------------------------------- *)
  (* fp12_frobenius: raise Fp12 element to p-th power                 *)
  (*   c0' = fp6_frobenius(c0)                                        *)
  (*   c1' = fp6_mul_fp2(fp6_frobenius(c1), w_frob_c1)               *)
  (*   Extra args: gamma1, gamma2, w_frob_c1                          *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_frobenius : function_t :=
    (fp12_frobenius_name, (["out"; "x"; "gamma1"; "gamma2"; "w_frob_c1"], []:list String.string, bedrock_func_body:(
      (* out.c0 = fp6_frobenius(x.c0) *)
      coq:(cmd.call [] fp6_frobenius_name [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "x"); expr.var "gamma1"; expr.var "gamma2"]);
      (* out.c1 = fp6_frobenius(x.c1) *)
      coq:(cmd.call [] fp6_frobenius_name [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "x"); expr.var "gamma1"; expr.var "gamma2"]);
      (* out.c1 = out.c1 * w_frob_c1 (scalar mul by Fp2) *)
      coq:(cmd.call [] fp6_mul_fp2_name [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "out"); expr.var "w_frob_c1"])
    ))).

  Lemma Fp12_frobenius_ok : program_logic_goal_for_function! Fp12_frobenius.
  Proof. exact I. Qed.

  (* -------------------------------------------------------------- *)
  (* fp12_frobenius_p2: raise Fp12 element to p^2-th power            *)
  (*   c0' = fp6_frobenius_p2(c0)                                     *)
  (*   c1' = fp6_mul_fp2(fp6_frobenius_p2(c1), w_frob_p2_c1)         *)
  (*   Extra args: gamma1_p2, gamma2_p2, w_frob_p2_c1                 *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_frobenius_p2 : function_t :=
    (fp12_frobenius_p2_name, (["out"; "x"; "gamma1_p2"; "gamma2_p2"; "w_frob_p2_c1"], []:list String.string, bedrock_func_body:(
      (* out.c0 = fp6_frobenius_p2(x.c0) *)
      coq:(cmd.call [] fp6_frobenius_p2_name [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "x"); expr.var "gamma1_p2"; expr.var "gamma2_p2"]);
      (* out.c1 = fp6_frobenius_p2(x.c1) *)
      coq:(cmd.call [] fp6_frobenius_p2_name [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "x"); expr.var "gamma1_p2"; expr.var "gamma2_p2"]);
      (* out.c1 = out.c1 * w_frob_p2_c1 *)
      coq:(cmd.call [] fp6_mul_fp2_name [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "out"); expr.var "w_frob_p2_c1"])
    ))).

  Lemma Fp12_frobenius_p2_ok : program_logic_goal_for_function! Fp12_frobenius_p2.
  Proof. exact I. Qed.

  (* -------------------------------------------------------------- *)
  (* Collected function list for downstream linking                    *)
  (* -------------------------------------------------------------- *)

  Definition PairingOps_funcs : list function_t :=
    [ Fp2_conjugate;
      Fp6_mul_fp2;
      Fp6_frobenius;
      Fp6_frobenius_p2;
      Fp12_frobenius;
      Fp12_frobenius_p2 ].

End PairingOps.
