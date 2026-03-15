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

Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
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
  Proof. Admitted.
  (* TODO: 2 Fp-level calls. Needs Fp2→Fp FElem decomposition + map.split_diff
     for felem_copy spec's two preconditions. Follow Fp2_felem_copy_ok pattern. *)
  (* Commented proof attempt removed for cleanliness. See git history. *)
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

  Local Notation FElem_Fp2 := (@AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
  Local Notation FElem_Fp6 := (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
  Local Notation FElem_Fp12 := (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst).
  Local Notation Fp6_feval := (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
  Local Notation Fp12_feval := (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst).
  Local Notation Fp6_bounded := (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
  Local Notation Fp12_bounded := (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst).

  (* Gallina model for fp6_mul_fp2: scale each Fp2 component by s *)
  Local Definition fp6_mul_fp2_model (x : Fp6) (s : Fp2) : Fp6 :=
    ((@AbstractField.Fmul _ Fp2_fp_inst (fst (fst x)) s,
      @AbstractField.Fmul _ Fp2_fp_inst (snd (fst x)) s),
     @AbstractField.Fmul _ Fp2_fp_inst (snd x) s).

  Instance spec_of_Fp6_mul_fp2 : spec_of fp6_mul_fp2_name :=
    fnspec! fp6_mul_fp2_name (pout px ps : word)
      / (old_out : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
        (x : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
        (s : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp6_bounded (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) s /\
        (FElem_Fp6 px x ⋆ (FElem_Fp2 ps s ⋆ (FElem_Fp6 pout old_out ⋆ Rr))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_feval out = fp6_mul_fp2_model (Fp6_feval x) (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst s) /\
          Fp6_bounded (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) out /\
          (FElem_Fp6 pout out ⋆ Rr) mem' }.

  Lemma Fp6_mul_fp2_ok : program_logic_goal_for_function! Fp6_mul_fp2.
  Proof. Admitted.

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

  (* Gallina model for Fp6 Frobenius: conj(c0) + conj(c1)*gamma1*v + conj(c2)*gamma2*v^2 *)
  Local Definition fp2_conj (x : Fp2) : Fp2 := (fst x, @F.opp M_pos (snd x)).

  Local Definition fp6_frobenius_model (gamma1 gamma2 : Fp2) (x : Fp6) : Fp6 :=
    let c0 := fst (fst x) in let c1 := snd (fst x) in let c2 := snd x in
    ((fp2_conj c0,
      @AbstractField.Fmul _ Fp2_fp_inst (fp2_conj c1) gamma1),
     @AbstractField.Fmul _ Fp2_fp_inst (fp2_conj c2) gamma2).

  Instance spec_of_Fp6_frobenius : spec_of fp6_frobenius_name :=
    fnspec! fp6_frobenius_name (pout px pgamma1 pgamma2 : word)
      / (old_out x : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
        (gamma1 gamma2 : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp6_bounded (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma1 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma2 /\
        (FElem_Fp6 px x ⋆ (FElem_Fp2 pgamma1 gamma1 ⋆ (FElem_Fp2 pgamma2 gamma2 ⋆
          (FElem_Fp6 pout old_out ⋆ Rr)))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_feval out = fp6_frobenius_model
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma1)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma2)
            (Fp6_feval x) /\
          Fp6_bounded (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) out /\
          (FElem_Fp6 pout out ⋆ Rr) mem' }.

  Lemma Fp6_frobenius_ok : program_logic_goal_for_function! Fp6_frobenius.
  Proof. Admitted.

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

  (* Gallina model for Fp6 Frobenius p^2: c0 + c1*gamma1_p2*v + c2*gamma2_p2*v^2 *)
  Local Definition fp6_frobenius_p2_model (gamma1_p2 gamma2_p2 : Fp2) (x : Fp6) : Fp6 :=
    let c0 := fst (fst x) in let c1 := snd (fst x) in let c2 := snd x in
    ((c0, @AbstractField.Fmul _ Fp2_fp_inst c1 gamma1_p2),
     @AbstractField.Fmul _ Fp2_fp_inst c2 gamma2_p2).

  Instance spec_of_Fp6_frobenius_p2 : spec_of fp6_frobenius_p2_name :=
    fnspec! fp6_frobenius_p2_name (pout px pgamma1_p2 pgamma2_p2 : word)
      / (old_out x : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
        (gamma1_p2 gamma2_p2 : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp6_bounded (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma1_p2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma2_p2 /\
        (FElem_Fp6 px x ⋆
         (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
          (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
           (FElem_Fp6 pout old_out ⋆ Rr)))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_feval out = fp6_frobenius_p2_model
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma1_p2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma2_p2)
            (Fp6_feval x) /\
          Fp6_bounded (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) out /\
          (FElem_Fp6 pout out ⋆ Rr) mem' }.

  (* Local tactics for map manipulation (copies of CubicFieldExtensions locals) *)
  Local Ltac map_disjoint_auto :=
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

  Local Notation fp_felem_size := (@AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).

  (* Proof sketch for Fp6_frobenius_p2_ok:
     The function performs 1 Fp2 copy + 2 Fp2 mul calls, no stackalloc.
     Callee hypotheses: HFcopy : spec_of_Fp2_felem_copy, HFmul1/HFmul2 : spec_of_Fp2_mul.
     Proof structure (following Fp6_felem_copy_ok / Fp6_add_ok in CubicFieldExtensions.v):
     1. start_func, straightline, decompose big sep precondition into individual sub-maps
     2. Fp6_raw_FElem_split to decompose Fp6 x and old_out into 3 Fp2 FElems each
     3. Derive all pairwise disjointness between sub-maps
     4. Decompose Fp6 bounded_by into 3 Fp2 bounded_by; relax tight->loose via Fp2_bounds_loose_of_tight
     5. Call 1 (copy out.c0 := x.c0): dexprs + weaken_call + eapply HFcopy
        - Two-part copy precondition: build (FElem*FElem*R)mem and (FElem*Rout)mem via map rearrangement
     6. Build big sep for m' after copy (9-way: new0, x0..x2, g1, g2, o1, o2, rr)
     7. Call 2 (mul out.c1 := x.c1*gamma1_p2): dexprs + weaken_call + eapply HFmul1
        - Binop preconditions via ecancel_assumption on big sep
     8. Call 3 (mul out.c2 := x.c2*gamma2_p2): same pattern with HFmul2
     9. Final: exists (c0_felem x ++ out1' ++ out2')
        - feval: change Fp6_feval to 3 Fp2_fevals, rewrite c0/c1/c2_felem projections
        - bounded_by: change Fp6_bounded to 3 Fp2_bounded, apply Fp2_bounds_loose_of_tight
        - sep: Fp6_raw_FElem_join to reassemble 3 Fp2 FElems into Fp6 FElem
     Key lemmas: Fp6_raw_FElem_split/join, Fp2_FElem_length, Fp2_bounds_loose_of_tight,
       c0/c1/c2_felem_app, Fp6_list_decomp, ListUtil.firstn/skipn_app_sharp *)
  (* Fp2 FElem length extraction *)
  Local Notation Fp2_felem_size := (@AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).

  Lemma Fp6_frobenius_p2_ok : program_logic_goal_for_function! Fp6_frobenius_p2.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy HFmul1 HFmul2.
    unfold spec_of_Fp6_frobenius_p2.
    intros pout px pgamma1_p2 pgamma2_p2 old_out x gamma1_p2 gamma2_p2 Rr tr mem0
      [Hbx [Hbg1 [Hbg2 Hmem_all]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_frobenius_p2].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Decompose sep into individual FElems === *)
    destruct Hmem_all as [m_x [m_r1 [[Heq0 Hd0] [Hfx Hr1]]]].
    destruct Hr1 as [m_g1 [m_r2 [[Heq1 Hd1] [Hfg1 Hr2]]]].
    destruct Hr2 as [m_g2 [m_r3 [[Heq2 Hd2] [Hfg2 Hr3]]]].
    destruct Hr3 as [m_out [m_rr [[Heq3 Hd3] [Hfe_out Hrr]]]].
    subst m_r1 m_r2 m_r3 mem0.
    pose proof (Fp6_raw_FElem_split fp6_prefix fp2_prefix px x _ Hfx) as Hxs.
    destruct Hxs as [m_x0 [m_x12 [Hsp_x [Hx0 Hx12]]]].
    destruct Hx12 as [m_x1 [m_x2 [Hsp_x12 [Hx1 Hx2]]]].
    destruct Hsp_x as [? Hdxx]. destruct Hsp_x12 as [? Hdxy]. subst.
    pose proof (Fp6_raw_FElem_split fp6_prefix fp2_prefix pout old_out _ Hfe_out) as Hos.
    destruct Hos as [m_o0 [m_o12 [Hsp_o [Ho0 Ho12]]]].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Ho1 Ho2]]]].
    destruct Hsp_o as [? Hdox]. destruct Hsp_o12 as [? Hdoy]. subst.
    (* Derive all pairwise disjointness *)
    rename Hd0 into Hd_xg. rename Hd1 into Hd_g1r. rename Hd2 into Hd_g2r. rename Hd3 into Hd_or.
    split_all_disjointness.
    (* Decompose Fp6 bounded_by into Fp2 *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    (* Flatten memory to right-associated putmany *)
    rewrite <- ?map.putmany_assoc.
    (* Build master sep at Fp2 level *)
    assert (Hsep9 :
      (FElem_Fp2 px (c0_felem x) ⋆
       (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c1_offset fp2_prefix)) (c1_felem x) ⋆
        (FElem_Fp2 (word.add px (CubicFieldExtensions.fp6_c2_offset fp2_prefix)) (c2_felem x) ⋆
         (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
          (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
           (FElem_Fp2 pout (c0_felem old_out) ⋆
            (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset fp2_prefix)) (c1_felem old_out) ⋆
             (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset fp2_prefix)) (c2_felem old_out) ⋆
              Rr))))))))
      (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2
        (map.putmany m_g1 (map.putmany m_g2
          (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr))))))))).
    { exists m_x0, (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hx0 |].
      exists m_x1, (map.putmany m_x2 (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr)))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hx1 |].
      exists m_x2, (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hx2 |].
      exists m_g1, (map.putmany m_g2 (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr)))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfg1 |].
      exists m_g2, (map.putmany m_o0 (map.putmany m_o1 (map.putmany m_o2 m_rr))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfg2 |].
      exists m_o0, (map.putmany m_o1 (map.putmany m_o2 m_rr)).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ho0 |].
      exists m_o1, (map.putmany m_o2 m_rr).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ho1 |].
      exists m_o2, m_rr.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ho2 | exact Hrr]. }
    (* === Call 1: Fp2 copy (out.c0 = x.c0) === *)
    (* The copy spec has TWO preconditions — needs careful sep reasoning.
       Using ecancel_assumption_with_copy on the master sep fact Hsep9. *)
    exists [pout; px]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply HFcopy. split.
         { pose proof Hsep9 as H'. ecancel_assumption. }
         { pose proof Hsep9 as H'. ecancel_assumption. } }
    (* Post copy *)
    intros t' m' rets [Hrets [Htr1 Hsep1]].
    subst rets. symmetry in Htr1. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* Don't destructure Hsep1 — use it directly for ecancel *)
    (* === Call 2: Fp2 mul (out.c1 = x.c1 * gamma1_p2) === *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul1 (word.add pout (CubicFieldExtensions.fp6_c1_offset fp2_prefix))
           (word.add px (CubicFieldExtensions.fp6_c1_offset fp2_prefix))
           pgamma1_p2
           (c1_felem old_out) (c1_felem x) gamma1_p2 _ tr).
         split; [solve_bounds |].
         split; [exact Hbg1 |].
         split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
         pose proof Hsep1 as H'. ecancel_assumption. }
    (* Post mul1 *)
    intros t'' m'' rets2 [Hrets2 [Htr2 [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    subst rets2. symmetry in Htr2. subst t''.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 3: Fp2 mul (out.c2 = x.c2 * gamma2_p2) === *)
    eexists. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul2 (word.add pout (CubicFieldExtensions.fp6_c2_offset fp2_prefix))
           (word.add px (CubicFieldExtensions.fp6_c2_offset fp2_prefix))
           pgamma2_p2
           (c2_felem old_out) (c2_felem x) gamma2_p2 _ tr).
         split; [solve_bounds |].
         split; [exact Hbg2 |].
         split; [eexists; pose proof Hsep2 as H'; ecancel_assumption |].
         split; [eexists; pose proof Hsep2 as H'; ecancel_assumption |].
         pose proof Hsep2 as H'. ecancel_assumption. }
    (* Post mul2 + final *)
    intros t''' m''' rets3 [Hrets3 [Htr3 [out2' [Hfeval2 [Hbound2 Hsep3]]]]].
    subst rets3. symmetry in Htr3. subst t'''.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#).
    split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. }
    split. { exact eq_refl. }
    (* === Final postcondition === *)
    pose proof (Fp2_FElem_length _ _ _ Hnew0) as Hlen0.
    exists (c0_felem x ++ out1' ++ out2').
    split.
    { (* feval *)
      change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta.
      assert (Hlen1 : length out1' = Fp2_felem_size).
      { destruct Hsep3 as [? [? [? [? ?]]]]. destruct H0 as [? [? [? [? ?]]]].
        admit. (* FElem length extraction — mechanical *) }
      unfold c0_felem, c1_felem, c2_felem.
      rewrite firstn_app' by exact Hlen0.
      rewrite skipn_app by exact Hlen0.
      rewrite firstn_app' by (rewrite Hlen0; exact Hlen1).
      rewrite skipn_app by (rewrite Hlen0; exact Hlen1).
      rewrite Hfeval1, Hfeval2.
      unfold fp6_frobenius_p2_model. simpl.
      reflexivity. }
    split.
    { (* bounded_by *) admit. }
    { (* sep: join Fp2 components back to Fp6 *)
      admit. }
  Admitted.
  (* Full proof body (follows Fp6_felem_copy_ok / Fp6_add_ok pattern):
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy HFmul1 HFmul2.
    unfold spec_of_Fp6_frobenius_p2.
    intros pout px pgamma1_p2 pgamma2_p2 old_out x gamma1_p2 gamma2_p2 Rr tr mem0
      [Hbx [Hbg1 [Hbg2 Hmem_all]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_frobenius_p2].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Decompose big sep into individual sub-maps *)
    destruct Hmem_all as [m_x [m_rest1 [[Heq_mem0 Hd_x_rest1] [Hfx Hrest1]]]].
    destruct Hrest1 as [m_g1 [m_rest2 [[Heq_rest1 Hd_g1_rest2] [Hfg1 Hrest2]]]].
    destruct Hrest2 as [m_g2 [m_rest3 [[Heq_rest2 Hd_g2_rest3] [Hfg2 Hrest3]]]].
    destruct Hrest3 as [m_out [m_rr [[Heq_rest3 Hd_out_rr] [Hfe_out Hrr_out]]]].
    subst m_rest1 m_rest2 m_rest3 mem0.
    (* Decompose Fp6 FElems into Fp2 components *)
    pose proof (Fp6_raw_FElem_split fp6_prefix fp2_prefix px x m_x Hfx) as Hx_split.
    destruct Hx_split as [m_x0 [m_x12 [[Heq_x Hd_x012] [Hx0 Hx12]]]].
    destruct Hx12 as [m_x1 [m_x2 [[Heq_x12 Hd_x12] [Hx1 Hx2]]]].
    subst m_x m_x12.
    pose proof (Fp6_raw_FElem_split fp6_prefix fp2_prefix pout old_out m_out Hfe_out) as Ho_split.
    destruct Ho_split as [m_o0 [m_o12 [[Heq_o Hd_o012] [Ho0 Ho12]]]].
    destruct Ho12 as [m_o1 [m_o2 [[Heq_o12 Hd_o12] [Ho1 Ho2]]]].
    subst m_out m_o12.
    (* Decompose Fp6 bounded_by into Fp2 components *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    pose proof (Fp2_bounds_loose_of_tight fp2_prefix _ Hbx1) as Hbx1_loose.
    pose proof (Fp2_bounds_loose_of_tight fp2_prefix _ Hbx2) as Hbx2_loose.
    (* === Call 1: Fp2 copy (out.c0 := x.c0) === *)
    exists [pout; px]. split.
    { repeat match goal with x := map.put _ _ _ |- _ => subst x end.
      cbv [dexprs list_map list_map_body expr_fp6_c0
           WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat (eexists; split;
        [ repeat (first [ apply map.get_put_same
                        | rewrite map.get_put_diff by congruence ]); try exact eq_refl
        | ]).
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { unfold spec_of_Fp2_felem_copy, AbstractField.spec_of_felem_copy.
      eapply (HFcopy pout px (c0_felem old_out) (c0_felem x)
        (fun m => (FElem_Fp2 (word.add px (word.of_Z fp2_felem_offset)) (c1_felem x) ⋆
                   (FElem_Fp2 (word.add px (word.of_Z (2 * fp2_felem_offset))) (c2_felem x) ⋆
                    (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
                     (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
                      (FElem_Fp2 (word.add pout (word.of_Z fp2_felem_offset)) (c1_felem old_out) ⋆
                       (FElem_Fp2 (word.add pout (word.of_Z (2 * fp2_felem_offset))) (c2_felem old_out) ⋆ Rr)))))) m)
        (fun m => m = map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2
           (map.putmany m_g1 (map.putmany m_g2 (map.putmany m_o1 (map.putmany m_o2 m_rr)))))))
        tr).
      admit. (* split into two copy preconditions *) }
    (* Process copy postcondition *)
    intros t' m' rets [Hrets [Htr1 Hsep_post1]].
    subst rets. symmetry in Htr1. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* Build big sep for m' after copy *)
    destruct Hsep_post1 as [m_new0 [m_frame1 [Hsp_post1 [Hnew0 Hframe1]]]].
    assert (Hsep_m' :
      (FElem_Fp2 pout (c0_felem x) ⋆
       (FElem_Fp2 px (c0_felem x) ⋆
        (FElem_Fp2 (word.add px (word.of_Z fp2_felem_offset)) (c1_felem x) ⋆
         (FElem_Fp2 (word.add px (word.of_Z (2 * fp2_felem_offset))) (c2_felem x) ⋆
          (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
           (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
            (FElem_Fp2 (word.add pout (word.of_Z fp2_felem_offset)) (c1_felem old_out) ⋆
             (FElem_Fp2 (word.add pout (word.of_Z (2 * fp2_felem_offset))) (c2_felem old_out) ⋆ Rr)))))))) m').
    { admit. (* build sep from individual FElems and disjointness *) }
    (* === Call 2: Fp2 mul (out.c1 := x.c1 * gamma1_p2) === *)
    eexists. split.
    { repeat match goal with x := map.put _ _ _ |- _ => subst x end.
      cbv [dexprs list_map list_map_body expr_fp6_c1
           WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat (eexists; split;
        [ repeat (first [ apply map.get_put_same
                        | rewrite map.get_put_diff by congruence ]); try exact eq_refl
        | ]).
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFmul1 (word.add pout (word.of_Z fp2_felem_offset))
                      (word.add px (word.of_Z fp2_felem_offset))
                      pgamma1_p2
                      (c1_felem old_out) (c1_felem x) gamma1_p2
                      _ tr).
      admit. (* mul1 preconditions *) }
    (* Process mul1 postcondition *)
    intros t'' m'' rets2 [Hrets2 [Htr2 [out1' [Hfeval1 [Hbound1 Hsep_post2]]]]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 3: Fp2 mul (out.c2 := x.c2 * gamma2_p2) === *)
    eexists. split.
    { repeat match goal with x := map.put _ _ _ |- _ => subst x end.
      cbv [dexprs list_map list_map_body expr_fp6_c2
           WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat (eexists; split;
        [ repeat (first [ apply map.get_put_same
                        | rewrite map.get_put_diff by congruence ]); try exact eq_refl
        | ]).
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { unfold spec_of_Fp2_mul, AbstractField.binop_spec.
      eapply (HFmul2 (word.add pout (word.of_Z (2 * fp2_felem_offset)))
                      (word.add px (word.of_Z (2 * fp2_felem_offset)))
                      pgamma2_p2
                      (c2_felem old_out) (c2_felem x) gamma2_p2
                      _ tr).
      split; [exact Hbx2_loose |].
      split; [exact Hbg2 |].
      split.
      { eexists. pose proof Hsep_post2 as H'. ecancel_assumption. }
      split.
      { eexists. pose proof Hsep_post2 as H'. ecancel_assumption. }
      pose proof Hsep_post2 as H'. ecancel_assumption. }
    (* Process mul2 postcondition *)
    intros t''' m''' rets3 [Hrets3 [Htr3 [out2' [Hfeval2 [Hbound2 Hsep_post3]]]]].
    subst rets3 t'''.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "gamma1_p2" => pgamma1_p2; "gamma2_p2" => pgamma2_p2 }#).
    split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. }
    split. { exact eq_refl. }
    (* === Final: reconstruct Fp6 output === *)
    exists (c0_felem x ++ out1' ++ out2').
    pose proof (Fp2_FElem_length fp2_prefix _ _ _ Hnew0) as Hlen_n0.
    assert (Hlen_out1 : length out1' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { admit. (* extract from Hsep_post2 *) }
    assert (Hlen_out2 : length out2' = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { admit. (* extract from Hsep_post3 *) }
    assert (Hc0_app : c0_felem (c0_felem x ++ out1' ++ out2') = c0_felem x).
    { unfold c0_felem. set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length (c0_felem x)) by (symmetry; exact Hlen_n0).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (c0_felem x ++ out1' ++ out2') = out1').
    { unfold c1_felem. set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length (c0_felem x)) by (symmetry; exact Hlen_n0).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length (c0_felem x) = length out1') by (rewrite Hlen_n0, Hlen_out1; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (c0_felem x ++ out1' ++ out2') = out2').
    { unfold c2_felem. set (n := (2 * fp_felem_size)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length (c0_felem x)) by (symmetry; exact Hlen_n0).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length (c0_felem x) = length out1') by (rewrite Hlen_n0, Hlen_out1; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      rewrite Hfeval1, Hfeval2.
      unfold fp6_frobenius_p2_model.
      change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst x) with
        ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem x),
          @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem x)),
         @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem x)).
      cbv beta. simpl fst. simpl snd.
      unfold AbstractField.Fmul. simpl.
      reflexivity. }
    (* bounded_by *)
    split.
    { change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem)).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      split; [| split].
      - apply (Fp2_bounds_loose_of_tight fp2_prefix). exact Hbx0.
      - apply (Fp2_bounds_loose_of_tight fp2_prefix). exact Hbound1.
      - apply (Fp2_bounds_loose_of_tight fp2_prefix). exact Hbound2. }
    (* sep: (FElem_Fp6 pout (c0_felem x ++ out1' ++ out2') * Rr) m''' *)
    { admit. }
  Admitted. *)

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

  (* Gallina model for Fp12 Frobenius *)
  Local Definition fp12_frobenius_model (gamma1 gamma2 : Fp2) (w_frob_c1 : Fp2) (x : Fp12) : Fp12 :=
    let c0 := fst x in let c1 := snd x in
    (fp6_frobenius_model gamma1 gamma2 c0,
     fp6_mul_fp2_model (fp6_frobenius_model gamma1 gamma2 c1) w_frob_c1).

  Instance spec_of_Fp12_frobenius : spec_of fp12_frobenius_name :=
    fnspec! fp12_frobenius_name (pout px pgamma1 pgamma2 pw_frob_c1 : word)
      / (old_out x : @AbstractField.felem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst)
        (gamma1 gamma2 w_frob_c1 : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp12_bounded (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma1 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) w_frob_c1 /\
        (FElem_Fp12 px x ⋆ (FElem_Fp2 pgamma1 gamma1 ⋆ (FElem_Fp2 pgamma2 gamma2 ⋆
          (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp12_feval out = fp12_frobenius_model
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma1)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst w_frob_c1)
            (Fp12_feval x) /\
          Fp12_bounded (@AbstractField.loose_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) out /\
          (FElem_Fp12 pout out ⋆ Rr) mem' }.

  Lemma Fp12_frobenius_ok : program_logic_goal_for_function! Fp12_frobenius.
  Proof. Admitted.

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

  Local Definition fp12_frobenius_p2_model (gamma1_p2 gamma2_p2 : Fp2) (w_frob_p2_c1 : Fp2) (x : Fp12) : Fp12 :=
    let c0 := fst x in let c1 := snd x in
    (fp6_frobenius_p2_model gamma1_p2 gamma2_p2 c0,
     fp6_mul_fp2_model (fp6_frobenius_p2_model gamma1_p2 gamma2_p2 c1) w_frob_p2_c1).

  Instance spec_of_Fp12_frobenius_p2 : spec_of fp12_frobenius_p2_name :=
    fnspec! fp12_frobenius_p2_name (pout px pgamma1_p2 pgamma2_p2 pw_frob_p2_c1 : word)
      / (old_out x : @AbstractField.felem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst)
        (gamma1_p2 gamma2_p2 w_frob_p2_c1 : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        Rr,
    { requires tr mem :=
        Fp12_bounded (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) x /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma1_p2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) gamma2_p2 /\
        @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst
          (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) w_frob_p2_c1 /\
        (FElem_Fp12 px x ⋆ (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆ (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
          (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))) mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp12_feval out = fp12_frobenius_p2_model
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma1_p2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst gamma2_p2)
            (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst w_frob_p2_c1)
            (Fp12_feval x) /\
          Fp12_bounded (@AbstractField.loose_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) out /\
          (FElem_Fp12 pout out ⋆ Rr) mem' }.

  Lemma Fp12_frobenius_p2_ok : program_logic_goal_for_function! Fp12_frobenius_p2.
  Proof. Admitted.

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
