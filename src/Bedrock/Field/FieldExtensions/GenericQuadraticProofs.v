(** * WP correctness proofs for generic quadratic extension functions.
    Uses WPTactics.v automation + GenericSplitJoin.v split/join. *)

Require Import Crypto.Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.FieldExtensions.SepFromPutmany.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.

Import Separation SeparationLogic.

Section GenericQuadProofs.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {BaseField : Type}.
  Context {base_fp : FieldParameters BaseField}.
  Context {base_repr : @FieldRepresentation BaseField base_fp width BW word mem}.
  Context {base_repr_ok : @FieldRepresentation_ok BaseField base_fp width BW word mem base_repr}.

  Variable nonresidue : BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Instance QE_fp : FieldParameters (BaseField * BaseField) :=
    QE_field_parameters nonresidue prefix eq_dec_base.
  Local Instance QE_repr : @FieldRepresentation _ QE_fp width BW word mem :=
    QE_field_representation nonresidue prefix eq_dec_base.

  Local Notation QE := (BaseField * BaseField)%type.
  Local Notation base_size := (@felem_size_in_words _ base_fp _ _ _ _ base_repr).

  Context {QE_names : FieldNames (F := QE)}.
  Context {base_names : FieldNames (F := BaseField)}.

  Variable mul_by_nr_name : string.
  Variable Mul_by_nr_func : string * (list String.string * list String.string * Syntax.cmd.cmd).
  Hypothesis Mul_by_nr_name_eq : fst Mul_by_nr_func = mul_by_nr_name.

  (* ================================================================ *)
  (* QE_opp_ok: simplest unop — two base opp calls, no stackalloc     *)
  (* ================================================================ *)

  Lemma QE_opp_ok :
    forall functions,
    map.get functions (opp (F := QE)) =
      Some (snd (QE_opp nonresidue prefix eq_dec_base)) ->
    (* Base opp specs *)
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (exists Ra, (@FElem _ base_fp _ _ _ _ base_repr px x * Ra)%sep m) ->
       (@FElem _ base_fp _ _ _ _ base_repr pout out * Rr)%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (@FElem _ base_fp _ _ _ _ base_repr pout out' * Rr)%sep m')) ->
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (exists Ra, (@FElem _ base_fp _ _ _ _ base_repr px x * Ra)%sep m) ->
       (@FElem _ base_fp _ _ _ _ base_repr pout out * Rr)%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (@FElem _ base_fp _ _ _ _ base_repr pout out' * Rr)%sep m')) ->
    (* QE opp spec *)
    forall pout px (out x : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@tight_bounds _ QE_fp _ _ _ _ QE_repr) x ->
    (exists Ra, (@FElem _ QE_fp _ _ _ _ QE_repr px x * Ra)%sep mem0) ->
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (opp (F := QE)) tr mem0 [pout; px]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' = @Fopp _ QE_fp (@feval _ QE_fp _ _ _ _ QE_repr x) /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFopp1 HFopp2
           pout px out x Rr tr mem0 Hbx [Rx HmemRx] Hmemout.
    (* Enter function *)
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func
      QE_opp GenericQuadratic.QE_opp].
    eexists. split. { exact eq_refl. }
    repeat straightline.
  Admitted.

End GenericQuadProofs.
