Require Import coqutil.Byte.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZUtil.ModInv.
Local Open Scope Z_scope.
Import bedrock2.Memory.

Section FieldSpecs.

  Class FieldParameters F :=
    {
      (* F : Type; *)
      Fzero : F;
      Fone : F;
      Feq : F -> F -> Prop;
      Fopp : F -> F;
      Finv : F -> F;
      Fadd : F -> F -> F;
      Fsub : F -> F -> F;
      Fmul : F -> F -> F;
      Fdiv : F -> F -> F; (*consider collecting these in a separate class.*)
      FofZ : Z -> F;
      Feq_dec : DecidableRel Feq;

      (* a24 : F; (* (a+2) / 4 or (a-2) / 4, depending on the implementation *) *)
      (* special wrapper for copy so that compilation lemmas can recognize it *)
      (* fe_copy := (@id (F)); *)
      }.

  (* move *)
  Class CurveParameters F :=
    {
      a24 : F
    }.

  Class FieldNames (F : Type) :=
    {
      (** function names **)
      zero : string;
      one : string;
      mul : string;
      add : string;
      sub : string;
      opp : string;
      square : string;
      inv : string;
      from_bytes : string;
      to_bytes : string;
      select_znz : string;
      (* felem_small_literal p x :=
          store p (expr.literal x);
          store (p+4) (expr.literal 0);
          ...

        felem_copy pX pY :=
          store pX (load pY);
          store (pX+4) (load (pY+4));
          ... *)
      felem_copy : string;
      from_word : string;
      (* from_lists name should depend on input *)
      (* from_list : string; *)
    }.

  Class CurveNames (F : Type) :=
    {
      scmula24 : string;
    }.

  Definition field_names_prefixed F
  (prefix: string) : FieldNames F :=
    Build_FieldNames F
    (prefix ++ "zero")
    (prefix ++ "one")
    (prefix ++ "mul")
    (prefix ++ "add")
    (prefix ++ "sub")
    (prefix ++ "opp")
    (prefix ++ "square")
    (prefix ++ "inv")
    (prefix ++ "from_bytes")
    (prefix ++ "to_bytes")
    (prefix ++ "select_znz")
    (prefix ++ "felem_copy")
    (prefix ++ "small_literal")
  .

  Definition curve_names_prefixed F
  (prefix: string) : CurveNames F :=
    Build_CurveNames F
    (prefix ++ "scmula24").

  Class FieldParameters_ok F {field_parameters : FieldParameters F} := {
    fld:@Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv
  }.

  Class FieldRepresentation
        (F : Type)
        {field_parameters : FieldParameters F}
        {width: Z}
        {BW: Bitwidth width}
        {word: word.word width}
        {mem: map.map word Byte.byte}
        :=
    { felem := list word;
      feval : felem -> F;

      feval_bytes : list byte -> F;
      felem_size_in_words : nat;
      felem_size_in_bytes : Z := Z.of_nat felem_size_in_words * bytes_per_word width; (* for stack allocation *)
      encoded_felem_size_in_bytes : nat; (* number of bytes when serialized *)
      bytes_in_bounds : list byte -> Prop;

      (* Memory layout *)

      bounds : Type;
      bounded_by : bounds -> felem -> Prop;
      maybe_bounded mbounds v :=
        match mbounds with
        | Some bounds => bounded_by bounds v
        | None => True
        end;
      FElem : option bounds -> word -> F -> mem -> Prop :=
        fun mbounds ptr v =>
          (Lift1Prop.ex1 (fun v' => (emp (feval v' = v /\ maybe_bounded mbounds v') ⋆ Bignum felem_size_in_words ptr v')%sep));
      FElemBytes : word -> list byte -> mem -> Prop :=
        fun addr bs =>
          (emp (length bs = encoded_felem_size_in_bytes
                /\ bytes_in_bounds bs)
          * array ptsto (word.of_Z 1) addr bs)%sep;

      (* for saturated implementations, loose/tight bounds are the same *)
      loose_bounds : bounds;
      tight_bounds : bounds;
    }.

  Definition Placeholder
            (F : Type)
            {field_parameters : FieldParameters F}
            {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
            {field_representation : FieldRepresentation F(mem:=mem)}
            (p : word) : mem -> Prop :=
    Memory.anybytes(mem:=mem) p felem_size_in_bytes.

  Class FieldRepresentation_ok
        (F : Type)
        {field_parameters : FieldParameters F}
        {width: Z}
        {BW: Bitwidth width}
        {word: word.word width}
        {mem: map.map word Byte.byte}
        {field_representation : FieldRepresentation F} := {
      relax_bounds :
        forall X : felem, bounded_by tight_bounds X
                          -> bounded_by loose_bounds X;
    }.

  Section BignumToFieldRepresentationAdapterLemmas.
    Context
    {F : Type}
    {field_parameters : FieldParameters F}
    {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
    {field_representation : FieldRepresentation F}.
    Context {word_ok : @word.ok width word} {map_ok : @map.ok word Init.Byte.byte mem}.

    Lemma felem_size_in_bytes_mod :
          felem_size_in_bytes mod Memory.bytes_per_word width = 0.
    Proof. apply Z_mod_mult. Qed.

    Lemma Bignum_from_bytes p : Lift1Prop.iff1 (Placeholder F p) (Lift1Prop.ex1 (Bignum felem_size_in_words p)).
    Proof.
      cbv [Placeholder FElem felem_size_in_bytes].
      repeat intro.
      cbv [Lift1Prop.ex1]; split; intros;
        repeat match goal with
              | H : anybytes _ _ _ |- _ => eapply Array.anybytes_to_array_1 in H
              | H : exists _, _ |- _ => destruct H
              | H : _ /\ _ |- _ => destruct H
              end.
        all : repeat match goal with
              | H : anybytes _ _ _ |- _ => eapply Array.anybytes_to_array_1 in H
              | H : exists _, _ |- _ => destruct H
              | H : _ /\ _ |- _ => destruct H
              end.
      { eexists; eapply Bignum_of_bytes; try eassumption.
        destruct Bitwidth.width_cases; subst width; revert H0; cbn; lia. }
      { eapply Bignum_to_bytes in H; sepsimpl.
        let H := match goal with
                | H : Array.array _ _ _ _ _ |- _ => H end in
        eapply Array.array_1_to_anybytes in H.
        unshelve (erewrite (_:_*_=_); eassumption).
        rewrite H; destruct Bitwidth.width_cases as [W|W];
          symmetry in W; destruct W; cbn; clear; lia. }
    Qed.

    Lemma Bignum_to_bytes px x :
      Lift1Prop.impl1 (Bignum felem_size_in_words px x) (Placeholder F px).
    Proof.
      rewrite Bignum_from_bytes.
      repeat intro; eexists; eauto.
    Qed.

    Lemma FElem_from_bytes
      : forall px : word.rep,
        Lift1Prop.iff1 (Placeholder F px) (Lift1Prop.ex1 (FElem None px)).
    Proof.
      unfold FElem.
      intros.
      split; intros.
      {
        apply Bignum_from_bytes in H.
        destruct H.
        do 2 eexists.
        sepsimpl; simpl; eauto.
      }
      {
        destruct H as [? [? ?]].
        sepsimpl.
        eapply Bignum_to_bytes; eauto.
      }
    Qed.
  End BignumToFieldRepresentationAdapterLemmas.

  Section ToFromBytes.
    Definition nth_byte (x : Z) (n : nat) : byte :=
      byte.of_Z (Z.shiftr x (8 * Z.of_nat n)).
    Definition Z_to_bytes (x : Z) (n : nat) : list byte :=
      List.map (nth_byte x) (seq 0 n).
    Definition Z_from_bytes (bs : list byte) : Z :=
      List.fold_right
        (fun b acc => Z.shiftl acc 8 + byte.unsigned b) 0 bs.
  End ToFromBytes.

  Section FunctionSpecs.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
    Context {locals: map.map String.string word}.
    Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
    Context {ext_spec: bedrock2.Semantics.ExtSpec}.
    Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
    Context {locals_ok : map.ok locals}.
    Context {env_ok : map.ok env}.
    Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
    (* Context {field_data : FieldData}. *)
    Context {F : Type}
            {field_parameters : FieldParameters F}
            {field_names : FieldNames F}
            {field_representation : FieldRepresentation F}
            {curve_parameters : CurveParameters F}
            {curve_names : CurveNames F}
    .

    Local Definition Fsquare (x : F) := Fmul x x.

    Import WeakestPrecondition.

    Class NullOp (name: string) :=
      { null_model: F;
        null_outbounds: bounds }.

    Definition nullop_spec {name} (op: NullOp name) :=
      fnspec! name (pout : word) / (out : F) Rr,
      { requires tr mem :=
          (FElem None pout out * Rr)%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            out = null_model
            /\ (FElem (Some null_outbounds) pout out * Rr)%sep mem' }.

    Instance spec_of_NullOp {name} (op: NullOp name) : spec_of name :=
      nullop_spec op.

    Class UnOp (name: string) :=
      { un_model: F -> F;
        un_xbounds: bounds;
        un_outbounds: bounds }.

    Definition unop_spec {name} (op: UnOp name) :=
      fnspec! name (pout px : word) / (out x : F) Rr,
      { requires tr mem :=
          (exists Ra, (FElem (Some un_xbounds) px x * Ra)%sep mem)
          /\ (FElem None pout out * Rr)%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            out = un_model x
            /\ (FElem (Some un_outbounds) pout out * Rr)%sep mem' }.

    Instance spec_of_UnOp {name} (op: UnOp name) : spec_of name :=
      unop_spec op.

    Class BinOp (name: string) :=
      { bin_model: F -> F -> F;
        bin_xbounds: bounds;
        bin_ybounds: bounds;
        bin_outbounds: bounds }.

    Definition binop_spec  {name} (op: BinOp name) :=
      fnspec! name (pout px py : word) / (out x y : F) Rr,
      { requires tr mem :=
          (exists Rx, (FElem (Some bin_xbounds) px x * Rx)%sep mem)
          /\ (exists Ry, (FElem (Some bin_ybounds) py y * Ry)%sep mem)
          /\ (FElem None pout out * Rr)%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            out = bin_model x y
            /\ (FElem (Some bin_outbounds) pout out * Rr)%sep mem' }.

    Instance spec_of_BinOp {name} (op: BinOp name) : spec_of name :=
      binop_spec op.

    Instance bin_mul : BinOp mul :=
      {| bin_model := Fmul; bin_xbounds := loose_bounds; bin_ybounds := loose_bounds; bin_outbounds := tight_bounds |}.
    Instance un_square : UnOp square :=
      {| un_model := fun x => Fsquare x; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
    Instance bin_add : BinOp add :=
      {| bin_model := Fadd; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
    Instance bin_sub : BinOp sub :=
      {| bin_model := Fsub; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
    Instance un_scmula24 : UnOp scmula24 :=
      {| un_model := Fmul a24; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
    Instance un_inv : UnOp inv := (* TODO: what are the bounds for inv? *)
      {| un_model := Finv; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.
    Instance un_opp : UnOp opp :=
      {| un_model := Fopp; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.
    Instance null_zero : NullOp zero :=
      {| null_model := Fzero; null_outbounds := tight_bounds |}.
    Instance null_one : NullOp one :=
      {| null_model := Fone; null_outbounds := tight_bounds |}.

    Instance spec_of_from_bytes : spec_of from_bytes :=
      fnspec! from_bytes (pout px : word) / out (bs : list byte) Rr,
      { requires tr mem :=
          (exists Ra, (FElemBytes px bs * Ra)%sep mem)
          /\ (FElem None pout out * Rr)%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists X, X = feval_bytes bs
              /\ (FElem (Some tight_bounds) pout X * Rr)%sep mem' }.

    Instance spec_of_to_bytes : spec_of to_bytes :=
      fnspec! to_bytes (pout px : word) / (out : list byte) (x : F) Rr,
      { requires tr mem :=
          (exists Ra, (FElem (Some tight_bounds) px x * Ra)%sep mem)
          /\ (FElemBytes pout out * Rr)%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists bs,
            x = feval_bytes bs /\
            (FElemBytes pout bs * Rr)%sep mem' }.

    Instance spec_of_felem_copy : spec_of felem_copy :=
      fnspec! felem_copy (pout px : word) / (out x : F) R Rout bounds,
      { requires tr mem :=
          (FElem bounds px x * FElem None pout out * R)%sep mem /\
          (FElem None pout out * Rout)%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          (FElem bounds pout x * Rout)%sep mem' }.

    Instance spec_of_from_word : spec_of from_word :=
      fnspec! from_word (pout x : word) / out R,
      { requires tr mem0 :=
          (FElem None pout out * R)%sep mem0;
        ensures tr' mem' :=
          tr = tr' /\
          exists X,  X = FofZ (word.unsigned x)
              /\ (FElem (Some tight_bounds) pout X * R)%sep mem' }.

    Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

    Instance spec_of_selectznz : spec_of select_znz :=
      fnspec! select_znz (pout pc px py : word) / out Rout Rx Ry x y ybounds xbounds,
        {
          requires tr mem :=
            (FElem None pout out * Rout)%sep mem /\
              (FElem xbounds px x * Rx)%sep mem /\
              (FElem ybounds py y * Ry)%sep mem /\
              ZRange.is_bounded_by_bool (word.unsigned pc) bit_range = true;
          ensures tr' mem' :=
            tr = tr' /\
            if ((word.unsigned pc) =? 1)
            then ((FElem ybounds pout y * Rout)%sep mem')
            else ((FElem xbounds pout x * Rout)%sep mem')
        }.

    Section FromList.
    Context (v : F).
    Context (name : string).

    Instance spec_of_from_list  : spec_of name :=
    fnspec! name (pout : word) / outold Rout,
    {
        requires tr mem :=
        (FElem None pout outold * Rout)%sep mem ;
        ensures tr' mem' := exists out,
        tr = tr' /\
          out = v /\
          (FElem (Some loose_bounds) pout out * Rout)%sep mem'
    }.
    End FromList.

  End FunctionSpecs.

  Existing Instances spec_of_UnOp spec_of_BinOp bin_mul un_square bin_add bin_sub
          un_scmula24
          un_inv spec_of_felem_copy.

End FieldSpecs.

(* Require Import Crypto.Bedrock.Specs.Field. *)
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import coqutil.Byte.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZUtil.ModInv.
Local Open Scope Z_scope.
Import bedrock2.Memory.

Section Field.

  Class PrimeParameters :=
    {
      M_pos : positive; (* modulus *)
      M : Z := Z.pos M_pos;
    }.

  Class PrimeParameters_ok {prime_parameters : PrimeParameters} := {
    M_prime : Znumtheory.prime M
  }.

  Section Specialized.
    Context {params : PrimeParameters}
            {names : FieldNames (F M_pos)}
            {params_ok : PrimeParameters_ok}
            {width: Z}
            {BW: Bitwidth width}
            {word: word.word width}
            {mem: map.map word Byte.byte}.

    Instance Field : (@field (F M_pos) (@eq (F M_pos)) (F.zero) (F.one) F.opp F.add F.sub F.mul F.inv F.div) := @F.field_modulo M_pos M_prime.

    Instance prime_field_parameters : FieldParameters (F M_pos).
    Proof.
      econstructor.
        - exact (@F.zero M_pos).
        - exact (@F.one M_pos).
        - exact (@F.opp M_pos).
        - exact (@F.inv M_pos).
        - exact (@F.add M_pos).
        - exact (@F.sub M_pos).
        - exact (@F.mul M_pos).
        - exact (@F.div M_pos).
        - exact (@F.of_Z _).
        - apply F.eq_dec.
    Defined.

    Instance prime_field_parameters_ok : FieldParameters_ok (F M_pos) := {| fld := Field |}.

    Context {field_representation : FieldRepresentation (F M_pos)}
            {field_representation_ok : FieldRepresentation_ok (F M_pos)}.

(*     (* Parameters for word-by-word Montgomery arithmetic*) *)
      Definition r := 2 ^ width.
      Definition m' := Z.modinv (- M) r.
      Definition r' := Z.modinv (r) M.

      Definition from_mont_model x := @F.mul M_pos x (@F.of_Z M_pos (r' ^ (Z.of_nat felem_size_in_words)%Z)).
      Definition to_mont_model x := @F.mul M_pos x (@F.of_Z M_pos (r ^ (Z.of_nat felem_size_in_words)%Z)).

      Instance un_from_mont {from_mont : string} : UnOp from_mont :=
        {| un_model := from_mont_model; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.

      Instance un_to_mont {to_mont : string} : UnOp to_mont :=
        {| un_model := to_mont_model; un_xbounds := tight_bounds; un_outbounds := loose_bounds|}.

  End Specialized.
End Field.
