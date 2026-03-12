(** * Rupicola compilation layer for cubic extensions (Fp6 = Fp2[v]/(v^3 - xi)).

    Analogous to QuadraticFieldExtensions.v for Fp2.

    Defines bedrock2 function bodies for Fp6 operations.  Includes a
    fp2_mul_xi helper (multiply by xi = 1+u), Karatsuba Fp6 multiplication,
    Chung-Hasan SQR3 squaring, and cubic extension inverse.
    WP proofs are currently stubs (exact I).
*)

Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Export Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.BLS12Pairing.Fp6.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Section Fp6.
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

  Existing Instance prime_field_parameters.

  Context {F_representation : AbstractField.FieldRepresentation (F:=Fp)}
          {F_representation_ok : AbstractField.FieldRepresentation_ok (F:=Fp)}.

  (* note that this excludes non-saturated representations *)
  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  (* Prefixes for function names *)
  Variable fp6_prefix : string.
  Variable fp2_prefix : string.

  (* ================================================================ *)
  (* Fp2 instances from the quadratic layer                            *)
  (* ================================================================ *)

  Local Instance Fp2_fp_inst : AbstractField.FieldParameters Fp2 :=
    Fp2_field_parameters (fp2_prefix:=fp2_prefix).
  Local Instance Fp2_fp_ok_inst : @AbstractField.FieldParameters_ok _ Fp2_fp_inst :=
    @Fp2_field_parameters_ok prime_parameters prime_parameters_ok M_mod fp2_prefix.
  Local Instance Fp2_repr_inst : @AbstractField.FieldRepresentation Fp2 Fp2_fp_inst width BW word mem :=
    @Fp2_field_representation width BW word mem prime_parameters F_representation fp2_prefix.
  Local Instance Fp2_repr_ok_inst : @AbstractField.FieldRepresentation_ok Fp2 Fp2_fp_inst _ _ _ _ Fp2_repr_inst :=
    @Fp2_field_representation_ok width BW word mem prime_parameters F_representation F_representation_ok fp2_prefix.

  (* ================================================================ *)
  (* Fp6 instances from the cubic layer                                *)
  (* ================================================================ *)

  Local Instance Fp6_fp_inst : AbstractField.FieldParameters Fp6 :=
    Fp6_field_parameters (fp6_prefix:=fp6_prefix).

  Local Instance Fp6_repr_inst : @AbstractField.FieldRepresentation Fp6 Fp6_fp_inst width BW word mem :=
    Fp6_field_representation (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  Local Instance Fp6_repr_ok_inst : @AbstractField.FieldRepresentation_ok Fp6 Fp6_fp_inst _ _ _ _ Fp6_repr_inst :=
    Fp6_field_representation_ok (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  (* ================================================================ *)
  (* FElem with optional bounds (reused from QuadraticFieldExtensions) *)
  (* ================================================================ *)

  Local Definition FElem
    {F' : Type} {fp' : AbstractField.FieldParameters F'}
    {fr' : @AbstractField.FieldRepresentation F' fp' width BW word mem}
    (mbounds : option (@AbstractField.bounds F' fp' _ _ _ _ fr'))
    (px : word) (v : F') : mem -> Prop :=
    Lift1Prop.ex1 (fun ws : @AbstractField.felem F' fp' _ _ _ _ fr' =>
      (emp (@AbstractField.feval F' fp' _ _ _ _ fr' ws = v /\
            match mbounds with
            | Some b => @AbstractField.bounded_by F' fp' _ _ _ _ fr' b ws
            | None => True
            end)
       * @AbstractField.FElem F' fp' _ _ _ _ fr' px ws)%sep).

  (* ================================================================ *)
  (* Fp2-level offset helpers                                          *)
  (* ================================================================ *)

  (* Offset in bytes for one Fp2 element = 2 * felem_size_in_words * bytes_per_word *)
  Local Notation fp2_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).
  Local Notation fp2_felem_offset_word := (word.of_Z fp2_felem_offset).

  (* Offset to 2nd Fp2 component = 1 * fp2_felem_offset *)
  Local Definition fp6_c1_offset : word := fp2_felem_offset_word.
  (* Offset to 3rd Fp2 component = 2 * fp2_felem_offset *)
  Local Definition fp6_c2_offset : word := word.of_Z (2 * fp2_felem_offset).

  (* Helper: offset expression to the ith Fp2 component *)
  Local Definition expr_fp6_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp6_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp2_felem_offset).
  Local Definition expr_fp6_c2 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal (2 * fp2_felem_offset)).

  (* ================================================================ *)
  (* Fp-level offset helpers (for accessing Fp components within Fp2) *)
  (* ================================================================ *)

  Local Notation fp_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).
  Local Definition expr_fp_snd (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp_felem_offset).

  (* ================================================================ *)
  (* Fp6 FElem decomposition and reassembly                           *)
  (* ================================================================ *)

  Local Notation FElem_Fp2 := (@AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
  Local Notation Fp2_felem_size := (@AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).

  Lemma Fp6_list_decomp : forall l, c0_felem l ++ c1_felem l ++ c2_felem l = l.
  Proof.
    intros. unfold c0_felem, c1_felem, c2_felem.
    set (n := (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat).
    replace (2 * n)%nat with (n + n)%nat by lia.
    change (skipn (n + n) l) with (ListDef.skipn (n + n) l).
    rewrite <- Lists.List.skipn_skipn.
    change (ListDef.skipn n (ListDef.skipn n l)) with (skipn n (skipn n l)).
    rewrite (QuadraticFieldExtensions.firstn_skipn (skipn n l) n).
    apply QuadraticFieldExtensions.firstn_skipn.
  Qed.

  Lemma Fp2_FElem_length pout
    (out : @AbstractField.felem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) m :
    FElem_Fp2 pout out m ->
    length out = Fp2_felem_size.
  Proof.
    unfold AbstractField.FElem, Bignum.Bignum.
    intros [me [ma [_ [[_ H] _]]]]. exact H.
  Qed.

  Lemma c0_felem_length (l : list word) :
    length l = (3 * Fp2_felem_size)%nat ->
    length (c0_felem l) = Fp2_felem_size.
  Proof.
    intros. unfold c0_felem.
    apply QuadraticFieldExtensions.length_firstn. lia.
  Qed.

  Local Notation fp_felem_size := (@AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).

  Lemma c1_felem_length (l : list word) :
    length l = (3 * Fp2_felem_size)%nat ->
    length (c1_felem l) = Fp2_felem_size.
  Proof.
    intros. unfold c1_felem.
    set (n := Fp2_felem_size) in *.
    apply QuadraticFieldExtensions.length_firstn.
    change (skipn n l) with (ListDef.skipn n l).
    rewrite Lists.List.length_skipn.
    change (2 * fp_felem_size)%nat with n. lia.
  Qed.

  Lemma c2_felem_length (l : list word) :
    length l = (3 * Fp2_felem_size)%nat ->
    length (c2_felem l) = Fp2_felem_size.
  Proof.
    intros. unfold c2_felem.
    set (n := Fp2_felem_size) in *.
    change (skipn (2 * n) l) with (ListDef.skipn (2 * n) l).
    rewrite Lists.List.length_skipn.
    change (2 * fp_felem_size)%nat with n. lia.
  Qed.

  Lemma Fp6_raw_FElem_split pout
    (out : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) m :
    @AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst pout out m ->
    (FElem_Fp2 pout (c0_felem out) *
     (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem out) *
      FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem out)))%sep m.
  Proof.
    intros H.
    unfold AbstractField.FElem, Bignum.Bignum in *.
    destruct H as [me [ma [Hms [[Hme Hlen] Ha]]]].
    subst me.
    assert (m = ma) by (apply Properties.map.split_empty_l in Hms; exact Hms). subst.
    set (n := Fp2_felem_size) in *.
    change (@AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
      with (3 * n)%nat in Hlen.
    assert (Hdecomp : out = c0_felem out ++ c1_felem out ++ c2_felem out)
      by (symmetry; apply Fp6_list_decomp).
    rewrite Hdecomp in Ha.
    (* First split: c0 ++ (c1 ++ c2) *)
    apply array_append' in Ha.
    destruct Ha as [m0 [m12 [Hms01 [Ha0 Ha12]]]].
    assert (Hlen0 : length (c0_felem out) = n) by (apply c0_felem_length; lia).
    rewrite Hlen0 in Ha12.
    rewrite <- (@word.ring_morph_mul _ _ word_ok) in Ha12.
    (* Second split: c1 ++ c2 *)
    apply array_append' in Ha12.
    destruct Ha12 as [m1 [m2 [Hms12 [Ha1 Ha2]]]].
    assert (Hlen1 : length (c1_felem out) = n) by (apply c1_felem_length; lia).
    rewrite Hlen1 in Ha2.
    rewrite <- (@word.ring_morph_mul _ _ word_ok) in Ha2.
    (* Fix c2 address: (pout + off1) + off1 = pout + off2 *)
    replace (word.add (word.add pout (word.of_Z (Memory.bytes_per_word width * Z.of_nat n)))
                      (word.of_Z (Memory.bytes_per_word width * Z.of_nat n)))
      with (word.add pout fp6_c2_offset) in Ha2
      by (unfold fp6_c2_offset; fold n;
          replace (2 * (Memory.bytes_per_word width * Z.of_nat n))
            with (Memory.bytes_per_word width * Z.of_nat n + Memory.bytes_per_word width * Z.of_nat n) by lia;
          rewrite word.ring_morph_add; apply word.add_assoc).
    (* Assemble the 3 FElems *)
    exists m0, (map.putmany m1 m2).
    destruct Hms01 as [Heq01 Hd01]. subst.
    destruct Hms12 as [Heq12 Hd12]. subst.
    split; [split; [reflexivity | exact Hd01] |]. split.
    - exists map.empty, m0. split. { apply Properties.map.split_empty_l. reflexivity. }
      split; [split; [exact eq_refl | exact Hlen0] | exact Ha0].
    - exists m1, m2. split; [split; [reflexivity | exact Hd12] |]. split.
      + exists map.empty, m1. split. { apply Properties.map.split_empty_l. reflexivity. }
        split; [split; [exact eq_refl | exact Hlen1] | exact Ha1].
      + exists map.empty, m2. split. { apply Properties.map.split_empty_l. reflexivity. }
        split; [split; [exact eq_refl |] | exact Ha2].
        apply c2_felem_length. lia.
  Qed.

  Lemma Fp6_raw_FElem_join pout c0 c1 c2 m :
    length c0 = Fp2_felem_size ->
    length c1 = Fp2_felem_size ->
    length c2 = Fp2_felem_size ->
    (FElem_Fp2 pout c0 *
     (FElem_Fp2 (word.add pout fp6_c1_offset) c1 *
      FElem_Fp2 (word.add pout fp6_c2_offset) c2))%sep m ->
    @AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst pout (c0 ++ c1 ++ c2) m.
  Proof.
    intros Hlen0 Hlen1 Hlen2 H.
    unfold AbstractField.FElem, Bignum.Bignum in *.
    destruct H as [m0 [m12 [Hms01 [H0 H12]]]].
    destruct H0 as [me0 [ma0 [Hms0 [[Hme0 Hlen0'] Ha0]]]].
    subst me0. assert (m0 = ma0) by (apply Properties.map.split_empty_l in Hms0; exact Hms0). subst.
    destruct H12 as [m1 [m2 [Hms12 [H1 H2]]]].
    destruct H1 as [me1 [ma1 [Hms1 [[Hme1 Hlen1'] Ha1]]]].
    subst me1. assert (m1 = ma1) by (apply Properties.map.split_empty_l in Hms1; exact Hms1). subst.
    destruct H2 as [me2 [ma2 [Hms2 [[Hme2 Hlen2'] Ha2]]]].
    subst me2. assert (m2 = ma2) by (apply Properties.map.split_empty_l in Hms2; exact Hms2). subst.
    set (n := Fp2_felem_size) in *.
    exists map.empty, m. split. { apply Properties.map.split_empty_l. reflexivity. }
    split.
    - split; [exact eq_refl |].
      rewrite !length_app.
      change (@AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst)
        with (3 * n)%nat. lia.
    - (* Join arrays using array_append' *)
      pose proof (proj2 (array_append'
        scalar (word.of_Z (Memory.bytes_per_word width))
        c0 (c1 ++ c2) pout m)) as Hback.
      apply Hback. clear Hback.
      exists ma0, (map.putmany ma1 ma2).
      destruct Hms01 as [Heq01 Hd01]. subst.
      destruct Hms12 as [Heq12 Hd12]. subst.
      split; [split; [reflexivity | exact Hd01] |]. split.
      { exact Ha0. }
      { rewrite Hlen0'. rewrite <- (@word.ring_morph_mul _ _ word_ok).
        pose proof (proj2 (array_append'
          scalar (word.of_Z (Memory.bytes_per_word width))
          c1 c2 (word.add pout (word.of_Z (Memory.bytes_per_word width * Z.of_nat n))) (map.putmany ma1 ma2))) as Hback2.
        apply Hback2. clear Hback2.
        exists ma1, ma2.
        split; [split; [reflexivity | exact Hd12] |]. split.
        { exact Ha1. }
        { rewrite Hlen1'. rewrite <- (@word.ring_morph_mul _ _ word_ok).
          replace (word.add (word.add pout (word.of_Z (Memory.bytes_per_word width * Z.of_nat n)))
                            (word.of_Z (Memory.bytes_per_word width * Z.of_nat n)))
            with (word.add pout fp6_c2_offset)
            by (unfold fp6_c2_offset; fold n;
                replace (2 * (Memory.bytes_per_word width * Z.of_nat n))
                  with (Memory.bytes_per_word width * Z.of_nat n + Memory.bytes_per_word width * Z.of_nat n) by lia;
                rewrite word.ring_morph_add; apply word.add_assoc).
          exact Ha2. } }
  Qed.

  (* ================================================================ *)
  (* spec_of instances for the underlying Fp2 operations               *)
  (* ================================================================ *)

  Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
    AbstractField.spec_of_felem_copy (F:=Fp2).
  Instance spec_of_Fp2_add : spec_of (AbstractField.add (F:=Fp2)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=Fp2).
  Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=Fp2).
  Instance spec_of_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=Fp2).
  Instance spec_of_Fp2_opp : spec_of (AbstractField.opp (F:=Fp2)) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=Fp2).
  Instance spec_of_Fp2_square : spec_of (AbstractField.square (F:=Fp2)) :=
    AbstractField.unop_spec AbstractField.un_square (F:=Fp2).
  Instance spec_of_Fp2_inv : spec_of (AbstractField.inv (F:=Fp2)) :=
    AbstractField.unop_spec AbstractField.un_inv (F:=Fp2).

  (* Fp-level spec_of instances (used by fp2_mul_xi) *)
  Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
    AbstractField.spec_of_felem_copy (F:=Fp).
  Instance spec_of_Fp_add : spec_of (AbstractField.add (F:=Fp)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=Fp).
  Instance spec_of_Fp_sub : spec_of (AbstractField.sub (F:=Fp)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=Fp).

  (* Function name for the fp2_mul_xi helper *)
  Local Definition fp2_mul_xi_name := (fp2_prefix ++ "mul_xi")%string.

  (* ================================================================ *)
  (* FieldNames for Fp6                                                *)
  (* ================================================================ *)

  Context {Fp6_names : FieldNames (F:=Fp6)}.
  Context {Fp2_names : FieldNames (F:=Fp2)}.
  Context {Fp_names : FieldNames (F:=Fp)}.

  (* ================================================================ *)
  (* Fp6 function bodies (placeholder: cmd.skip)                       *)
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

  (* -------------------------------------------------------------- *)
  (* fp2_mul_xi: multiply Fp2 element by xi = 1+u                    *)
  (*   (a0, a1) -> (a0 - a1, a0 + a1)                                *)
  (* -------------------------------------------------------------- *)

  Definition Fp2_mul_xi : function_t :=
    (fp2_mul_xi_name, (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp)) [expr.var "tmp"; expr.var "x"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp)) [expr_fp_snd (expr.var "tmp"); expr_fp_snd (expr.var "x")]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp)) [expr.var "out"; expr.var "tmp"; expr_fp_snd (expr.var "tmp")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp)) [expr_fp_snd (expr.var "out"); expr.var "tmp"; expr_fp_snd (expr.var "tmp")])
    ))).

  Lemma Fp2_mul_xi_ok : program_logic_goal_for_function! Fp2_mul_xi.
  Proof. exact I. Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_copy: copy 3 Fp2 elements                                   *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_felem_copy : function_t :=
    (AbstractField.felem_copy (F:=Fp6), (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "x")]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "x")]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "x")])
    ))).

  Instance spec_of_Fp6_copy : spec_of (AbstractField.felem_copy (F:=Fp6)) :=
    AbstractField.spec_of_felem_copy (F:=Fp6).

  (* Disjointness automation for map algebra *)
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

  (* Swap two adjacent elements in a right-associated putmany chain:
     putmany a (putmany b X) → putmany b (putmany a X) *)
  Local Ltac map_swap a b :=
    rewrite (map.putmany_assoc a b);
    let D := fresh "D" in
    assert (D : map.disjoint a b) by map_disjoint_auto;
    rewrite (map.putmany_comm a b D);
    clear D;
    rewrite <- (map.putmany_assoc b a).

  Lemma Fp6_felem_copy_ok : program_logic_goal_for_function! Fp6_felem_copy.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2 HFcopy3.
    unfold spec_of_Fp6_copy, AbstractField.spec_of_felem_copy.
    intros pout px out x R Rout tr mem0 [Hmem0_1 Hmem0_2].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_felem_copy].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for first call: [out; x] (c0 at offset 0) *)
    exists [pout; px]. split.
    { unfold dexprs, expr_fp6_c0. repeat straightline.
      eexists. split. { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
      cbv [list_map]. eexists. split.
      { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body]. apply map.get_put_same. }
      exact eq_refl. }
    (* === Decompose preconditions === *)
    destruct Hmem0_1 as [m_x [m_or [Hsep1 [Hx Hor]]]].
    destruct Hor as [m_o [m_r [Hsep_or [Ho Hr]]]].
    (* Split Fp6 FElems into 3 Fp2 components *)
    pose proof (Fp6_raw_FElem_split _ _ _ Hx) as Hx_split.
    destruct Hx_split as [m_x0 [m_x12 [Hsep_x [Hx0 Hx12]]]].
    destruct Hx12 as [m_x1 [m_x2 [Hsep_x12 [Hx1 Hx2]]]].
    pose proof (Fp6_raw_FElem_split _ _ _ Ho) as Ho_split.
    destruct Ho_split as [m_o0 [m_o12 [Hsep_o [Ho0 Ho12]]]].
    destruct Ho12 as [m_o1 [m_o2 [Hsep_o12 [Ho1 Ho2]]]].
    (* Relate two preconditions using FElem_to_bytes + anybytes_unique_domain *)
    destruct Hmem0_2 as [m_o' [m_rout [Hsep2 [Ho' Hrout]]]].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout out m_o Ho) as Hph_o.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout out m_o' Ho') as Hph_o'.
    unfold AbstractField.Placeholder in Hph_o, Hph_o'.
    pose proof (Memory.anybytes_unique_domain _ _ _ _ Hph_o Hph_o') as Hsd.
    destruct Hsep1 as [Heq1 Hd1]. destruct Hsep_or as [Heq_or Hd_or]. subst m_or mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd1) as [Hd_x_o Hd_x_r].
    assert (Hsplit_mem : map.split (map.putmany m_x (map.putmany m_o m_r)) m_o (map.putmany m_x m_r)).
    { split.
      { rewrite map.putmany_assoc.
        rewrite (map.putmany_comm m_x m_o Hd_x_o).
        symmetry. apply map.putmany_assoc. }
      { apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x_o k v2 v1 Hg2 Hg1). }
        { exact Hd_or. } } }
    pose proof (proj1 (map.split_comm _ _ _) Hsplit_mem) as Hsplit_mem'.
    pose proof (proj1 (map.split_comm _ _ _) Hsep2) as Hsep2'.
    pose proof (map.split_diff Hsd Hsplit_mem' Hsep2') as [Heq_rout Heq_o'].
    subst m_o'.
    rewrite <- Heq_rout in Hrout.
    clear Heq_rout Hsd Hsep2 Hsep2' Hsplit_mem Hsplit_mem' Hph_o Hph_o' Ho'.
    (* Now: Hrout : Rout (map.putmany m_x m_r) *)
    (* Inline map.split equalities *)
    destruct Hsep_x as [Heq_x Hd_x012]. destruct Hsep_x12 as [Heq_x12 Hd_x12].
    destruct Hsep_o as [Heq_o Hd_o012]. destruct Hsep_o12 as [Heq_o12 Hd_o12].
    subst m_x m_o m_x12 m_o12.
    (* Derive pairwise disjointness *)
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_o) as [Hd_x0_o Hd_x12_o].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x12_o) as [Hd_x1_o Hd_x2_o].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x0_o) as [Hd_x0_o0 Hd_x0_o12].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x0_o12) as [Hd_x0_o1 Hd_x0_o2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x1_o) as [Hd_x1_o0 Hd_x1_o12].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x1_o12) as [Hd_x1_o1 Hd_x1_o2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x2_o) as [Hd_x2_o0 Hd_x2_o12].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x2_o12) as [Hd_x2_o1 Hd_x2_o2].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_r) as [Hd_x0_r Hd_x12_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x12_r) as [Hd_x1_r Hd_x2_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_or) as [Hd_o0_r Hd_o12_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_o12_r) as [Hd_o1_r Hd_o2_r].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x012) as [Hd_x0_x1 Hd_x0_x2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_o012) as [Hd_o0_o1 Hd_o0_o2].
    clear Hd_x_o Hd_x_r Hd_or Hd1 Hd_x0_o Hd_x12_o Hd_x0_o12 Hd_x1_o Hd_x1_o12 Hd_x2_o Hd_x2_o12 Hd_x12_r Hd_o12_r.
    (* === First Fp2 copy call (c0) via weaken_call === *)
    set (rest1 := map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_o1 (map.putmany m_o2 m_r))))).
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 pout px (c0_felem out) (c0_felem x)
        (fun m => (FElem_Fp2 (word.add px fp6_c1_offset) (c1_felem x) ⋆
                   (FElem_Fp2 (word.add px fp6_c2_offset) (c2_felem x) ⋆
                    (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem out) ⋆
                     (FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem out) ⋆ R)))) m)
        (eq rest1)
        tr).
      split.
      { (* Precondition 1: (FElem px (c0 x) * FElem pout (c0 out) * frame) *)
        exists (map.putmany m_x0 m_o0),
               (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_o1 (map.putmany m_o2 m_r)))).
        split; [split |].
        { rewrite !map.putmany_assoc.
          repeat (apply f_equal2; [| reflexivity]).
          rewrite (map.disjoint_putmany_commutes _ m_x2 m_o0 Hd_x2_o0).
          rewrite (map.disjoint_putmany_commutes m_x0 m_x1 m_o0 Hd_x1_o0).
          reflexivity. }
        { map_disjoint_auto. }
        split.
        { exists m_x0, m_o0.
          split; [split; [reflexivity | exact Hd_x0_o0] |].
          split; [exact Hx0 | exact Ho0]. }
        { exists m_x1, (map.putmany m_x2 (map.putmany m_o1 (map.putmany m_o2 m_r))).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx1 |].
          exists m_x2, (map.putmany m_o1 (map.putmany m_o2 m_r)).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx2 |].
          exists m_o1, (map.putmany m_o2 m_r).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Ho1 |].
          exists m_o2, m_r.
          split; [split; [reflexivity | exact Hd_o2_r] |].
          split; [exact Ho2 | exact Hr]. } }
      { (* Precondition 2: (FElem pout (c0 out) * eq rest1) *)
        exists m_o0, rest1.
        split; [split |].
        { subst rest1.
          rewrite !map.putmany_assoc.
          repeat (apply f_equal2; [| reflexivity]).
          rewrite (map.disjoint_putmany_commutes _ m_x2 m_o0 Hd_x2_o0).
          rewrite (map.disjoint_putmany_commutes m_x0 m_x1 m_o0 Hd_x1_o0).
          rewrite (map.putmany_comm m_x0 m_o0 Hd_x0_o0).
          reflexivity. }
        { subst rest1. map_disjoint_auto. }
        split; [exact Ho0 | exact eq_refl]. } }
    (* === Process postcondition of first call === *)
    intros t' m' rets [Hrets [Htr1 Hsep_post1]].
    subst rets. symmetry in Htr1. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for second call: [out+off1; x+off1] *)
    eexists. split.
    { unfold dexprs. repeat straightline.
      exists pout. split.
      { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body expr_fp6_c1].
      repeat straightline.
      unfold list_map. repeat straightline.
      exists px. split. { apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat straightline. exact eq_refl. }
    (* Unpack postcondition of first call *)
    destruct Hsep_post1 as [m_new0 [m_frame1 [Hsp_post1 [Hnew0 Hframe1]]]].
    subst m_frame1.
    destruct Hsp_post1 as [Heq_p1 Hd_p1].
    subst rest1.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p1) as [Hd_n0_x0 Hd_n0_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n0_rest) as [Hd_n0_x1 Hd_n0_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n0_rest2) as [Hd_n0_x2 Hd_n0_rest3].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n0_rest3) as [Hd_n0_o1 Hd_n0_rest4].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n0_rest4) as [Hd_n0_o2 Hd_n0_r].
    clear Hd_n0_rest Hd_n0_rest2 Hd_n0_rest3 Hd_n0_rest4.
    (* === Second Fp2 copy call (c1) via weaken_call === *)
    set (rest2 := map.putmany m_new0 (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_o2 m_r))))).
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 (word.add pout fp6_c1_offset) (word.add px fp6_c1_offset)
        (c1_felem out) (c1_felem x)
        (fun m => (FElem_Fp2 pout (c0_felem x) ⋆
                   (FElem_Fp2 px (c0_felem x) ⋆
                    (FElem_Fp2 (word.add px fp6_c2_offset) (c2_felem x) ⋆
                     (FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem out) ⋆ R)))) m)
        (eq rest2)
        tr).
      split.
      { (* Precondition 1: (FElem (px+off1) (c1 x) * FElem (pout+off1) (c1 out) * frame) m' *)
        subst m'.
        exists (map.putmany m_x1 m_o1),
               (map.putmany m_new0 (map.putmany m_x0 (map.putmany m_x2 (map.putmany m_o2 m_r)))).
        split; [split |].
        { map_swap m_x2 m_o1.
          map_swap m_x0 m_x1.
          map_swap m_new0 m_x1.
          map_swap m_x0 m_o1.
          map_swap m_new0 m_o1.
          rewrite <- (map.putmany_assoc m_x1 m_o1).
          reflexivity. }
        { map_disjoint_auto. }
        split.
        { exists m_x1, m_o1.
          split; [split; [reflexivity | exact Hd_x1_o1] |].
          split; [exact Hx1 | exact Ho1]. }
        { exists m_new0, (map.putmany m_x0 (map.putmany m_x2 (map.putmany m_o2 m_r))).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hnew0 |].
          exists m_x0, (map.putmany m_x2 (map.putmany m_o2 m_r)).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx0 |].
          exists m_x2, (map.putmany m_o2 m_r).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx2 |].
          exists m_o2, m_r.
          split; [split; [reflexivity | exact Hd_o2_r] |].
          split; [exact Ho2 | exact Hr]. } }
      { (* Precondition 2: (FElem (pout+off1) (c1 out) * eq rest2) m' *)
        subst m'.
        exists m_o1, rest2.
        split; [split |].
        { subst rest2.
          map_swap m_x2 m_o1.
          map_swap m_x1 m_o1.
          map_swap m_x0 m_o1.
          map_swap m_new0 m_o1.
          reflexivity. }
        { subst rest2. map_disjoint_auto. }
        split; [exact Ho1 | exact eq_refl]. } }
    (* === Process postcondition of second call === *)
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_post2]].
    subst rets2. symmetry in Htr2. subst t''.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for third call: [out+off2; x+off2] *)
    eexists. split.
    { unfold dexprs. repeat straightline.
      exists pout. split.
      { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body expr_fp6_c2].
      repeat straightline.
      unfold list_map. repeat straightline.
      exists px. split. { apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat straightline. exact eq_refl. }
    (* Unpack postcondition of second call *)
    destruct Hsep_post2 as [m_new1 [m_frame2 [Hsp_post2 [Hnew1 Hframe2]]]].
    subst m_frame2.
    destruct Hsp_post2 as [Heq_p2 Hd_p2].
    subst rest2.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p2) as [Hd_n1_n0 Hd_n1_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest) as [Hd_n1_x0 Hd_n1_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest2) as [Hd_n1_x1 Hd_n1_rest3].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest3) as [Hd_n1_x2 Hd_n1_rest4].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest4) as [Hd_n1_o2 Hd_n1_r].
    clear Hd_n1_rest Hd_n1_rest2 Hd_n1_rest3 Hd_n1_rest4.
    (* === Third Fp2 copy call (c2) via weaken_call === *)
    set (rest3 := map.putmany m_new0 (map.putmany m_new1 (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_x2 m_r))))).
    eapply Semantics.weaken_call.
    { eapply (HFcopy3 (word.add pout fp6_c2_offset) (word.add px fp6_c2_offset)
        (c2_felem out) (c2_felem x)
        (fun m => (FElem_Fp2 pout (c0_felem x) ⋆
                   (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem x) ⋆
                    (FElem_Fp2 px (c0_felem x) ⋆
                     (FElem_Fp2 (word.add px fp6_c1_offset) (c1_felem x) ⋆ R)))) m)
        (eq rest3)
        tr).
      split.
      { (* Precondition 1: (FElem (px+off2) (c2 x) * FElem (pout+off2) (c2 out) * frame) m'' *)
        subst m''.
        exists (map.putmany m_x2 m_o2),
               (map.putmany m_new0 (map.putmany m_new1 (map.putmany m_x0 (map.putmany m_x1 m_r)))).
        split; [split |].
        { map_swap m_x1 m_x2.
          map_swap m_x0 m_x2.
          map_swap m_new0 m_x2.
          map_swap m_new1 m_x2.
          map_swap m_x1 m_o2.
          map_swap m_x0 m_o2.
          map_swap m_new0 m_o2.
          map_swap m_new1 m_o2.
          map_swap m_new1 m_new0.
          rewrite <- (map.putmany_assoc m_x2 m_o2).
          reflexivity. }
        { map_disjoint_auto. }
        split.
        { exists m_x2, m_o2.
          split; [split; [reflexivity | exact Hd_x2_o2] |].
          split; [exact Hx2 | exact Ho2]. }
        { exists m_new0, (map.putmany m_new1 (map.putmany m_x0 (map.putmany m_x1 m_r))).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hnew0 |].
          exists m_new1, (map.putmany m_x0 (map.putmany m_x1 m_r)).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hnew1 |].
          exists m_x0, (map.putmany m_x1 m_r).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx0 |].
          exists m_x1, m_r.
          split; [split; [reflexivity | exact Hd_x1_r] |].
          split; [exact Hx1 | exact Hr]. } }
      { (* Precondition 2: (FElem (pout+off2) (c2 out) * eq rest3) m'' *)
        subst m''.
        exists m_o2, rest3.
        split; [split |].
        { subst rest3.
          map_swap m_x2 m_o2.
          map_swap m_x1 m_o2.
          map_swap m_x0 m_o2.
          map_swap m_new0 m_o2.
          map_swap m_new1 m_o2.
          map_swap m_new1 m_new0.
          reflexivity. }
        { subst rest3. map_disjoint_auto. }
        split; [exact Ho2 | exact eq_refl]. } }
    (* === Final: process third postcondition and close === *)
    intros t''' m''' rets3 [Hrets3 [Htr3 Hsep_post3]].
    subst rets3. symmetry in Htr3. subst t'''.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. }
    split. { exact eq_refl. }
    (* Destruct third postcondition *)
    destruct Hsep_post3 as [m_new2 [m_frame3 [Hsp_post3 [Hnew2 Hframe3]]]].
    subst m_frame3.
    destruct Hsp_post3 as [Heq_p3 Hd_p3].
    subst rest3.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p3) as [Hd_n2_n0 Hd_n2_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest) as [Hd_n2_n1 Hd_n2_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest2) as [Hd_n2_x0 Hd_n2_rest3].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest3) as [Hd_n2_x1 Hd_n2_rest4].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest4) as [Hd_n2_x2 Hd_n2_r].
    clear Hd_n2_rest Hd_n2_rest2 Hd_n2_rest3 Hd_n2_rest4.
    (* Reconstruct Fp6 FElem for x *)
    assert (Hdecomp : x = c0_felem x ++ c1_felem x ++ c2_felem x)
      by (symmetry; apply Fp6_list_decomp).
    rewrite Hdecomp.
    exists (map.putmany m_new0 (map.putmany m_new1 m_new2)),
           (map.putmany (map.putmany m_x0 (map.putmany m_x1 m_x2)) m_r).
    split; [split |].
    { subst m'''.
      map_swap m_new2 m_new0.
      map_swap m_new2 m_new1.
      rewrite <- !map.putmany_assoc.
      reflexivity. }
    { map_disjoint_auto. }
    split.
    { (* Fp6_raw_FElem_join *)
      apply Fp6_raw_FElem_join.
      { exact (Fp2_FElem_length _ _ _ Hnew0). }
      { exact (Fp2_FElem_length _ _ _ Hnew1). }
      { exact (Fp2_FElem_length _ _ _ Hnew2). }
      exists m_new0, (map.putmany m_new1 m_new2).
      split; [split; [reflexivity |] |].
      { apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n1_n0 k v2 v1 Hg2 Hg1). }
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n2_n0 k v2 v1 Hg2 Hg1). } }
      split; [exact Hnew0 |].
      exists m_new1, m_new2.
      split; [split; [reflexivity |] |].
      { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n2_n1 k v2 v1 Hg2 Hg1). }
      split; [exact Hnew1 | exact Hnew2]. }
    { exact Hrout. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_add: componentwise addition of 3 Fp2 elements               *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_add : function_t :=
    (AbstractField.add (F:=Fp6), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocy;
      (* Copy inputs to stack-allocated temporaries *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocy"; expr.var "iny"]);
      (* out.c0 = x.c0 + y.c0 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "allocx"); expr_fp6_c0 (expr.var "allocy")]);
      (* out.c1 = x.c1 + y.c1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocy")]);
      (* out.c2 = x.c2 + y.c2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocy")])
    ))).

  Instance spec_of_Fp6_add : spec_of (AbstractField.add (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=Fp6).

  Lemma Fp6_add_ok : program_logic_goal_for_function! Fp6_add.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2 HFadd1 HFadd2 HFadd3.
    unfold spec_of_Fp6_add, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_add].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Stackalloc allocy === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    (* FElem_from_bytes *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    (* Decompose memory *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m2) as [Hd_xrx_sY Hd_sX_sY].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_x_sY Hd_rx_sY].
    (* For copy spec, relate the two preconditions *)
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    (* === First Fp6 copy call: x → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    { subst l0 l.
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 allocx px allocx_val x
        (fun m => (Rx ⋆ AbstractField.FElem (F:=Fp6) allocy allocy_val) m)
        (eq (map.putmany (map.putmany m_x m_rx) mStackY))
        tr).
      split.
      { (* Precondition 1: (FElem px x * FElem allocx allocx_val * R1) *)
        exists (map.putmany m_x mStackX), (map.putmany m_rx mStackY).
        split; [split |].
        { rewrite <- !map.putmany_assoc. f_equal.
          map_swap m_rx mStackX. reflexivity. }
        { map_disjoint_auto. }
        split.
        { exists m_x, mStackX.
          split; [split; [reflexivity | exact Hd_x_sX] |].
          split; [exact Hfx | exact Hallocx]. }
        { exists m_rx, mStackY.
          split; [split; [reflexivity | exact Hd_rx_sY] |].
          split; [exact Hrx | exact Hallocy]. } }
      { (* Precondition 2: (FElem allocx allocx_val * Rout1) *)
        exists mStackX, (map.putmany (map.putmany m_x m_rx) mStackY).
        split; [split |].
        { rewrite map.putmany_assoc.
          let D := fresh "D" in
          assert (D : map.disjoint (map.putmany m_x m_rx) mStackX) by map_disjoint_auto;
          rewrite (map.putmany_comm (map.putmany m_x m_rx) mStackX D); clear D.
          rewrite <- map.putmany_assoc. reflexivity. }
        { map_disjoint_auto. }
        split; [exact Hallocx | exact eq_refl]. } }
    (* Process first copy postcondition *)
    intros t' m' rets [Hrets [Htr Hsep_copy1]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp6 copy call: y → allocy === *)
    (* Decompose copy1 postcondition *)
    destruct Hsep_copy1 as [m_new1 [m_frame1 [[Heq_m' Hd_n1_f1] [Hfelem_allocx Hframe1]]]].
    subst m_frame1 m'.
    (* Decompose Hmemy *)
    destruct Hmemy as [m_y [m_ry [Hmemy_sp [Hfelem_y Hry]]]].
    destruct Hmemy_sp as [Heq_mem0_y Hd_yry].
    (* Derive disjointness facts *)
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_f1) as [Hd_n1_mem0 Hd_n1_sY].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_x Hd_n1_rx].
    rewrite Heq_mem0_y in Hd_n1_mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_y Hd_n1_ry].
    rewrite Heq_mem0_y in Hd_xrx_sY.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_y_sY Hd_ry_sY'].
    (* dexprs for second copy *)
    exists [allocy; py]. split.
    { subst l0 l.
      eexists. split. { apply map.get_put_same. }
      cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 allocy py allocy_val y
        (fun m => (AbstractField.FElem (F:=Fp6) allocx x ⋆ Ry) m)
        (eq (map.putmany m_new1 (map.putmany m_y m_ry)))
        tr).
      split.
      { (* Precondition 1: (FElem py y * FElem allocy allocy_val * R2) *)
        rewrite Heq_mem0_y.
        exists (map.putmany m_y mStackY), (map.putmany m_new1 m_ry).
        split; [split |].
        { transitivity (map.putmany m_new1 (map.putmany (map.putmany m_y mStackY) m_ry)).
          { f_equal. apply map.disjoint_putmany_commutes. exact Hd_ry_sY'. }
          transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y mStackY)) m_ry).
          { apply map.putmany_assoc. }
          transitivity (map.putmany (map.putmany m_new1 m_ry) (map.putmany m_y mStackY)).
          { apply map.disjoint_putmany_commutes.
            apply map.disjoint_putmany_l. split; [exact Hd_yry |].
            unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_ry_sY' k v2 v1 H2 H1). }
          apply map.putmany_comm.
          apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_n1_y | exact Hd_n1_sY]. }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_yry k v2 v1 H2 H1). }
            { exact Hd_ry_sY'. } } }
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_n1_y k v2 v1 H2 H1). }
            { exact Hd_yry. } }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_n1_sY k v2 v1 H2 H1). }
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_ry_sY' k v2 v1 H2 H1). } } }
        split.
        { exists m_y, mStackY.
          split; [split; [reflexivity | exact Hd_y_sY] |].
          split; [exact Hfelem_y | exact Hallocy]. }
        { exists m_new1, m_ry.
          split; [split; [reflexivity | exact Hd_n1_ry] |].
          split; [exact Hfelem_allocx | exact Hry]. } }
      { (* Precondition 2: (FElem allocy allocy_val * Rout2) *)
        rewrite Heq_mem0_y.
        exists mStackY, (map.putmany m_new1 (map.putmany m_y m_ry)).
        split; [split |].
        { transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y m_ry)) mStackY).
          { apply map.putmany_assoc. }
          apply map.putmany_comm.
          apply map.disjoint_putmany_l. split; [exact Hd_n1_sY | exact Hd_xrx_sY]. }
        { apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_n1_sY k v2 v1 H2 H1). }
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_xrx_sY k v2 v1 H2 H1). } }
        split; [exact Hallocy | exact eq_refl]. } }
    (* Process second copy postcondition *)
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 3: Three Fp2 add calls === *)
    (* Decompose copy2 postcondition *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    (* Split Fp6 FElems into 3 Fp2 components each *)
    pose proof (Fp6_raw_FElem_split allocx x m_new1 Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax12 [Hsp_ax [Hfe_ax0 Hax12]]]].
    destruct Hsp_ax as [Heq_new1_ax Hd_ax0_12].
    destruct Hax12 as [m_ax1 [m_ax2 [Hsp_ax12 [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax12 as [Heq_ax12 Hd_ax12].
    pose proof (Fp6_raw_FElem_split allocy y m_new2 Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay0 [m_ay12 [Hsp_ay [Hfe_ay0 Hay12]]]].
    destruct Hsp_ay as [Heq_new2_ay Hd_ay0_12].
    destruct Hay12 as [m_ay1 [m_ay2 [Hsp_ay12 [Hfe_ay1 Hfe_ay2]]]].
    destruct Hsp_ay12 as [Heq_ay12 Hd_ay12].
    (* Split output FElem *)
    pose proof (Fp6_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o12 [Hsp_out [Hfe_o0 Ho12]]]].
    destruct Hsp_out as [Heq_out_o Hd_o0_12].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_o12 as [Heq_o12 Hd_o12].
    (* Decompose bounded_by at Fp2 level *)
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx, Hby.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx, Hby.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    destruct Hby as [Hby0 [Hby1 Hby2]].
    (* Derive Heq_yr: m_y ++ m_ry = m_out ++ m_rr *)
    assert (Heq_yr : map.putmany m_y m_ry = map.putmany m_out m_rr)
      by (rewrite <- Heq_mem0_y; exact Heq_m0_out).
    (* Subst decomposed maps *)
    subst m_ax12 m_ay12 m_o12 m_out m_new1 m_new2.
    rewrite Heq_yr in Hd_n2_f2.
    rewrite Heq_yr in Hd_n1_mem0.
    subst m''.
    rewrite Heq_yr.
    (* Build 10-way sep fact *)
    assert (Hsep10 :
      ((FElem_Fp2 allocy (c0_felem y) ⋆
        (FElem_Fp2 (word.add allocy fp6_c1_offset) (c1_felem y) ⋆
         FElem_Fp2 (word.add allocy fp6_c2_offset) (c2_felem y))) ⋆
       ((FElem_Fp2 allocx (c0_felem x) ⋆
         (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
          FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x))) ⋆
        ((FElem_Fp2 pout (c0_felem old_out) ⋆
          (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem old_out) ⋆
           FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem old_out))) ⋆ Rr)))
      (map.putmany (map.putmany m_ay0 (map.putmany m_ay1 m_ay2))
        (map.putmany (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
          (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)))).
    { exists (map.putmany m_ay0 (map.putmany m_ay1 m_ay2)),
        (map.putmany (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
          (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)).
      split; [split; [reflexivity | exact Hd_n2_f2] |].
      split.
      { exists m_ay0, (map.putmany m_ay1 m_ay2).
        split; [split; [reflexivity | exact Hd_ay0_12] |].
        split; [exact Hfe_ay0 |].
        exists m_ay1, m_ay2.
        split; [split; [reflexivity | exact Hd_ay12] |].
        split; [exact Hfe_ay1 | exact Hfe_ay2]. }
      exists (map.putmany m_ax0 (map.putmany m_ax1 m_ax2)),
        (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr).
      split; [split; [reflexivity | exact Hd_n1_mem0] |].
      split.
      { exists m_ax0, (map.putmany m_ax1 m_ax2).
        split; [split; [reflexivity | exact Hd_ax0_12] |].
        split; [exact Hfe_ax0 |].
        exists m_ax1, m_ax2.
        split; [split; [reflexivity | exact Hd_ax12] |].
        split; [exact Hfe_ax1 | exact Hfe_ax2]. }
      exists (map.putmany m_o0 (map.putmany m_o1 m_o2)), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o0, (map.putmany m_o1 m_o2).
        split; [split; [reflexivity | exact Hd_o0_12] |].
        split; [exact Hfe_o0 |].
        exists m_o1, m_o2.
        split; [split; [reflexivity | exact Hd_o12] |].
        split; [exact Hfe_o1 | exact Hfe_o2]. }
      exact Hrr_out. }
    (* === Phase 4: First Fp2 add call: add(out.c0, allocx.c0, allocy.c0) === *)
    exists [pout; allocx; allocy]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 pout allocx allocy
           (c0_felem old_out) (c0_felem x) (c0_felem y)
           _ tr).
         split; [exact Hbx0 |].
         split; [exact Hby0 |].
         split.
         { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         pose proof Hsep10 as H'. ecancel_assumption. }
    (* Process first Fp2 add postcondition *)
    intros t_add1 m_add1 rets_add1 [Hrets_add1 [Htr_add1 [out0' [Hfeval0 [Hbound0 Hsep_add1]]]]].
    subst rets_add1 t_add1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 4: Second Fp2 add call: add(out.c1, allocx.c1, allocy.c1) === *)
    exists [word.add pout fp6_c1_offset; word.add allocx fp6_c1_offset;
            word.add allocy fp6_c1_offset].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map expr_fp6_c1 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 (word.add pout fp6_c1_offset)
           (word.add allocx fp6_c1_offset) (word.add allocy fp6_c1_offset)
           (c1_felem old_out) (c1_felem x) (c1_felem y)
           _ tr).
         split; [exact Hbx1 |].
         split; [exact Hby1 |].
         split.
         { eexists. pose proof Hsep_add1 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep_add1 as H'. ecancel_assumption. }
         pose proof Hsep_add1 as H'. ecancel_assumption. }
    (* Process second Fp2 add postcondition *)
    intros t_add2 m_add2 rets_add2 [Hrets_add2 [Htr_add2 [out1' [Hfeval1 [Hbound1 Hsep_add2]]]]].
    subst rets_add2 t_add2.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 4: Third Fp2 add call: add(out.c2, allocx.c2, allocy.c2) === *)
    exists [word.add pout fp6_c2_offset; word.add allocx fp6_c2_offset;
            word.add allocy fp6_c2_offset].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map expr_fp6_c2 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd3 (word.add pout fp6_c2_offset)
           (word.add allocx fp6_c2_offset) (word.add allocy fp6_c2_offset)
           (c2_felem old_out) (c2_felem x) (c2_felem y)
           _ tr).
         split; [exact Hbx2 |].
         split; [exact Hby2 |].
         split.
         { eexists. pose proof Hsep_add2 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep_add2 as H'. ecancel_assumption. }
         pose proof Hsep_add2 as H'. ecancel_assumption. }
    (* Process third Fp2 add postcondition *)
    intros t_add3 m_add3 rets_add3 [Hrets_add3 [Htr_add3 [out2' [Hfeval2 [Hbound2 Hsep_add3]]]]].
    subst rets_add3 t_add3.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 5: Destructure Hsep_add3 into 10 map components === *)
    destruct Hsep_add3 as [m_A [m_rest1 [[Heq_add3 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_FF [m_rest6 [[Heq_r5 Hd_FF] [HFF Hrest6]]]].
    destruct Hrest6 as [m_G [m_rest7 [[Heq_r6 Hd_G] [HG Hrest7]]]].
    destruct Hrest7 as [m_HH [m_rest8 [[Heq_r7 Hd_HH] [HHH Hrest8]]]].
    destruct Hrest8 as [m_I [m_J [[Heq_r8 Hd_IJ] [HI HJ]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_rest6 m_rest7 m_rest8 m_add3.
    (* Derive pairwise disjointness *)
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hd" in let H2 := fresh "Hd" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    end.
    (* Get FElem lengths *)
    pose proof (Fp2_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp2_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp2_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp2_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp2_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp2_FElem_length _ _ _ HFF) as Hlen_FF.
    pose proof (Fp2_FElem_length _ _ _ HG) as Hlen_G.
    pose proof (Fp2_FElem_length _ _ _ HHH) as Hlen_HH.
    pose proof (Fp2_FElem_length _ _ _ HI) as Hlen_I.
    (* === Phase 6: Allocy stack deallocation === *)
    assert (Hjoin_y : (FElem_Fp2 allocy (c0_felem y) ⋆
      (FElem_Fp2 (word.add allocy fp6_c1_offset) (c1_felem y) ⋆
       FElem_Fp2 (word.add allocy fp6_c2_offset) (c2_felem y)))
      (map.putmany m_D (map.putmany m_E m_FF))).
    { exists m_D, (map.putmany m_E m_FF).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HD |].
      exists m_E, m_FF.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HE | exact HFF]. }
    pose proof (Fp6_raw_FElem_join allocy (c0_felem y) (c1_felem y) (c2_felem y)
      (map.putmany m_D (map.putmany m_E m_FF))
      Hlen_D Hlen_E Hlen_FF Hjoin_y) as Hfp6_y.
    rewrite Fp6_list_decomp in Hfp6_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocy y
      (map.putmany m_D (map.putmany m_E m_FF)) Hfp6_y) as Hanybytes_y.
    unfold AbstractField.Placeholder in Hanybytes_y.
    (* Provide witnesses for allocy deallocation *)
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C
      (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))))),
      (map.putmany m_D (map.putmany m_E m_FF)).
    split. { exact Hanybytes_y. }
    split. { split.
      { (* Equality: rearrange putmany to move D, E, FF to the end *)
        rewrite (map.putmany_assoc m_E m_FF
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        rewrite (map.putmany_assoc m_D (map.putmany m_E m_FF)
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        rewrite (map.putmany_comm (map.putmany m_D (map.putmany m_E m_FF))
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_C _ _).
        rewrite (map.putmany_assoc m_B _ _).
        rewrite (map.putmany_assoc m_A _ _).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Phase 7: Allocx stack deallocation === *)
    assert (Hjoin_x : (FElem_Fp2 allocx (c0_felem x) ⋆
      (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
       FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x)))
      (map.putmany m_G (map.putmany m_HH m_I))).
    { exists m_G, (map.putmany m_HH m_I).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HG |].
      exists m_HH, m_I.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HHH | exact HI]. }
    pose proof (Fp6_raw_FElem_join allocx (c0_felem x) (c1_felem x) (c2_felem x)
      (map.putmany m_G (map.putmany m_HH m_I))
      Hlen_G Hlen_HH Hlen_I Hjoin_x) as Hfp6_x.
    rewrite Fp6_list_decomp in Hfp6_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocx x
      (map.putmany m_G (map.putmany m_HH m_I)) Hfp6_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    (* Provide witnesses for allocx deallocation *)
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C m_J))),
      (map.putmany m_G (map.putmany m_HH m_I)).
    split. { exact Hanybytes_x. }
    split. { split.
      { (* Equality: rearrange putmany to move G, HH, I to the end *)
        rewrite (map.putmany_assoc m_HH m_I m_J).
        rewrite (map.putmany_assoc m_G (map.putmany m_HH m_I) m_J).
        rewrite (map.putmany_comm (map.putmany m_G (map.putmany m_HH m_I)) m_J).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_C _ _).
        rewrite (map.putmany_assoc m_B _ _).
        rewrite (map.putmany_assoc m_A _ _).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Phase 8: Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1' ++ out2').
    (* Prove c0/c1/c2 decomposition of output *)
    assert (Hc0_app : c0_felem (out0' ++ out1' ++ out2') = out0').
    { unfold c0_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (out0' ++ out1' ++ out2') = out1').
    { unfold c1_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (out0' ++ out1' ++ out2') = out2').
    { unfold c2_felem.
      set (n := (2 * fp_felem_size)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    (* feval *)
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    (* bounded_by *)
    split.
    { change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem)).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      split; [|split]; [exact Hbound0 | exact Hbound1 | exact Hbound2]. }
    (* sep *)
    { assert (Hjoin_out : (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout fp6_c1_offset) out1' ⋆
         FElem_Fp2 (word.add pout fp6_c2_offset) out2'))
        (map.putmany m_C (map.putmany m_B m_A))).
      { exists m_C, (map.putmany m_B m_A).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC |].
        exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp6_raw_FElem_join pout out0' out1' out2'
        (map.putmany m_C (map.putmany m_B m_A))
        Hlen_C Hlen_B Hlen_A Hjoin_out) as Hfp6_out.
      exists (map.putmany m_C (map.putmany m_B m_A)), m_J.
      split; [split |].
      { rewrite (map.putmany_assoc m_B m_C m_J).
        rewrite (map.putmany_assoc m_A (map.putmany m_B m_C) m_J).
        f_equal.
        rewrite (map.putmany_assoc m_A m_B m_C).
        rewrite (map.putmany_comm m_A m_B). 2: { exact Hd33. }
        apply map.putmany_comm. map_disjoint_auto. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out | exact HJ]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_sub: componentwise subtraction of 3 Fp2 elements            *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_sub : function_t :=
    (AbstractField.sub (F:=Fp6), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocy;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocy"; expr.var "iny"]);
      (* out.c0 = x.c0 - y.c0 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "allocx"); expr_fp6_c0 (expr.var "allocy")]);
      (* out.c1 = x.c1 - y.c1 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocy")]);
      (* out.c2 = x.c2 - y.c2 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocy")])
    ))).

  Instance spec_of_Fp6_sub : spec_of (AbstractField.sub (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=Fp6).

  Lemma Fp6_sub_ok : program_logic_goal_for_function! Fp6_sub.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2 HFsub1 HFsub2 HFsub3.
    unfold spec_of_Fp6_sub, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_sub].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Stackalloc allocy === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    (* FElem_from_bytes *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    (* Decompose memory *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m2) as [Hd_xrx_sY Hd_sX_sY].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_x_sY Hd_rx_sY].
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp6_fp_inst Fp6_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    (* === First Fp6 copy call: x → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    { subst l0 l.
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 allocx px allocx_val x
        (fun m => (Rx ⋆ AbstractField.FElem (F:=Fp6) allocy allocy_val) m)
        (eq (map.putmany (map.putmany m_x m_rx) mStackY))
        tr).
      split.
      { exists (map.putmany m_x mStackX), (map.putmany m_rx mStackY).
        split; [split |].
        { rewrite <- !map.putmany_assoc. f_equal.
          map_swap m_rx mStackX. reflexivity. }
        { map_disjoint_auto. }
        split.
        { exists m_x, mStackX.
          split; [split; [reflexivity | exact Hd_x_sX] |].
          split; [exact Hfx | exact Hallocx]. }
        { exists m_rx, mStackY.
          split; [split; [reflexivity | exact Hd_rx_sY] |].
          split; [exact Hrx | exact Hallocy]. } }
      { exists mStackX, (map.putmany (map.putmany m_x m_rx) mStackY).
        split; [split |].
        { rewrite map.putmany_assoc.
          let D := fresh "D" in
          assert (D : map.disjoint (map.putmany m_x m_rx) mStackX) by map_disjoint_auto;
          rewrite (map.putmany_comm (map.putmany m_x m_rx) mStackX D); clear D.
          rewrite <- map.putmany_assoc. reflexivity. }
        { map_disjoint_auto. }
        split; [exact Hallocx | exact eq_refl]. } }
    intros t' m' rets [Hrets [Htr Hsep_copy1]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp6 copy call: y → allocy === *)
    destruct Hsep_copy1 as [m_new1 [m_frame1 [[Heq_m' Hd_n1_f1] [Hfelem_allocx Hframe1]]]].
    subst m_frame1 m'.
    destruct Hmemy as [m_y [m_ry [Hmemy_sp [Hfelem_y Hry]]]].
    destruct Hmemy_sp as [Heq_mem0_y Hd_yry].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_f1) as [Hd_n1_mem0 Hd_n1_sY].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_x Hd_n1_rx].
    rewrite Heq_mem0_y in Hd_n1_mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_y Hd_n1_ry].
    rewrite Heq_mem0_y in Hd_xrx_sY.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_y_sY Hd_ry_sY'].
    exists [allocy; py]. split.
    { subst l0 l.
      eexists. split. { apply map.get_put_same. }
      cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { repeat (rewrite map.get_put_diff by (cbv; congruence)).
        apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 allocy py allocy_val y
        (fun m => (AbstractField.FElem (F:=Fp6) allocx x ⋆ Ry) m)
        (eq (map.putmany m_new1 (map.putmany m_y m_ry)))
        tr).
      split.
      { rewrite Heq_mem0_y.
        exists (map.putmany m_y mStackY), (map.putmany m_new1 m_ry).
        split; [split |].
        { transitivity (map.putmany m_new1 (map.putmany (map.putmany m_y mStackY) m_ry)).
          { f_equal. apply map.disjoint_putmany_commutes. exact Hd_ry_sY'. }
          transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y mStackY)) m_ry).
          { apply map.putmany_assoc. }
          transitivity (map.putmany (map.putmany m_new1 m_ry) (map.putmany m_y mStackY)).
          { apply map.disjoint_putmany_commutes.
            apply map.disjoint_putmany_l. split; [exact Hd_yry |].
            unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_ry_sY' k v2 v1 H2 H1). }
          apply map.putmany_comm.
          apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_n1_y | exact Hd_n1_sY]. }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_yry k v2 v1 H2 H1). }
            { exact Hd_ry_sY'. } } }
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_n1_y k v2 v1 H2 H1). }
            { exact Hd_yry. } }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_n1_sY k v2 v1 H2 H1). }
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_ry_sY' k v2 v1 H2 H1). } } }
        split.
        { exists m_y, mStackY.
          split; [split; [reflexivity | exact Hd_y_sY] |].
          split; [exact Hfelem_y | exact Hallocy]. }
        { exists m_new1, m_ry.
          split; [split; [reflexivity | exact Hd_n1_ry] |].
          split; [exact Hfelem_allocx | exact Hry]. } }
      { rewrite Heq_mem0_y.
        exists mStackY, (map.putmany m_new1 (map.putmany m_y m_ry)).
        split; [split |].
        { transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y m_ry)) mStackY).
          { apply map.putmany_assoc. }
          apply map.putmany_comm.
          apply map.disjoint_putmany_l. split; [exact Hd_n1_sY | exact Hd_xrx_sY]. }
        { apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_n1_sY k v2 v1 H2 H1). }
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_xrx_sY k v2 v1 H2 H1). } }
        split; [exact Hallocy | exact eq_refl]. } }
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 3: Three Fp2 sub calls === *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    pose proof (Fp6_raw_FElem_split allocx x m_new1 Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax12 [Hsp_ax [Hfe_ax0 Hax12]]]].
    destruct Hsp_ax as [Heq_new1_ax Hd_ax0_12].
    destruct Hax12 as [m_ax1 [m_ax2 [Hsp_ax12 [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax12 as [Heq_ax12 Hd_ax12].
    pose proof (Fp6_raw_FElem_split allocy y m_new2 Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay0 [m_ay12 [Hsp_ay [Hfe_ay0 Hay12]]]].
    destruct Hsp_ay as [Heq_new2_ay Hd_ay0_12].
    destruct Hay12 as [m_ay1 [m_ay2 [Hsp_ay12 [Hfe_ay1 Hfe_ay2]]]].
    destruct Hsp_ay12 as [Heq_ay12 Hd_ay12].
    pose proof (Fp6_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o12 [Hsp_out [Hfe_o0 Ho12]]]].
    destruct Hsp_out as [Heq_out_o Hd_o0_12].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_o12 as [Heq_o12 Hd_o12].
    cbv [bounded_by Fp6_field_representation Fp6_repr_inst] in Hbx, Hby.
    fold (@AbstractField.bounded_by _ _ _ _ _ _ F_representation) in Hbx, Hby.
    destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    destruct Hby as [Hby0 [Hby1 Hby2]].
    assert (Heq_yr : map.putmany m_y m_ry = map.putmany m_out m_rr)
      by (rewrite <- Heq_mem0_y; exact Heq_m0_out).
    subst m_ax12 m_ay12 m_o12 m_out m_new1 m_new2.
    rewrite Heq_yr in Hd_n2_f2.
    rewrite Heq_yr in Hd_n1_mem0.
    subst m''.
    rewrite Heq_yr.
    (* Build 10-way sep fact *)
    assert (Hsep10 :
      ((FElem_Fp2 allocy (c0_felem y) ⋆
        (FElem_Fp2 (word.add allocy fp6_c1_offset) (c1_felem y) ⋆
         FElem_Fp2 (word.add allocy fp6_c2_offset) (c2_felem y))) ⋆
       ((FElem_Fp2 allocx (c0_felem x) ⋆
         (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
          FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x))) ⋆
        ((FElem_Fp2 pout (c0_felem old_out) ⋆
          (FElem_Fp2 (word.add pout fp6_c1_offset) (c1_felem old_out) ⋆
           FElem_Fp2 (word.add pout fp6_c2_offset) (c2_felem old_out))) ⋆ Rr)))
      (map.putmany (map.putmany m_ay0 (map.putmany m_ay1 m_ay2))
        (map.putmany (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
          (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)))).
    { exists (map.putmany m_ay0 (map.putmany m_ay1 m_ay2)),
        (map.putmany (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
          (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr)).
      split; [split; [reflexivity | exact Hd_n2_f2] |].
      split.
      { exists m_ay0, (map.putmany m_ay1 m_ay2).
        split; [split; [reflexivity | exact Hd_ay0_12] |].
        split; [exact Hfe_ay0 |].
        exists m_ay1, m_ay2.
        split; [split; [reflexivity | exact Hd_ay12] |].
        split; [exact Hfe_ay1 | exact Hfe_ay2]. }
      exists (map.putmany m_ax0 (map.putmany m_ax1 m_ax2)),
        (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr).
      split; [split; [reflexivity | exact Hd_n1_mem0] |].
      split.
      { exists m_ax0, (map.putmany m_ax1 m_ax2).
        split; [split; [reflexivity | exact Hd_ax0_12] |].
        split; [exact Hfe_ax0 |].
        exists m_ax1, m_ax2.
        split; [split; [reflexivity | exact Hd_ax12] |].
        split; [exact Hfe_ax1 | exact Hfe_ax2]. }
      exists (map.putmany m_o0 (map.putmany m_o1 m_o2)), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o0, (map.putmany m_o1 m_o2).
        split; [split; [reflexivity | exact Hd_o0_12] |].
        split; [exact Hfe_o0 |].
        exists m_o1, m_o2.
        split; [split; [reflexivity | exact Hd_o12] |].
        split; [exact Hfe_o1 | exact Hfe_o2]. }
      exact Hrr_out. }
    (* === First Fp2 sub call === *)
    exists [pout; allocx; allocy]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 pout allocx allocy
           (c0_felem old_out) (c0_felem x) (c0_felem y)
           _ tr).
         split; [exact Hbx0 |].
         split; [exact Hby0 |].
         split.
         { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep10 as H'. ecancel_assumption. }
         pose proof Hsep10 as H'. ecancel_assumption. }
    intros t_sub1 m_sub1 rets_sub1 [Hrets_sub1 [Htr_sub1 [out0' [Hfeval0 [Hbound0 Hsep_sub1]]]]].
    subst rets_sub1 t_sub1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp2 sub call === *)
    exists [word.add pout fp6_c1_offset; word.add allocx fp6_c1_offset;
            word.add allocy fp6_c1_offset].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map expr_fp6_c1 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub2 (word.add pout fp6_c1_offset)
           (word.add allocx fp6_c1_offset) (word.add allocy fp6_c1_offset)
           (c1_felem old_out) (c1_felem x) (c1_felem y)
           _ tr).
         split; [exact Hbx1 |].
         split; [exact Hby1 |].
         split.
         { eexists. pose proof Hsep_sub1 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep_sub1 as H'. ecancel_assumption. }
         pose proof Hsep_sub1 as H'. ecancel_assumption. }
    intros t_sub2 m_sub2 rets_sub2 [Hrets_sub2 [Htr_sub2 [out1' [Hfeval1 [Hbound1 Hsep_sub2]]]]].
    subst rets_sub2 t_sub2.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Third Fp2 sub call === *)
    exists [word.add pout fp6_c2_offset; word.add allocx fp6_c2_offset;
            word.add allocy fp6_c2_offset].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map expr_fp6_c2 WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub3 (word.add pout fp6_c2_offset)
           (word.add allocx fp6_c2_offset) (word.add allocy fp6_c2_offset)
           (c2_felem old_out) (c2_felem x) (c2_felem y)
           _ tr).
         split; [exact Hbx2 |].
         split; [exact Hby2 |].
         split.
         { eexists. pose proof Hsep_sub2 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep_sub2 as H'. ecancel_assumption. }
         pose proof Hsep_sub2 as H'. ecancel_assumption. }
    intros t_sub3 m_sub3 rets_sub3 [Hrets_sub3 [Htr_sub3 [out2' [Hfeval2 [Hbound2 Hsep_sub3]]]]].
    subst rets_sub3 t_sub3.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 5: Destructure sep into 10 map components === *)
    destruct Hsep_sub3 as [m_A [m_rest1 [[Heq_sub3 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_FF [m_rest6 [[Heq_r5 Hd_FF] [HFF Hrest6]]]].
    destruct Hrest6 as [m_G [m_rest7 [[Heq_r6 Hd_G] [HG Hrest7]]]].
    destruct Hrest7 as [m_HH [m_rest8 [[Heq_r7 Hd_HH] [HHH Hrest8]]]].
    destruct Hrest8 as [m_I [m_J [[Heq_r8 Hd_IJ] [HI HJ]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_rest6 m_rest7 m_rest8 m_sub3.
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hd" in let H2 := fresh "Hd" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    end.
    pose proof (Fp2_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp2_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp2_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp2_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp2_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp2_FElem_length _ _ _ HFF) as Hlen_FF.
    pose proof (Fp2_FElem_length _ _ _ HG) as Hlen_G.
    pose proof (Fp2_FElem_length _ _ _ HHH) as Hlen_HH.
    pose proof (Fp2_FElem_length _ _ _ HI) as Hlen_I.
    (* === Phase 6: Allocy stack deallocation === *)
    assert (Hjoin_y : (FElem_Fp2 allocy (c0_felem y) ⋆
      (FElem_Fp2 (word.add allocy fp6_c1_offset) (c1_felem y) ⋆
       FElem_Fp2 (word.add allocy fp6_c2_offset) (c2_felem y)))
      (map.putmany m_D (map.putmany m_E m_FF))).
    { exists m_D, (map.putmany m_E m_FF).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HD |].
      exists m_E, m_FF.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HE | exact HFF]. }
    pose proof (Fp6_raw_FElem_join allocy (c0_felem y) (c1_felem y) (c2_felem y)
      (map.putmany m_D (map.putmany m_E m_FF))
      Hlen_D Hlen_E Hlen_FF Hjoin_y) as Hfp6_y.
    rewrite Fp6_list_decomp in Hfp6_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocy y
      (map.putmany m_D (map.putmany m_E m_FF)) Hfp6_y) as Hanybytes_y.
    unfold AbstractField.Placeholder in Hanybytes_y.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C
      (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))))),
      (map.putmany m_D (map.putmany m_E m_FF)).
    split. { exact Hanybytes_y. }
    split. { split.
      { rewrite (map.putmany_assoc m_E m_FF
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        rewrite (map.putmany_assoc m_D (map.putmany m_E m_FF)
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        rewrite (map.putmany_comm (map.putmany m_D (map.putmany m_E m_FF))
          (map.putmany m_G (map.putmany m_HH (map.putmany m_I m_J)))).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_C _ _).
        rewrite (map.putmany_assoc m_B _ _).
        rewrite (map.putmany_assoc m_A _ _).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Phase 7: Allocx stack deallocation === *)
    assert (Hjoin_x : (FElem_Fp2 allocx (c0_felem x) ⋆
      (FElem_Fp2 (word.add allocx fp6_c1_offset) (c1_felem x) ⋆
       FElem_Fp2 (word.add allocx fp6_c2_offset) (c2_felem x)))
      (map.putmany m_G (map.putmany m_HH m_I))).
    { exists m_G, (map.putmany m_HH m_I).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HG |].
      exists m_HH, m_I.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HHH | exact HI]. }
    pose proof (Fp6_raw_FElem_join allocx (c0_felem x) (c1_felem x) (c2_felem x)
      (map.putmany m_G (map.putmany m_HH m_I))
      Hlen_G Hlen_HH Hlen_I Hjoin_x) as Hfp6_x.
    rewrite Fp6_list_decomp in Hfp6_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocx x
      (map.putmany m_G (map.putmany m_HH m_I)) Hfp6_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C m_J))),
      (map.putmany m_G (map.putmany m_HH m_I)).
    split. { exact Hanybytes_x. }
    split. { split.
      { rewrite (map.putmany_assoc m_HH m_I m_J).
        rewrite (map.putmany_assoc m_G (map.putmany m_HH m_I) m_J).
        rewrite (map.putmany_comm (map.putmany m_G (map.putmany m_HH m_I)) m_J).
        2: { map_disjoint_auto. }
        rewrite (map.putmany_assoc m_C _ _).
        rewrite (map.putmany_assoc m_B _ _).
        rewrite (map.putmany_assoc m_A _ _).
        reflexivity. }
      { map_disjoint_auto. } }
    (* === Phase 8: Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1' ++ out2').
    assert (Hc0_app : c0_felem (out0' ++ out1' ++ out2') = out0').
    { unfold c0_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (out0' ++ out1' ++ out2') = out1').
    { unfold c1_felem.
      set (n := (2 * fp_felem_size)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (out0' ++ out1' ++ out2') = out2').
    { unfold c2_felem.
      set (n := (2 * fp_felem_size)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length out1') by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    split.
    { change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                     @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                    @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws))).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    split.
    { change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                     /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem)).
      cbv beta. rewrite Hc0_app, Hc1_app, Hc2_app.
      split; [|split]; [exact Hbound0 | exact Hbound1 | exact Hbound2]. }
    { assert (Hjoin_out : (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout fp6_c1_offset) out1' ⋆
         FElem_Fp2 (word.add pout fp6_c2_offset) out2'))
        (map.putmany m_C (map.putmany m_B m_A))).
      { exists m_C, (map.putmany m_B m_A).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC |].
        exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp6_raw_FElem_join pout out0' out1' out2'
        (map.putmany m_C (map.putmany m_B m_A))
        Hlen_C Hlen_B Hlen_A Hjoin_out) as Hfp6_out.
      exists (map.putmany m_C (map.putmany m_B m_A)), m_J.
      split; [split |].
      { rewrite (map.putmany_assoc m_B m_C m_J).
        rewrite (map.putmany_assoc m_A (map.putmany m_B m_C) m_J).
        f_equal.
        rewrite (map.putmany_assoc m_A m_B m_C).
        rewrite (map.putmany_comm m_A m_B). 2: { exact Hd33. }
        apply map.putmany_comm. map_disjoint_auto. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out | exact HJ]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp6_neg: componentwise negation                                  *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_opp : function_t :=
    (AbstractField.opp (F:=Fp6), (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "x"]);
      (* out.c0 = -x.c0 *)
      coq:(cmd.call [] (AbstractField.opp (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr_fp6_c0 (expr.var "allocx")]);
      (* out.c1 = -x.c1 *)
      coq:(cmd.call [] (AbstractField.opp (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c1 (expr.var "allocx")]);
      (* out.c2 = -x.c2 *)
      coq:(cmd.call [] (AbstractField.opp (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c2 (expr.var "allocx")])
    ))).

  Instance spec_of_Fp6_opp : spec_of (AbstractField.opp (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=Fp6).

  Lemma Fp6_opp_ok : program_logic_goal_for_function! Fp6_opp.
  Proof. Admitted.

  (* -------------------------------------------------------------- *)
  (* fp6_mul: Karatsuba-like multiplication                           *)
  (*                                                                  *)
  (* a0b0 = a.c0 * b.c0                                              *)
  (* a1b1 = a.c1 * b.c1                                              *)
  (* a2b2 = a.c2 * b.c2                                              *)
  (* t0 = (a.c1 + a.c2)(b.c1 + b.c2) - a1b1 - a2b2                 *)
  (* out.c0 = a0b0 + xi * t0                                         *)
  (* t1 = (a.c0 + a.c1)(b.c0 + b.c1) - a0b0 - a1b1                 *)
  (* out.c1 = t1 + xi * a2b2                                         *)
  (* t2 = (a.c0 + a.c2)(b.c0 + b.c2) - a0b0 - a2b2                 *)
  (* out.c2 = t2 + a1b1                                              *)
  (*                                                                  *)
  (* Placeholder: uses cmd.skip                                       *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_mul : function_t :=
    (AbstractField.mul (F:=Fp6), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocy;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as a0b0;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as a1b1;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as a2b2;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as u;
      (* Copy inputs to stack *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocy"; expr.var "iny"]);
      (* a0b0 = a.c0 * b.c0 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "a0b0"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c0 (expr.var "allocy")]);
      (* a1b1 = a.c1 * b.c1 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "a1b1"; expr_fp6_c1 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocy")]);
      (* a2b2 = a.c2 * b.c2 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "a2b2"; expr_fp6_c2 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocy")]);
      (* --- c0 = a0b0 + xi * ((a1+a2)(b1+b2) - a1b1 - a2b2) --- *)
      (* t = a.c1 + a.c2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr_fp6_c1 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocx")]);
      (* u = b.c1 + b.c2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "u"; expr_fp6_c1 (expr.var "allocy"); expr_fp6_c2 (expr.var "allocy")]);
      (* t = t * u = (a1+a2)(b1+b2) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "u"]);
      (* t = t - a1b1 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a1b1"]);
      (* t = t - a2b2 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a2b2"]);
      (* t = xi * t *)
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t"; expr.var "t"]);
      (* out.c0 = a0b0 + xi*t0 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr.var "a0b0"; expr.var "t"]);
      (* --- c1 = (a0+a1)(b0+b1) - a0b0 - a1b1 + xi*(a2b2) --- *)
      (* t = a.c0 + a.c1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocx")]);
      (* u = b.c0 + b.c1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "u"; expr_fp6_c0 (expr.var "allocy"); expr_fp6_c1 (expr.var "allocy")]);
      (* t = t * u = (a0+a1)(b0+b1) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "u"]);
      (* t = t - a0b0 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a0b0"]);
      (* t = t - a1b1 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a1b1"]);
      (* u = xi * a2b2 *)
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "u"; expr.var "a2b2"]);
      (* out.c1 = t + xi*a2b2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr.var "t"; expr.var "u"]);
      (* --- c2 = (a0+a2)(b0+b2) - a0b0 - a2b2 + a1b1 --- *)
      (* t = a.c0 + a.c2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocx")]);
      (* u = b.c0 + b.c2 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "u"; expr_fp6_c0 (expr.var "allocy"); expr_fp6_c2 (expr.var "allocy")]);
      (* t = t * u = (a0+a2)(b0+b2) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "u"]);
      (* t = t - a0b0 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a0b0"]);
      (* t = t - a2b2 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "a2b2"]);
      (* out.c2 = t + a1b1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr.var "t"; expr.var "a1b1"])
    ))).

  Instance spec_of_Fp6_mul : spec_of (AbstractField.mul (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=Fp6).

  Lemma Fp6_mul_ok : program_logic_goal_for_function! Fp6_mul.
  Proof. Admitted.

  (* -------------------------------------------------------------- *)
  (* fp6_sqr: Chung-Hasan SQR3 squaring                              *)
  (*                                                                  *)
  (* s0 = a.c0^2                                                      *)
  (* s1 = 2 * a.c0 * a.c1                                            *)
  (* s2 = (a.c0 - a.c1 + a.c2)^2                                    *)
  (* s3 = 2 * a.c1 * a.c2                                            *)
  (* s4 = a.c2^2                                                      *)
  (* out.c0 = s0 + xi * s3                                           *)
  (* out.c1 = s1 + xi * s4                                           *)
  (* out.c2 = s1 + s2 + s3 - s0 - s4                                *)
  (*                                                                  *)
  (* Placeholder: uses cmd.skip                                       *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_sqr : function_t :=
    (AbstractField.square (F:=Fp6), (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s0;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s1;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s2;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s3;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as s4;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t;
      (* Copy input to stack *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "x"]);
      (* s0 = a0^2 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "s0"; expr_fp6_c0 (expr.var "allocx")]);
      (* t = a0*a1; s1 = t + t = 2*a0*a1 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "s1"; expr.var "t"; expr.var "t"]);
      (* s2 = (a0 - a1 + a2)^2 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr.var "t"; expr_fp6_c2 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "s2"; expr.var "t"]);
      (* t = a1*a2; s3 = t + t = 2*a1*a2 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t"; expr_fp6_c1 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "s3"; expr.var "t"; expr.var "t"]);
      (* s4 = a2^2 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "s4"; expr_fp6_c2 (expr.var "allocx")]);
      (* out.c0 = s0 + xi*s3 *)
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t"; expr.var "s3"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr.var "s0"; expr.var "t"]);
      (* out.c1 = s1 + xi*s4 *)
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t"; expr.var "s4"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr.var "s1"; expr.var "t"]);
      (* out.c2 = s1 + s2 + s3 - s0 - s4 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr.var "s1"; expr.var "s2"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "s3"]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "t"; expr.var "t"; expr.var "s0"]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr.var "t"; expr.var "s4"])
    ))).

  Instance spec_of_Fp6_sqr : spec_of (AbstractField.square (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_square (F:=Fp6).

  Lemma Fp6_sqr_ok : program_logic_goal_for_function! Fp6_sqr.
  Proof. Admitted.

  (* -------------------------------------------------------------- *)
  (* fp6_inv: cubic extension inverse                                 *)
  (*                                                                  *)
  (* A = a0^2 - xi*(a1*a2)                                           *)
  (* B = xi*(a2^2) - a0*a1                                           *)
  (* C = a1^2 - a0*a2                                                *)
  (* F = a0*A + xi*(a2*B + a1*C)                                     *)
  (* out = (A/F, B/F, C/F)                                           *)
  (*                                                                  *)
  (* Placeholder: uses cmd.skip                                       *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_inv : function_t :=
    (AbstractField.inv (F:=Fp6), (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as vA;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as vB;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as vC;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t1;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t2;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t3;
      (* Copy input to stack *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "allocx"; expr.var "x"]);
      (* A = a0^2 - xi*(a1*a2) *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "t1"; expr_fp6_c0 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t2"; expr_fp6_c1 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocx")]);
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t3"; expr.var "t2"]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "vA"; expr.var "t1"; expr.var "t3"]);
      (* B = xi*(a2^2) - a0*a1 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "t1"; expr_fp6_c2 (expr.var "allocx")]);
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t3"; expr.var "t1"]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t2"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c1 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "vB"; expr.var "t3"; expr.var "t2"]);
      (* C = a1^2 - a0*a2 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp2)) [expr.var "t1"; expr_fp6_c1 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t2"; expr_fp6_c0 (expr.var "allocx"); expr_fp6_c2 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp2)) [expr.var "vC"; expr.var "t1"; expr.var "t2"]);
      (* FF = a0*A + xi*(a2*B + a1*C) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t1"; expr_fp6_c0 (expr.var "allocx"); expr.var "vA"]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t2"; expr_fp6_c2 (expr.var "allocx"); expr.var "vB"]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr.var "t3"; expr_fp6_c1 (expr.var "allocx"); expr.var "vC"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t2"; expr.var "t2"; expr.var "t3"]);
      coq:(cmd.call [] fp2_mul_xi_name [expr.var "t2"; expr.var "t2"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp2)) [expr.var "t1"; expr.var "t1"; expr.var "t2"]);
      (* t1 = FF^{-1} *)
      coq:(cmd.call [] (AbstractField.inv (F:=Fp2)) [expr.var "t1"; expr.var "t1"]);
      (* out = (A/F, B/F, C/F) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c0 (expr.var "out"); expr.var "vA"; expr.var "t1"]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr.var "vB"; expr.var "t1"]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr.var "vC"; expr.var "t1"])
    ))).

  Instance spec_of_Fp6_inv : spec_of (AbstractField.inv (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_inv (F:=Fp6).

  Lemma Fp6_inv_ok : program_logic_goal_for_function! Fp6_inv.
  Proof. Admitted.

  (* -------------------------------------------------------------- *)
  (* Collected function list for downstream linking                    *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_funcs : list function_t :=
    [ Fp2_mul_xi;
      Fp6_felem_copy;
      Fp6_add;
      Fp6_sub;
      Fp6_opp;
      Fp6_mul;
      Fp6_sqr;
      Fp6_inv ].

End Fp6.
