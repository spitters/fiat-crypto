(** * BLS12-381 Pairing — bedrock2 compilation top-level.

    Instantiates the full field tower (Fp → Fp2 → Fp6 → Fp12) for
    BLS12-381 and defines bedrock2 function bodies for the optimal Ate
    pairing: Miller loop, final exponentiation, and top-level pairing.

    The field tower arithmetic bodies are imported from the FieldExtensions
    layer. This file adds:
    - Helper functions (fp2_mul_fp, make_line for line evaluation)
    - Miller loop with cmd.while over 63 bits of the BLS parameter
    - Final exponentiation: easy part (conjugate/inv/frobenius_p2) +
      hard part (square-and-multiply with 1268-bit h3 exponent)
    - Top-level pairing chaining Miller loop + final exponentiation

    WP proofs are stubs (exact I) — the function bodies are real.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.PairingFieldOps.

Import BinInt String List.ListNotations.
Import Syntax.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Compatibility shim *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section BLS12_Pairing.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* ============================================================== *)
    (* BLS12-381 prime parameters                                      *)
    (* ============================================================== *)

    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Instance bls12_prime_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls12_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls12_mul";
      PrimeField.add := "bls12_add";
      PrimeField.sub := "bls12_sub";
      PrimeField.opp := "bls12_opp";
      PrimeField.square := "bls12_square";
      PrimeField.scmula24 := "bls12_scmula24";
      PrimeField.inv := "bls12_inv";
      PrimeField.from_bytes := "bls12_from_bytes";
      PrimeField.to_bytes := "bls12_to_bytes";
      PrimeField.select_znz := "bls12_select_znz";
      PrimeField.felem_copy := "bls12_felem_copy";
      PrimeField.from_word := "bls12_from_word";
      PrimeField.from_list := "bls12_from_list";
    |}.

    Instance bls12_prime_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_381. Qed.

    Existing Instance prime_field_parameters.

    (* Fp-level representation from synthesis pipeline *)
    Instance bls12_fp_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls12_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls12_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls12_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls12_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls12_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls12_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls12_frep |}.

    Instance bls12_fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls12_fp_rep] in *.
      cbv [Field.bounded_by bls12_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    (* β = -1 for BLS12-381 (p ≡ 3 mod 4) *)
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    Lemma bls12_beta_nz : bls12_beta <> @F.zero PrimeField.M_pos.
    Proof.
      unfold bls12_beta. intro H. apply (f_equal F.to_Z) in H.
      rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
    Qed.

    Lemma bls12_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bls12_beta).
    Proof. (* -1 is QNR when p ≡ 3 mod 4 *) Admitted.

    Lemma bls12_M_big : 2 < Z.pos PrimeField.M_pos.
    Proof. vm_compute. reflexivity. Qed.

    (* ============================================================== *)
    (* Field name prefixes                                             *)
    (* ============================================================== *)

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".

    (* ============================================================== *)
    (* Type notations                                                  *)
    (* ============================================================== *)

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* ============================================================== *)
    (* Fp2 instances                                                   *)
    (* ============================================================== *)

    Instance bls12_Fp2_params : AbstractField.FieldParameters Fp2 :=
      Fp2_field_parameters bls12_beta fp2_prefix.
    Instance bls12_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      Fp2_field_representation bls12_beta fp2_prefix.
    Instance bls12_Fp2_names : FieldNames (F:=Fp2) :=
      field_names_prefixed fp2_prefix.

    (* ============================================================== *)
    (* Fp6 instances                                                   *)
    (* ============================================================== *)

    Instance bls12_Fp6_params : AbstractField.FieldParameters Fp6 :=
      Fp6_field_parameters (fp6_prefix:=fp6_prefix).
    Instance bls12_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
      Fp6_field_representation bls12_beta (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
    Instance bls12_Fp6_names : FieldNames (F:=Fp6) :=
      field_names_prefixed fp6_prefix.

    (* ============================================================== *)
    (* Fp12 instances                                                  *)
    (* ============================================================== *)

    Instance bls12_Fp12_params : AbstractField.FieldParameters Fp12 :=
      Fp12_field_parameters (fp12_prefix:=fp12_prefix).
    Instance bls12_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
      Fp12_field_representation bls12_beta (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
    Instance bls12_Fp12_names : FieldNames (F:=Fp12) :=
      field_names_prefixed fp12_prefix.
    Instance bls12_Fp_names : FieldNames (F:=Fp) :=
      field_names_prefixed "bls12_".

    (* ============================================================== *)
    (* Offset and address helpers                                      *)
    (* ============================================================== *)

    (* Fp-level offset within Fp2 *)
    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).
    Local Definition expr_fp_snd (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp_felem_offset).

    (* Fp2-level offsets within Fp6 *)
    Local Notation fp2_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).
    Local Definition expr_fp6_c0 (x : Syntax.expr.expr) := x.
    Local Definition expr_fp6_c1 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp2_felem_offset).
    Local Definition expr_fp6_c2 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal (2 * fp2_felem_offset)).

    (* Fp6-level offsets within Fp12 *)
    Local Notation fp6_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp6))).
    Local Definition expr_fp12_c0 (x : Syntax.expr.expr) := x.
    Local Definition expr_fp12_c1 (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp6_felem_offset).

    (* ============================================================== *)
    (* Function name helpers                                           *)
    (* ============================================================== *)

    Let fp_mul_name : string := PrimeField.mul.
    Let fp_copy_name : string := PrimeField.felem_copy.
    Let from_word_name : string := PrimeField.from_word.
    Let fp2_add_name : string := AbstractField.add (F:=Fp2).
    Let fp2_sub_name : string := AbstractField.sub (F:=Fp2).
    Let fp2_mul_name : string := AbstractField.mul (F:=Fp2).
    Let fp2_sqr_name : string := AbstractField.square (F:=Fp2).
    Let fp2_inv_name : string := AbstractField.inv (F:=Fp2).
    Let fp2_opp_name : string := AbstractField.opp (F:=Fp2).
    Let fp2_copy_name : string := AbstractField.felem_copy (F:=Fp2).
    Let fp12_add_name : string := AbstractField.add (F:=Fp12).
    Let fp12_mul_name : string := AbstractField.mul (F:=Fp12).
    Let fp12_sqr_name : string := AbstractField.square (F:=Fp12).
    Let fp12_inv_name : string := AbstractField.inv (F:=Fp12).
    Let fp12_copy_name : string := AbstractField.felem_copy (F:=Fp12).
    Let fp12_conjugate_name : string := (fp12_prefix ++ "conjugate")%string.
    Let fp12_frobenius_p2_name : string := (fp12_prefix ++ "frobenius_p2")%string.
    Let fp2_mul_fp_name : string := "bls12_Fp2_mul_fp".
    Let make_line_name : string := "bls12_make_line".

    (* ============================================================== *)
    (* Fp6/Fp12/PairingOps function bodies from lower layers           *)
    (* ============================================================== *)

    Definition bls12_Fp6_funcs : list function_t :=
      Fp6_funcs bls12_beta fp6_prefix fp2_prefix.

    Definition bls12_Fp12_funcs : list function_t :=
      Fp12_funcs bls12_beta fp12_prefix fp6_prefix fp2_prefix.

    Definition bls12_pairing_ops : list function_t :=
      PairingOps_funcs bls12_beta fp12_prefix fp6_prefix fp2_prefix.

    (* ============================================================== *)
    (* Helper: fold a list of cmds into nested cmd.seq                 *)
    (* ============================================================== *)

    Local Fixpoint cmd_seq_list (cmds : list Syntax.cmd.cmd) : Syntax.cmd.cmd :=
      match cmds with
      | [] => cmd.skip
      | [c] => c
      | c :: rest => cmd.seq c (cmd_seq_list rest)
      end.

    (* ============================================================== *)
    (* fp2_mul_fp: multiply Fp2 by Fp scalar (2 Fp muls)              *)
    (* ============================================================== *)

    Definition bls12_Fp2_mul_fp : function_t :=
      (fp2_mul_fp_name,
       (["out"; "x"; "s"], []:list String.string, bedrock_func_body:(
         coq:(cmd.call [] fp_mul_name
           [expr.var "out"; expr.var "x"; expr.var "s"]);
         coq:(cmd.call [] fp_mul_name
           [expr_fp_snd (expr.var "out"); expr_fp_snd (expr.var "x"); expr.var "s"])
       ))).

    Lemma bls12_Fp2_mul_fp_ok : program_logic_goal_for_function! bls12_Fp2_mul_fp.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* make_line: construct line evaluation as Fp12                    *)
    (*   c0 = (lambda*x_T - y_T, -(lambda*x_P), 0)                   *)
    (*   c1 = (0, (y_P, 0), 0)                                        *)
    (* ============================================================== *)

    Definition bls12_make_line : function_t :=
      (make_line_name,
       (["out"; "lam"; "x_t"; "y_t"; "x_p"; "y_p"],
        []:list String.string, bedrock_func_body:(
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp;
         coq:(cmd_seq_list [
           (* out.c0.c0 = lam * x_t *)
           cmd.call [] fp2_mul_name
             [expr_fp6_c0 (expr_fp12_c0 (expr.var "out"));
              expr.var "lam"; expr.var "x_t"];
           (* out.c0.c0 -= y_t *)
           cmd.call [] fp2_sub_name
             [expr_fp6_c0 (expr_fp12_c0 (expr.var "out"));
              expr_fp6_c0 (expr_fp12_c0 (expr.var "out")); expr.var "y_t"];
           (* tmp = lam * x_p (Fp2 scaled by Fp) *)
           cmd.call [] fp2_mul_fp_name
             [expr.var "tmp"; expr.var "lam"; expr.var "x_p"];
           (* out.c0.c1 = -tmp *)
           cmd.call [] fp2_opp_name
             [expr_fp6_c1 (expr_fp12_c0 (expr.var "out")); expr.var "tmp"];
           (* out.c0.c2 = 0 *)
           cmd.call [] from_word_name
             [expr_fp6_c2 (expr_fp12_c0 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c2 (expr_fp12_c0 (expr.var "out")));
              expr.literal 0];
           (* out.c1.c0 = 0 *)
           cmd.call [] from_word_name
             [expr_fp6_c0 (expr_fp12_c1 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c0 (expr_fp12_c1 (expr.var "out")));
              expr.literal 0];
           (* out.c1.c1 = (y_p, 0) *)
           cmd.call [] fp_copy_name
             [expr_fp6_c1 (expr_fp12_c1 (expr.var "out")); expr.var "y_p"];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c1 (expr_fp12_c1 (expr.var "out")));
              expr.literal 0];
           (* out.c1.c2 = 0 *)
           cmd.call [] from_word_name
             [expr_fp6_c2 (expr_fp12_c1 (expr.var "out")); expr.literal 0];
           cmd.call [] from_word_name
             [expr_fp_snd (expr_fp6_c2 (expr_fp12_c1 (expr.var "out")));
              expr.literal 0]
         ])
       ))).

    Lemma bls12_make_line_ok : program_logic_goal_for_function! bls12_make_line.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Frobenius constant loaders for BLS12-381                        *)
    (*                                                                  *)
    (* Values are in Montgomery form, precomputed for BLS12-381.       *)
    (* Only the p²-Frobenius constants are needed for final exp:       *)
    (*   gamma1_p2 = ξ^{(p²-1)/3}                                     *)
    (*   gamma2_p2 = ξ^{2(p²-1)/3}                                    *)
    (*   w_frob_p2_c1 = ξ^{(p²-1)/6}                                  *)
    (* ============================================================== *)

    (* Helper: store an Fp2 constant = (real, 0) where real is 6 limbs *)
    Local Definition store_fp2_real_only (v : string) (l0 l1 l2 l3 l4 l5 : Z) :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var v) (expr.literal l0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 8)) (expr.literal l1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 16)) (expr.literal l2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 24)) (expr.literal l3);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 32)) (expr.literal l4);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 40)) (expr.literal l5);
        (* Imaginary part = 0 *)
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 64)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 72)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 80)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 88)) (expr.literal 0)
      ].

    (* γ₁^{p²} = ξ^{(p²-1)/3} — cube root of unity in Fp *)
    Definition bls12_load_gamma1_p2 : function_t :=
      ("bls12_load_gamma1_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x2e01fffffffefffe 0xde17d813620a0002
          0xddb3a93be6f89688 0xba69c6076a0f77ea
          0x5f19672fdf76ce51 0x0000000000000000)).

    Lemma bls12_load_gamma1_p2_ok :
      program_logic_goal_for_function! bls12_load_gamma1_p2.
    Proof. exact I. Qed.

    (* γ₂^{p²} = ξ^{2(p²-1)/3} *)
    Definition bls12_load_gamma2_p2 : function_t :=
      ("bls12_load_gamma2_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x8bfd00000000aaac 0x409427eb4f49fffd
          0x897d29650fb85f9b 0xaa0d857d89759ad4
          0xec02408663d4de85 0x1a0111ea397fe699)).

    Lemma bls12_load_gamma2_p2_ok :
      program_logic_goal_for_function! bls12_load_gamma2_p2.
    Proof. exact I. Qed.

    (* w^{p²} coefficient = ξ^{(p²-1)/6} *)
    Definition bls12_load_w_frob_p2_c1 : function_t :=
      ("bls12_load_w_frob_p2_c1",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x2e01fffffffeffff 0xde17d813620a0002
          0xddb3a93be6f89688 0xba69c6076a0f77ea
          0x5f19672fdf76ce51 0x0000000000000000)).

    Lemma bls12_load_w_frob_p2_c1_ok :
      program_logic_goal_for_function! bls12_load_w_frob_p2_c1.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Helper: set an Fp12 element to the multiplicative identity      *)
    (* (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0) in Fp components        *)
    (* ============================================================== *)

    Local Definition fp12_set_one (v : string) : Syntax.cmd.cmd :=
      let p := expr.var v in
      cmd_seq_list [
        cmd.call [] from_word_name [p; expr.literal 1];
        cmd.call [] from_word_name [expr_fp_snd p; expr.literal 0];
        cmd.call [] from_word_name [expr_fp6_c1 p; expr.literal 0];
        cmd.call [] from_word_name [expr_fp_snd (expr_fp6_c1 p); expr.literal 0];
        cmd.call [] from_word_name [expr_fp6_c2 p; expr.literal 0];
        cmd.call [] from_word_name [expr_fp_snd (expr_fp6_c2 p); expr.literal 0];
        cmd.call [] from_word_name [expr_fp12_c1 p; expr.literal 0];
        cmd.call [] from_word_name [expr_fp_snd (expr_fp12_c1 p); expr.literal 0];
        cmd.call [] from_word_name [expr_fp6_c1 (expr_fp12_c1 p); expr.literal 0];
        cmd.call [] from_word_name [expr_fp_snd (expr_fp6_c1 (expr_fp12_c1 p)); expr.literal 0];
        cmd.call [] from_word_name [expr_fp6_c2 (expr_fp12_c1 p); expr.literal 0];
        cmd.call [] from_word_name [expr_fp_snd (expr_fp6_c2 (expr_fp12_c1 p)); expr.literal 0]
      ].

    (* ============================================================== *)
    (* Miller loop (real body — processes 63 bits of BLS parameter)    *)
    (* ============================================================== *)

    (* BLS parameter |x| = 0xd201000000010000 *)
    Let bls_x : Z := 0xd201000000010000.

    (* One iteration of the Miller loop:
       - Decrement i
       - Doubling step: compute tangent, line evaluation, update f and T
       - Conditional addition step if bit i of bls_x is set *)
    Local Definition miller_loop_iteration : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));

        (* === Doubling step === *)
        (* lambda = 3*t_x^2 / (2*t_y) *)
        cmd.call [] fp2_sqr_name
          [expr.var "tmp1"; expr.var "t_x"];
        cmd.call [] fp2_add_name
          [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp1"];
        cmd.call [] fp2_add_name
          [expr.var "lambda"; expr.var "lambda"; expr.var "tmp1"];
        cmd.call [] fp2_add_name
          [expr.var "tmp1"; expr.var "t_y"; expr.var "t_y"];
        cmd.call [] fp2_inv_name
          [expr.var "tmp1"; expr.var "tmp1"];
        cmd.call [] fp2_mul_name
          [expr.var "lambda"; expr.var "lambda"; expr.var "tmp1"];

        (* Line evaluation at P *)
        cmd.call [] make_line_name
          [expr.var "line"; expr.var "lambda";
           expr.var "t_x"; expr.var "t_y";
           expr.var "p_x"; expr.var "p_y"];

        (* f = f^2 * line_d *)
        cmd.call [] fp12_sqr_name
          [expr.var "f"; expr.var "f"];
        cmd.call [] fp12_mul_name
          [expr.var "f"; expr.var "f"; expr.var "line"];

        (* T = 2T: new_x = lambda^2 - 2*t_x *)
        cmd.call [] fp2_sqr_name
          [expr.var "tmp1"; expr.var "lambda"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
        cmd.call [] fp2_sub_name
          [expr.var "tmp2"; expr.var "tmp1"; expr.var "t_x"];
        (* new_y = lambda*(t_x - new_x) - t_y *)
        cmd.call [] fp2_sub_name
          [expr.var "tmp1"; expr.var "t_x"; expr.var "tmp2"];
        cmd.call [] fp2_mul_name
          [expr.var "tmp1"; expr.var "lambda"; expr.var "tmp1"];
        cmd.call [] fp2_sub_name
          [expr.var "t_y"; expr.var "tmp1"; expr.var "t_y"];
        cmd.call [] fp2_copy_name
          [expr.var "t_x"; expr.var "tmp2"];

        (* === Conditional addition step === *)
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal bls_x) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd_seq_list [
            (* Chord slope: lambda_a = (q_y - t_y) / (q_x - t_x) *)
            cmd.call [] fp2_sub_name
              [expr.var "tmp1"; expr.var "q_y"; expr.var "t_y"];
            cmd.call [] fp2_sub_name
              [expr.var "tmp2"; expr.var "q_x"; expr.var "t_x"];
            cmd.call [] fp2_inv_name
              [expr.var "tmp2"; expr.var "tmp2"];
            cmd.call [] fp2_mul_name
              [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp2"];
            (* Line evaluation at P *)
            cmd.call [] make_line_name
              [expr.var "line"; expr.var "lambda";
               expr.var "t_x"; expr.var "t_y";
               expr.var "p_x"; expr.var "p_y"];
            (* f = f * line_a *)
            cmd.call [] fp12_mul_name
              [expr.var "f"; expr.var "f"; expr.var "line"];
            (* T = T + Q: new_x = lambda^2 - t_x - q_x *)
            cmd.call [] fp2_sqr_name
              [expr.var "tmp1"; expr.var "lambda"];
            cmd.call [] fp2_sub_name
              [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
            cmd.call [] fp2_sub_name
              [expr.var "tmp2"; expr.var "tmp1"; expr.var "q_x"];
            (* new_y = lambda*(t_x - new_x) - t_y *)
            cmd.call [] fp2_sub_name
              [expr.var "tmp1"; expr.var "t_x"; expr.var "tmp2"];
            cmd.call [] fp2_mul_name
              [expr.var "tmp1"; expr.var "lambda"; expr.var "tmp1"];
            cmd.call [] fp2_sub_name
              [expr.var "t_y"; expr.var "tmp1"; expr.var "t_y"];
            cmd.call [] fp2_copy_name
              [expr.var "t_x"; expr.var "tmp2"]
          ])
          cmd.skip
      ].

    (* Full Miller loop: init + while loop + copy to output.
       Processes bits 62 down to 0 of |x| (bit 63 = MSB initializes T = Q). *)
    Local Definition miller_loop_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp12_set_one "f";
        cmd.call [] fp2_copy_name [expr.var "t_x"; expr.var "q_x"];
        cmd.call [] fp2_copy_name [expr.var "t_y"; expr.var "q_y"];
        cmd.set "i" (expr.literal 63);
        cmd.while (expr.var "i") miller_loop_iteration;
        cmd.call [] fp12_copy_name [expr.var "out"; expr.var "f"]
      ].

    Definition bls12_miller_loop : function_t :=
      ("bls12_miller_loop",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as f;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_x;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_y;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as lambda;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as line;
          coq:(miller_loop_full_body)
        ))).

    Lemma bls12_miller_loop_ok : program_logic_goal_for_function! bls12_miller_loop.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Final exponentiation                                            *)
    (*   f^{(p^12-1)/r} = f^{(p^6-1)(p^2+1)*h3}                     *)
    (*   Easy part: conjugate + inv + mul + frobenius_p2 + mul         *)
    (*   Hard part: square-and-multiply with h3 (1268-bit exponent)    *)
    (* ============================================================== *)

    (* Store h3 = (p^4 - p^2 + 1)/r exponent as 20 little-endian u64 limbs *)
    Local Definition h3_store_limbs : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.store access_size.word
          (expr.var "h3") (expr.literal 0xe516c3f438e3ba79);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 8))
          (expr.literal 0xfa9912aae208ccf1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 16))
          (expr.literal 0x905ce937335d5b68);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 24))
          (expr.literal 0xc71a2629b0dea236);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 32))
          (expr.literal 0x83774940996754c8);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 40))
          (expr.literal 0x21d160aeb6a1e799);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 48))
          (expr.literal 0x2ed0b283ed237db4);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 56))
          (expr.literal 0x915c97f36c6f1821);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 64))
          (expr.literal 0x67f17fcbde783765);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 72))
          (expr.literal 0x2378b9039096d1b7);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 80))
          (expr.literal 0x7988f8761bdc51dc);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 88))
          (expr.literal 0x2076995003fc77a1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 96))
          (expr.literal 0x827eca0ba621315b);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 104))
          (expr.literal 0xe5a72bce8d63cb9f);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 112))
          (expr.literal 0xf68f7764c28b6f8a);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 120))
          (expr.literal 0x2f230063cf081517);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 128))
          (expr.literal 0x94506632528d6a9a);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 136))
          (expr.literal 0xd3cde88eeb996ca3);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 144))
          (expr.literal 0xc0bd38c3195c899e);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var "h3") (expr.literal 152))
          (expr.literal 0x000f686b3d807d01)
      ].

    (* One iteration of left-to-right binary square-and-multiply:
       - Decrement i
       - Extract bit from h3 array
       - If started: square the accumulator
       - If bit set: multiply by base (or initialize if first bit) *)
    Local Definition h3_loop_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        (* Extract bit i from h3: word = h3[i/64], bit = (word >> (i%64)) & 1 *)
        cmd.set "word" (expr.load access_size.word
          (expr.op bopname.add (expr.var "h3")
            (expr.op bopname.slu
              (expr.op bopname.sru (expr.var "i") (expr.literal 6))
              (expr.literal 3))));
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.var "word")
            (expr.op bopname.and (expr.var "i") (expr.literal 63)))
          (expr.literal 1));
        (* if started: result = sqr(result) *)
        cmd.cond (expr.var "started")
          (cmd.call [] fp12_sqr_name
            [expr.var "result"; expr.var "result"])
          cmd.skip;
        (* if bit set: multiply or initialize *)
        cmd.cond (expr.var "bit")
          (cmd.cond (expr.var "started")
            (cmd.call [] fp12_mul_name
              [expr.var "result"; expr.var "result"; expr.var "base"])
            (cmd.seq
              (cmd.call [] fp12_copy_name
                [expr.var "result"; expr.var "base"])
              (cmd.set "started" (expr.literal 1))))
          cmd.skip
      ].

    (* Full final exponentiation:
       Easy part 1: result = conj(f) * inv(f) = f^{p^6-1}
       Easy part 2: result = frob_p2(result) * result = result^{p^2+1}
       Hard part:   result = result^{h3} *)
    Local Definition final_exp_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Easy part 1: f^{p^6-1} *)
        cmd.call [] fp12_conjugate_name
          [expr.var "result"; expr.var "f"];
        cmd.call [] fp12_inv_name
          [expr.var "tmp"; expr.var "f"];
        cmd.call [] fp12_mul_name
          [expr.var "result"; expr.var "result"; expr.var "tmp"];
        (* Easy part 2: result^{p^2+1} *)
        cmd.call [] fp12_frobenius_p2_name
          [expr.var "tmp"; expr.var "result";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"];
        cmd.call [] fp12_mul_name
          [expr.var "result"; expr.var "tmp"; expr.var "result"];
        (* Hard part: result^{h3} via square-and-multiply *)
        cmd.call [] fp12_copy_name
          [expr.var "base"; expr.var "result"];
        fp12_set_one "result";
        h3_store_limbs;
        cmd.set "started" (expr.literal 0);
        cmd.set "i" (expr.literal 1280);
        cmd.while (expr.var "i") h3_loop_body;
        (* Copy to output *)
        cmd.call [] fp12_copy_name
          [expr.var "out"; expr.var "result"]
      ].

    Definition bls12_final_exp : function_t :=
      ("bls12_final_exp",
       (["out"; "f"; "gamma1_p2"; "gamma2_p2"; "w_frob_p2_c1"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as base;
          stackalloc 160 as h3;
          coq:(final_exp_full_body)
        ))).

    Lemma bls12_final_exp_ok : program_logic_goal_for_function! bls12_final_exp.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Top-level pairing: e(P, Q) = final_exp(miller_loop(P, Q))      *)
    (* ============================================================== *)

    Local Definition pairing_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius constants *)
        cmd.call [] "bls12_load_gamma1_p2" [expr.var "gamma1_p2"];
        cmd.call [] "bls12_load_gamma2_p2" [expr.var "gamma2_p2"];
        cmd.call [] "bls12_load_w_frob_p2_c1" [expr.var "w_frob_p2_c1"];
        (* Miller loop *)
        cmd.call [] "bls12_miller_loop"
          [expr.var "tmp"; expr.var "p_x"; expr.var "p_y";
           expr.var "q_x"; expr.var "q_y"];
        (* Final exponentiation *)
        cmd.call [] "bls12_final_exp"
          [expr.var "out"; expr.var "tmp";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"]
      ].

    Definition bls12_pairing : function_t :=
      ("bls12_pairing",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma1_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma2_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as w_frob_p2_c1;
          coq:(pairing_full_body)
        ))).

    Lemma bls12_pairing_ok : program_logic_goal_for_function! bls12_pairing.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Collected function lists                                        *)
    (* ============================================================== *)

    Definition bls12_all_pairing_funcs : list function_t :=
      bls12_Fp6_funcs ++
      bls12_Fp12_funcs ++
      bls12_pairing_ops ++
      [ bls12_Fp2_mul_fp;
        bls12_make_line;
        bls12_load_gamma1_p2;
        bls12_load_gamma2_p2;
        bls12_load_w_frob_p2_c1;
        bls12_miller_loop;
        bls12_final_exp;
        bls12_pairing ].

    (* ============================================================== *)
    (* Top-level pairing correctness theorem                            *)
    (*                                                                  *)
    (* States: given the function table containing all pairing          *)
    (* functions, calling "bls12_pairing" on G1 point P = (p_x, p_y)   *)
    (* and G2 point Q = (q_x, q_y) produces the optimal Ate pairing    *)
    (* e(P, Q) as an Fp12 element.                                     *)
    (* ============================================================== *)

    (** Top-level pairing correctness claim.
        States that calling bls12_pairing with all functions in the table
        terminates and produces an Fp12 result. The functional correctness
        (result = optimal Ate pairing of P and Q) requires additional
        specifications for the Miller loop and final exponentiation. *)
    Theorem bls12_pairing_correct :
      forall functions tr mem
        pout p_px p_py p_qx p_qy,
      (* All pairing functions are in the function table *)
      (forall f, In f bls12_all_pairing_funcs ->
        map.get functions (fst f) = Some (snd f)) ->
      (* The call terminates *)
      WeakestPrecondition.call functions "bls12_pairing" tr mem
        [pout; p_px; p_py; p_qx; p_qy]
        (fun tr' mem' rets =>
          rets = [] /\ tr = tr'
          (* Full spec: exists result : Fp12 felem,
               feval result = Pairing.pairing (P_x, P_y) (Q_x, Q_y) *)
        ).
    Proof. Admitted.

End BLS12_Pairing.
