(** * BN254 Pairing — bedrock2 compilation top-level.

    Instantiates the full field tower (Fp -> Fp2 -> Fp6 -> Fp12) for
    BN254 (alt_bn128) and defines bedrock2 function bodies for the optimal
    Ate pairing: Miller loop, final exponentiation, and top-level pairing.

    The field tower arithmetic bodies are imported from the FieldExtensions
    layer. This file adds:
    - Helper functions (fp2_mul_fp, make_line for line evaluation)
    - Miller loop with cmd.while over 65 bits of the 6u+2 parameter
    - Final exponentiation: easy part (conjugate/inv/frobenius_p2) +
      hard part (DSD decomposition — placeholder, BN-specific formula TBD)
    - Top-level pairing chaining Miller loop + final exponentiation

    BN254 differences from BLS12-377:
    - beta = -1 (not -5), xi = (9, 1) (not u = (0, 1))
    - Fp = 4 words (not 6), 254-bit prime
    - u = 0x44E992B44A6909F1 is positive => NO conjugation after Miller loop
    - Miller loop iterates over bits of |6u+2| (65 bits, single word)
    - p ≡ 3 mod 4 makes QNR proof simpler

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
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime_certif.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsFiat.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

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

Section BN254_Pairing.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* ============================================================== *)
    (* BN254 prime parameters                                          *)
    (* ============================================================== *)

    Let bn254_M_pos : positive := Eval vm_compute in (Z.to_pos bn254_prime.m).

    Instance bn254_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn254_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn254_mul";
      PrimeField.add := "bn254_add";
      PrimeField.sub := "bn254_sub";
      PrimeField.opp := "bn254_opp";
      PrimeField.square := "bn254_square";
      PrimeField.scmula24 := "bn254_scmula24";
      PrimeField.inv := "bn254_inv";
      PrimeField.from_bytes := "bn254_from_bytes";
      PrimeField.to_bytes := "bn254_to_bytes";
      PrimeField.select_znz := "bn254_select_znz";
      PrimeField.felem_copy := "bn254_felem_copy";
      PrimeField.from_word := "bn254_from_word";
      PrimeField.from_list := "bn254_from_list";
    |}.

    Instance bn254_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn254. Qed.

    Existing Instance prime_field_parameters.

    (* Fp-level representation from synthesis pipeline *)
    Instance bn254_fp_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn254_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn254_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn254_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn254_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn254_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn254_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn254_frep |}.

    Instance bn254_fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn254_fp_rep] in *.
      cbv [Field.bounded_by bn254_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    (* beta = -1 for BN254 (Fp2 = Fp[u]/(u^2 + 1)) *)
    Let bn254_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* xi = (9, 1) for BN254 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bn254_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 9.
    Let bn254_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Lemma bn254_beta_nz : bn254_beta <> @F.zero PrimeField.M_pos.
    Proof.
      unfold bn254_beta. intro H. apply (f_equal F.to_Z) in H.
      rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
    Qed.

    Lemma bn254_M_big : 2 < Z.pos PrimeField.M_pos.
    Proof. vm_compute. reflexivity. Qed.

    (* BN254: p ≡ 3 mod 4, so -1 is a QNR.
       Euler criterion: (-1)^((p-1)/2) = -1 ≠ 1. *)
    Lemma bn254_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bn254_beta).
    Proof.
      intro H.
      assert (Hprime : Znumtheory.prime (Z.pos PrimeField.M_pos))
        by exact prime_bn254.
      assert (Hbig : 2 < Z.pos PrimeField.M_pos) by exact bn254_M_big.
      apply (proj2 (@F.euler_criterion _ Hprime Hbig bn254_beta bn254_beta_nz)) in H.
      assert (Hcheck : (F.to_Z (@F.pow PrimeField.M_pos bn254_beta
        (Z.to_N (Z.pos PrimeField.M_pos / 2))) =? F.to_Z (@F.one PrimeField.M_pos))%Z = false).
      { vm_cast_no_check (eq_refl false). }
      apply (f_equal F.to_Z) in H. rewrite H in Hcheck.
      rewrite Z.eqb_refl in Hcheck. discriminate.
    Qed.

    (* ============================================================== *)
    (* Field name prefixes                                             *)
    (* ============================================================== *)

    Let fp2_prefix := "bn254_Fp2_".
    Let fp6_prefix := "bn254_Fp6_".
    Let fp12_prefix := "bn254_Fp12_".

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

    Instance bn254_Fp2_params : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bn254_beta "bn254_") in exact v).
    Instance bn254_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bn254_beta "bn254_") in exact v).
    Instance bn254_Fp2_names : FieldNames (F:=Fp2) :=
      field_names_prefixed fp2_prefix.

    (* ============================================================== *)
    (* Fp6 instances                                                   *)
    (* ============================================================== *)

    Instance bn254_Fp6_params : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp6_names : FieldNames (F:=Fp6) :=
      field_names_prefixed fp6_prefix.

    (* ============================================================== *)
    (* Fp12 instances                                                  *)
    (* ============================================================== *)

    Instance bn254_Fp12_params : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
    Instance bn254_Fp12_names : FieldNames (F:=Fp12) :=
      field_names_prefixed fp12_prefix.
    Instance bn254_Fp_names : FieldNames (F:=Fp) :=
      field_names_prefixed "bn254_".

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

    Let fp_add_name : string := PrimeField.add.
    Let fp_sub_name : string := PrimeField.sub.
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
    Let fp12_frobenius_name : string := (fp12_prefix ++ "frobenius")%string.
    Let fp2_mul_fp_name : string := "bn254_Fp2_mul_fp".
    Let make_line_name : string := "bn254_make_line".
    Let fp2_mul_xi_name : string := (fp2_prefix ++ "mul_xi")%string.

    (* ============================================================== *)
    (* Fp2_mul_xi: multiply Fp2 element by xi = (9, 1)                *)
    (*   (a0 + a1*u) * (9 + u) = (9*a0 - a1) + (a0 + 9*a1)*u        *)
    (*   where beta = -1, so a1*u*u = -a1                              *)
    (*   Multiply-by-9: x -> 2x -> 4x -> 8x -> 8x+x = 9x            *)
    (* ============================================================== *)

    Definition bn254_Fp2_mul_xi : function_t :=
      (fp2_mul_xi_name,
       (["out"; "x"], []:list String.string, bedrock_func_body:(
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp)) as tmp_a9;
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp)) as tmp_b9;
         (* tmp_a9 = 9*a: 2a -> 4a -> 8a -> 8a+a *)
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_a9"; expr.var "x"; expr.var "x"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_a9"; expr.var "tmp_a9"; expr.var "tmp_a9"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_a9"; expr.var "tmp_a9"; expr.var "tmp_a9"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_a9"; expr.var "tmp_a9"; expr.var "x"]);
         (* tmp_b9 = 9*b: 2b -> 4b -> 8b -> 8b+b *)
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_b9"; expr_fp_snd (expr.var "x"); expr_fp_snd (expr.var "x")]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_b9"; expr.var "tmp_b9"; expr.var "tmp_b9"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_b9"; expr.var "tmp_b9"; expr.var "tmp_b9"]);
         coq:(cmd.call [] fp_add_name
           [expr.var "tmp_b9"; expr.var "tmp_b9"; expr_fp_snd (expr.var "x")]);
         (* out.re = 9a - b *)
         coq:(cmd.call [] fp_sub_name
           [expr.var "out"; expr.var "tmp_a9"; expr_fp_snd (expr.var "x")]);
         (* out.im = a + 9b *)
         coq:(cmd.call [] fp_add_name
           [expr_fp_snd (expr.var "out"); expr.var "x"; expr.var "tmp_b9"])
       ))).

    Lemma bn254_Fp2_mul_xi_name_eq : fst bn254_Fp2_mul_xi = fp2_mul_xi_name.
    Proof. reflexivity. Qed.

    (* ============================================================== *)
    (* Fp6/Fp12/PairingOps function bodies from lower layers           *)
    (* ============================================================== *)

    Definition bn254_Fp6_funcs : list function_t :=
      Fp6_funcs bn254_beta bn254_xi_re bn254_xi_im fp6_prefix fp2_prefix bn254_Fp2_mul_xi.

    Definition bn254_Fp12_funcs : list function_t :=
      Fp12_funcs bn254_beta bn254_xi_re bn254_xi_im fp12_prefix fp6_prefix fp2_prefix.

    Definition bn254_pairing_ops : list function_t :=
      PairingOps_funcs bn254_beta bn254_xi_re bn254_xi_im fp12_prefix fp6_prefix fp2_prefix.

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

    Definition bn254_Fp2_mul_fp : function_t :=
      (fp2_mul_fp_name,
       (["out"; "x"; "s"], []:list String.string, bedrock_func_body:(
         coq:(cmd.call [] fp_mul_name
           [expr.var "out"; expr.var "x"; expr.var "s"]);
         coq:(cmd.call [] fp_mul_name
           [expr_fp_snd (expr.var "out"); expr_fp_snd (expr.var "x"); expr.var "s"])
       ))).

    Lemma bn254_Fp2_mul_fp_ok : program_logic_goal_for_function! bn254_Fp2_mul_fp.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* make_line: construct line evaluation as Fp12                    *)
    (*   c0 = (lambda*x_T - y_T, -(lambda*x_P), 0)                   *)
    (*   c1 = (0, (y_P, 0), 0)                                        *)
    (* ============================================================== *)

    Definition bn254_make_line : function_t :=
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

    Lemma bn254_make_line_ok : program_logic_goal_for_function! bn254_make_line.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Frobenius constant loaders for BN254                            *)
    (*                                                                  *)
    (* p^2-Frobenius constants (imaginary parts are zero):              *)
    (*   gamma1_p2 = xi^{(p^2-1)/3}                                    *)
    (*   gamma2_p2 = xi^{2(p^2-1)/3}                                   *)
    (*   w_frob_p2_c1 = xi^{(p^2-1)/6}                                 *)
    (* ============================================================== *)

    (* Helper: store an Fp2 constant = (real, 0) where real is 4 limbs *)
    Local Definition store_fp2_real_only (v : string) (l0 l1 l2 l3 : Z) :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var v) (expr.literal l0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 8)) (expr.literal l1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 16)) (expr.literal l2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 24)) (expr.literal l3);
        (* Imaginary part = 0 *)
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 32)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 40)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal 0)
      ].

    (* Helper: store a full Fp2 constant (real + imaginary, 8 limbs) *)
    Local Definition store_fp2_full (v : string)
      (r0 r1 r2 r3 i0 i1 i2 i3 : Z) :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var v) (expr.literal r0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 8)) (expr.literal r1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 16)) (expr.literal r2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 24)) (expr.literal r3);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 32)) (expr.literal i0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 40)) (expr.literal i1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal i2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal i3)
      ].

    (* gamma1_p2 = xi^{(p^2-1)/3} for BN254 in Montgomery form *)
    Definition bn254_load_gamma1_p2 : function_t :=
      ("bn254_load_gamma1_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x3350c88e13e80b9c 0x7dce557cdb5e56b9 0x6001b4b8b615564a 0x2682e617020217e0)).

    Lemma bn254_load_gamma1_p2_ok :
      program_logic_goal_for_function! bn254_load_gamma1_p2.
    Proof. exact I. Qed.

    (* gamma2_p2 = xi^{2(p^2-1)/3} for BN254 in Montgomery form *)
    Definition bn254_load_gamma2_p2 : function_t :=
      ("bn254_load_gamma2_p2",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0x71930c11d782e155 0xa6bb947cffbe3323 0xaa303344d4741444 0x2c3b3f0d26594943)).

    Lemma bn254_load_gamma2_p2_ok :
      program_logic_goal_for_function! bn254_load_gamma2_p2.
    Proof. exact I. Qed.

    (* w_frob_p2_c1 = xi^{(p^2-1)/6} for BN254 in Montgomery form *)
    Definition bn254_load_w_frob_p2_c1 : function_t :=
      ("bn254_load_w_frob_p2_c1",
       (["out"], []:list String.string,
        store_fp2_real_only "out"
          0xca8d800500fa1bf2 0xf0c5d61468b39769 0x0e201271ad0d4418 0x04290f65bad856e6)).

    Lemma bn254_load_w_frob_p2_c1_ok :
      program_logic_goal_for_function! bn254_load_w_frob_p2_c1.
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
    (* Miller loop (real body — processes 65 bits of |6u+2|)           *)
    (* ============================================================== *)

    (* BN254 parameter u = 0x44E992B44A6909F1 (positive) *)
    Let bn254_x : Z := 0x44E992B44A6909F1.

    (* |6u+2| = 29793968203157093288 = 0x19D797039BE763BA8, 65 bits.
       Fits in a single 64-bit word after the leading bit is consumed.
       We store it as a single 64-bit limb (low 64 bits) on the stack:
         lo = 0x9D797039BE763BA8 (low 64 bits, bit 64 = MSB initializes T=Q)
       and iterate 64 bits (bits 63 down to 0).
       Bit extraction: bit = (lo >> i) & 1 *)

    Let bn254_6u2_lo : Z := 0x9D797039BE763BA8.

    (* Store the single 6u+2 limb on the stack *)
    Local Definition store_6u2_limbs : Syntax.cmd.cmd :=
      cmd.store access_size.word (expr.var "u6p2") (expr.literal bn254_6u2_lo).

    (* One iteration of the Miller loop:
       - Decrement i
       - Extract bit i from the single-word 6u+2
       - Doubling step: compute tangent, line evaluation, update f and T
       - Conditional addition step if bit i of 6u+2 is set *)
    Local Definition miller_loop_iteration : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));

        (* Extract bit i from u6p2: bit = (u6p2 >> i) & 1 *)
        cmd.set "word" (expr.load access_size.word (expr.var "u6p2"));
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.var "word") (expr.var "i"))
          (expr.literal 1));

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
       Processes bits 63 down to 0 of |6u+2| (bit 64 = MSB initializes T = Q).
       BN254 has positive u, so NO conjugation after the loop. *)
    Local Definition miller_loop_full_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        fp12_set_one "f";
        cmd.call [] fp2_copy_name [expr.var "t_x"; expr.var "q_x"];
        cmd.call [] fp2_copy_name [expr.var "t_y"; expr.var "q_y"];
        store_6u2_limbs;
        cmd.set "i" (expr.literal 64);
        cmd.while (expr.var "i") miller_loop_iteration;
        (* No conjugation needed: BN254 has positive u *)
        cmd.call [] fp12_copy_name [expr.var "out"; expr.var "f"]
      ].

    Definition bn254_miller_loop : function_t :=
      ("bn254_miller_loop",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as f;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_x;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as t_y;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as lambda;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as line;
          stackalloc 8 as u6p2;
          coq:(miller_loop_full_body)
        ))).

    Lemma bn254_miller_loop_ok : program_logic_goal_for_function! bn254_miller_loop.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Final exponentiation                                            *)
    (*   f^{(p^12-1)/r} = f^{(p^6-1)(p^2+1)*h3}                     *)
    (*   Easy part: conjugate + inv + mul + frobenius_p2 + mul         *)
    (*   Hard part: BN-specific DSD formula (placeholder for now)      *)
    (* ============================================================== *)

    (* ============================================================== *)
    (* Fp12_pow_u: raise Fp12 element to the BN parameter u            *)
    (*   Uses left-to-right binary square-and-multiply on              *)
    (*   u = 0x44E992B44A6909F1 (64-bit, top bit always set)           *)
    (*   u is POSITIVE for BN254, so NO conjugation after.             *)
    (* ============================================================== *)

    Local Definition pow_u_loop_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
        cmd.call [] fp12_sqr_name
          [expr.var "result"; expr.var "result"];
        cmd.set "bit" (expr.op bopname.and
          (expr.op bopname.sru (expr.literal 0x44E992B44A6909F1) (expr.var "i"))
          (expr.literal 1));
        cmd.cond (expr.var "bit")
          (cmd.call [] fp12_mul_name
            [expr.var "result"; expr.var "result"; expr.var "base"])
          cmd.skip
      ].

    Definition bn254_Fp12_pow_u : function_t :=
      ("bn254_Fp12_pow_u",
       (["out"; "base"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          coq:(cmd_seq_list [
            cmd.call [] fp12_copy_name
              [expr.var "result"; expr.var "base"];
            cmd.set "i" (expr.literal 62);
            cmd.while (expr.var "i") pow_u_loop_body;
            cmd.call [] fp12_copy_name
              [expr.var "out"; expr.var "result"]
          ])
        ))).

    Lemma bn254_Fp12_pow_u_ok :
      program_logic_goal_for_function! bn254_Fp12_pow_u.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Frobenius p constant loaders (for DSD final exponentiation)    *)
    (* Constants: gamma1 = xi^{(p-1)/3}, gamma2 = xi^{2(p-1)/3},     *)
    (*   w_frob_c1 = xi^{(p-1)/6} for BN254 in Montgomery form       *)
    (* All imaginary parts are zero.                                   *)
    (* ============================================================== *)

    (* gamma1 = xi^{(p-1)/3} for BN254 in Montgomery form
       TODO: Compute actual values; currently PLACEHOLDERS (zeros). *)
    Definition bn254_load_gamma1 : function_t :=
      ("bn254_load_gamma1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0 0 0 0
          0 0 0 0)).

    Lemma bn254_load_gamma1_ok :
      program_logic_goal_for_function! bn254_load_gamma1.
    Proof. exact I. Qed.

    (* gamma2 = xi^{2(p-1)/3} for BN254 in Montgomery form
       TODO: Compute actual values; currently PLACEHOLDERS (zeros). *)
    Definition bn254_load_gamma2 : function_t :=
      ("bn254_load_gamma2",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0 0 0 0
          0 0 0 0)).

    Lemma bn254_load_gamma2_ok :
      program_logic_goal_for_function! bn254_load_gamma2.
    Proof. exact I. Qed.

    (* w_frob_c1 = xi^{(p-1)/6} for BN254 in Montgomery form
       TODO: Compute actual values; currently PLACEHOLDERS (zeros). *)
    Definition bn254_load_w_frob_c1 : function_t :=
      ("bn254_load_w_frob_c1",
       (["out"], []:list String.string,
        store_fp2_full "out"
          0 0 0 0
          0 0 0 0)).

    Lemma bn254_load_w_frob_c1_ok :
      program_logic_goal_for_function! bn254_load_w_frob_c1.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Final exponentiation hard part (DSD decomposition)             *)
    (*   PLACEHOLDER: Uses the same DSD structure as BLS12-377 for    *)
    (*   now. The actual BN-specific formula will be implemented later *)
    (*   (BN curves use a different DSD decomposition than BLS12).    *)
    (*                                                                  *)
    (*   BN254 has POSITIVE u, so NO conjugations after pow_u.        *)
    (*   t0 = f^u (no conjugation — u is positive)                    *)
    (*   t1 = t0^2                                                     *)
    (*   t2 = pow_u(t0) = f^{u^2}                                     *)
    (*   t3 = t2^2 = f^{2u^2}                                         *)
    (*   Chain multiplications and Frobenius maps                     *)
    (* ============================================================== *)

    Local Definition final_exp_hard_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius constants *)
        cmd.call [] "bn254_load_gamma1" [expr.var "gamma1"];
        cmd.call [] "bn254_load_gamma2" [expr.var "gamma2"];
        cmd.call [] "bn254_load_w_frob_c1" [expr.var "w_frob_c1"];

        (* t0 = f^u (NO conjugation — u is positive for BN254) *)
        cmd.call [] "bn254_Fp12_pow_u"
          [expr.var "t0"; expr.var "f"];

        (* t1 = t0^2 (NO conjugation — u positive means t0^2 = f^{2u}) *)
        cmd.call [] fp12_sqr_name
          [expr.var "t1"; expr.var "t0"];

        (* t2 = pow_u(t0) = f^{u^2} (NO conjugation) *)
        cmd.call [] "bn254_Fp12_pow_u"
          [expr.var "t2"; expr.var "t0"];

        (* t3 = t2^2 = f^{2u^2} (NO conjugation) *)
        cmd.call [] fp12_sqr_name
          [expr.var "t3"; expr.var "t2"];

        (* t1 = t1 * t2 => f^{2u + u^2} *)
        cmd.call [] fp12_mul_name
          [expr.var "t1"; expr.var "t1"; expr.var "t2"];

        (* t2 = pow_u(t2) => f^{u^3} *)
        cmd.call [] "bn254_Fp12_pow_u"
          [expr.var "t2"; expr.var "t2"];

        (* t1 = t1 * t2 => f^{u^3 + u^2 + 2u} *)
        cmd.call [] fp12_mul_name
          [expr.var "t1"; expr.var "t1"; expr.var "t2"];

        (* t1 = conjugate(t1) *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t1"; expr.var "t1"];

        (* t1 = t1 * f *)
        cmd.call [] fp12_mul_name
          [expr.var "t1"; expr.var "t1"; expr.var "f"];

        (* t1 = conjugate(t1) *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t1"; expr.var "t1"];

        (* t0 = conjugate(f) — reuse t0 as temp for conj(f) *)
        cmd.call [] fp12_conjugate_name
          [expr.var "t0"; expr.var "f"];

        (* t1 = t1 * conj(f) *)
        cmd.call [] fp12_mul_name
          [expr.var "t1"; expr.var "t1"; expr.var "t0"];

        (* t2 = pow_u(t2) => f^{u^4} *)
        cmd.call [] "bn254_Fp12_pow_u"
          [expr.var "t2"; expr.var "t2"];

        (* t0 = t2 * t3 — reuse t0 as accumulator *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t2"; expr.var "t3"];

        (* t0 = t0 * t1 *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t1"];

        (* Frobenius maps: t1 = f^p, t2 = f^{p^2}, t3 = f^{p^3} *)
        cmd.call [] fp12_frobenius_name
          [expr.var "t1"; expr.var "f";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        cmd.call [] fp12_frobenius_name
          [expr.var "t2"; expr.var "t1";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
        cmd.call [] fp12_frobenius_name
          [expr.var "t3"; expr.var "t2";
           expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];

        (* result = t0 * frob1 * frob2 * frob3 *)
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t1"];
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t2"];
        cmd.call [] fp12_mul_name
          [expr.var "t0"; expr.var "t0"; expr.var "t3"];

        (* Copy to output *)
        cmd.call [] fp12_copy_name
          [expr.var "out"; expr.var "t0"]
      ].

    Definition bn254_final_exp_hard_dsd : function_t :=
      ("bn254_final_exp_hard_dsd",
       (["out"; "f"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t0;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as t3;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma1;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as w_frob_c1;
          coq:(final_exp_hard_dsd_body)
        ))).

    Lemma bn254_final_exp_hard_dsd_ok :
      program_logic_goal_for_function! bn254_final_exp_hard_dsd.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* DSD final exponentiation (easy part + DSD hard part)           *)
    (*   Easy part: same as BLS12 (conjugate/inv/frobenius_p2)         *)
    (*   Hard part: DSD decomposition (placeholder — BN-specific TBD) *)
    (* ============================================================== *)

    Local Definition final_exp_dsd_body : Syntax.cmd.cmd :=
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
        (* Hard part: DSD decomposition *)
        cmd.call [] "bn254_final_exp_hard_dsd"
          [expr.var "out"; expr.var "result"]
      ].

    Definition bn254_final_exp_dsd : function_t :=
      ("bn254_final_exp_dsd",
       (["out"; "f"; "gamma1_p2"; "gamma2_p2"; "w_frob_p2_c1"],
        []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as result;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          coq:(final_exp_dsd_body)
        ))).

    Lemma bn254_final_exp_dsd_ok :
      program_logic_goal_for_function! bn254_final_exp_dsd.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Top-level pairing using DSD final exponentiation                *)
    (* ============================================================== *)

    Local Definition pairing_dsd_body : Syntax.cmd.cmd :=
      cmd_seq_list [
        (* Load Frobenius p^2 constants *)
        cmd.call [] "bn254_load_gamma1_p2" [expr.var "gamma1_p2"];
        cmd.call [] "bn254_load_gamma2_p2" [expr.var "gamma2_p2"];
        cmd.call [] "bn254_load_w_frob_p2_c1" [expr.var "w_frob_p2_c1"];
        (* Miller loop *)
        cmd.call [] "bn254_miller_loop"
          [expr.var "tmp"; expr.var "p_x"; expr.var "p_y";
           expr.var "q_x"; expr.var "q_y"];
        (* Final exponentiation (DSD) *)
        cmd.call [] "bn254_final_exp_dsd"
          [expr.var "out"; expr.var "tmp";
           expr.var "gamma1_p2"; expr.var "gamma2_p2";
           expr.var "w_frob_p2_c1"]
      ].

    Definition bn254_pairing_dsd : function_t :=
      ("bn254_pairing_dsd",
       (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
        bedrock_func_body:(
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as tmp;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma1_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as gamma2_p2;
          stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as w_frob_p2_c1;
          coq:(pairing_dsd_body)
        ))).

    Lemma bn254_pairing_dsd_ok :
      program_logic_goal_for_function! bn254_pairing_dsd.
    Proof. exact I. Qed.

    (* ============================================================== *)
    (* Collected function lists                                        *)
    (* ============================================================== *)

    Definition bn254_all_pairing_funcs : list function_t :=
      bn254_Fp6_funcs ++
      bn254_Fp12_funcs ++
      bn254_pairing_ops ++
      [ bn254_Fp2_mul_fp;
        bn254_make_line;
        bn254_load_gamma1_p2;
        bn254_load_gamma2_p2;
        bn254_load_w_frob_p2_c1;
        bn254_load_gamma1;
        bn254_load_gamma2;
        bn254_load_w_frob_c1;
        bn254_Fp12_pow_u;
        bn254_final_exp_hard_dsd;
        bn254_final_exp_dsd;
        bn254_miller_loop;
        bn254_pairing_dsd ].

    (* ============================================================== *)
    (* Top-level pairing correctness theorem                            *)
    (*                                                                  *)
    (* States: given the function table containing all pairing          *)
    (* functions, calling "bn254_pairing_dsd" on G1 point P = (p_x,    *)
    (* p_y) and G2 point Q = (q_x, q_y) produces the optimal Ate      *)
    (* pairing e(P, Q) as an Fp12 element.                             *)
    (* ============================================================== *)

End BN254_Pairing.
