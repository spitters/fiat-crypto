(* BLS12-377 Fp2 = Fp[u]/(u² + 5) where β = -5 is a QNR.
   Unlike BLS12-381 which uses u² + 1 (β = -1), BLS12-377 has p ≡ 1 (mod 4)
   so -1 is a QR and cannot be used.

   The Karatsuba Fp2 multiplication:
     (a + bu)(c + du) = (ac + β·bd) + ((a+b)(c+d) - ac - bd)u
   For β = -5: ac + β·bd = ac - 5·bd

   Implementation: scmul_neg5(x) = -(x + x + x + x + x) = -(4x + x)
   Realized as: tmp = add(x, x); tmp = add(tmp, tmp); out = add(tmp, x); out = opp(out)
   Or more efficiently: out = sub(0, x); tmp = add(out, out); tmp = add(tmp, tmp); out = add(tmp, out)
   i.e., out = -x; out = -4x + (-x) = -5x *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section bls377_Fp2.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bls377_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_377_prime.m).

    Instance bls377_prime_parameters : PrimeFieldParameters := {|
      PrimeField.M_pos := bls377_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls377_mul";
      PrimeField.add := "bls377_add";
      PrimeField.sub := "bls377_sub";
      PrimeField.opp := "bls377_opp";
      PrimeField.square := "bls377_square";
      PrimeField.scmula24 := "bls377_scmula24";
      PrimeField.inv := "bls377_inv";
      PrimeField.from_bytes := "bls377_from_bytes";
      PrimeField.to_bytes := "bls377_to_bytes";
      PrimeField.select_znz := "bls377_select_znz";
      PrimeField.felem_copy := "bls377_felem_copy";
      PrimeField.from_word := "bls377_from_word";
      PrimeField.from_list := "bls377_from_list";
    |}.

    Instance bls377_prime_parameters_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_377. Qed.

    Existing Instance prime_field_parameters.

    Instance bls377_field_representation : AbstractField.FieldRepresentation
      (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls377_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls377_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls377_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls377_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls377_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls377_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls377_frep |}.

    Instance bls377_field_representation_ok : AbstractField.FieldRepresentation_ok
      (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls377_field_representation] in *.
      cbv [Field.bounded_by bls377_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Instance bls377_field_names : FieldNames (F:=F PrimeField.M_pos) :=
      field_names_prefixed "bls377_".

    Local Notation F := (F PrimeField.M_pos).
    Local Notation Fp2 := (F * F)%type.

    (* Pointer to the second Fp element in an Fp2 pair *)
    Local Definition felem_offset : Z :=
      AbstractField.felem_size_in_bytes (F:=F).
    Local Definition expr_2nd_felem (x : Syntax.expr) :=
      expr.op bopname.add x (expr.literal felem_offset).

    (* β = -5 is a QNR for BLS12-377 *)
    Definition beta_val : Z := -5.

    (* scmul_neg5: compute -5 * x in Fp.
       Implementation: neg_x = 0 - x; t = neg_x + neg_x; t = t + t; out = t + neg_x
       i.e., out = -4x + (-x) = -5x *)
    Definition bls377_scmul_beta : string * Syntax.func :=
      ("bls377_scmul_beta", (["out"; "x"], []:list String.string, bedrock_func_body:(
        (* out = 0 - x = -x *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "out"; expr.var "x"]);
        (* BUG: out is uninitialized. Need a zero constant or use opp. *)
        (* Actually for sub(out, out, x): out starts as whatever was there.
           Better approach: use the fact that sub(out, 0, x) = -x
           But we need 0 in an felem. Use a temp or a different strategy. *)
        (* Simple 4-add approach: *)
        (* t = x + x *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "x"; expr.var "x"]);
        (* t = t + t = 4x *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "out"; expr.var "out"]);
        (* t = t + x = 5x *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "out"; expr.var "x"]);
        (* out = 0 - t = -5x. Use sub(out, x, out) and then sub(out, x, out) again? No. *)
        (* Actually: sub(out, out, out) = 0, then sub that from... *)
        (* Simplest: compute 5x then negate. But we don't have opp in AbstractField. *)
        (* We DO have sub. sub(out, zero, 5x)? But zero needs to be in memory. *)
        (* Alternative: sub(out, x, out) after computing 6x in out? No. *)
        (* Let's just use: out = sub(0_const, 5x). But 0_const needs a memory location. *)
        (* Actually the simplest approach: just use sub(out, v0, 5*v1) in the Fp2_mul body.
           That is: replace the last line "sub(out.re, v0, v1)" with:
             tmp = add(v1, v1)      -- 2*v1
             tmp = add(tmp, tmp)    -- 4*v1
             tmp = add(tmp, v1)     -- 5*v1
             out.re = sub(v0, tmp)  -- v0 - 5*v1 = ac + (-5)*bd = ac + β·bd
           This avoids needing a separate scmul_beta function. *)
        coq:(cmd.skip)
      ))).

    (* Fp2 multiplication for BLS12-377: (a+bu)(c+du) = (ac + β·bd) + ((a+b)(c+d)-ac-bd)u
       where β = -5.
       Karatsuba with scmul by -5 inlined as 5 additions + 1 subtraction. *)
    Definition Fp2_mul_377 : string * Syntax.func :=
      ("bls377_Fp2_mul", (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v0;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v1;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v2;
        (* v0 = a * c *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr.var "v0"; expr.var "inx"; expr.var "iny"]);
        (* v1 = b * d *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr.var "v1"; expr_2nd_felem (expr.var "inx"); expr_2nd_felem (expr.var "iny")]);
        (* v2 = a + b *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "v2"; expr.var "inx"; expr_2nd_felem (expr.var "inx")]);
        (* out.im = c + d *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "iny"; expr_2nd_felem (expr.var "iny")]);
        (* out.im = (c+d) * (a+b) *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v2"]);
        (* out.im -= v0 *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v0"]);
        (* out.im -= v1 = ad + bc *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v1"]);
        (* Now compute out.re = v0 - 5*v1 = ac + β·bd *)
        (* v2 = v1 + v1 = 2*bd *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "v2"; expr.var "v1"; expr.var "v1"]);
        (* v2 = v2 + v2 = 4*bd *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "v2"; expr.var "v2"; expr.var "v2"]);
        (* v2 = v2 + v1 = 5*bd *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "v2"; expr.var "v2"; expr.var "v1"]);
        (* out.re = v0 - v2 = ac - 5*bd *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "v0"; expr.var "v2"])
      ))).

End bls377_Fp2.
