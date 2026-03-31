Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.

Require Import Crypto.Arithmetic.BYInv.WordByWordMontgomery.
Require Import Crypto.Arithmetic.BYInv.UnsaturatedSolinas.
Require Import Crypto.Arithmetic.BYInv.ArithmeticShiftr.
Require Import Crypto.Arithmetic.BYInv.TCAdd.
Require Import Crypto.Arithmetic.BYInv.TCMul.
Require Import Crypto.Arithmetic.BYInv.TCOpp.
Require Import Crypto.Arithmetic.BYInv.Zero.
Require Import Crypto.Arithmetic.BYInv.One.
Require Import Crypto.Arithmetic.BYInv.Select.
Require Import Crypto.Arithmetic.BYInv.Firstn.
Require Import Crypto.Arithmetic.BYInv.Partition.

Require Import Crypto.Util.ZUtil.TwosComplement.
Require Import Crypto.Util.ZUtil.TwosComplementOpp.
Require Import Crypto.Util.ZUtil.TwosComplementPos.

Local Open Scope Z_scope.

#[global] Hint Rewrite
 length_tc_add
 arithmetic_shiftr_length
 word_tc_mul_length
  : length_distr.

#[global] Hint Rewrite
 tc_eval_arithmetic_shiftr1
 tc_eval_tc_add
 tc_eval_select
 tc_eval_tc_opp
 tc_opp_mod2
 tc_eval_zero : tc.

#[global] Hint Rewrite
 Z.twos_complement_mod
 Z.twos_complement_add_full
 Z.twos_complement_opp'_spec
 Z.twos_complement_one
 Z.twos_complement_zero
 Z.twos_complement_pos'_spec : Ztc.

#[global] Hint Resolve
 length_tc_add
 length_tc_opp
 length_select
 length_zero
 length_one
 length_partition
 firstn_length_le
 arithmetic_shiftr1_length
 arithmetic_shiftr_length
 word_tc_mul_length
 WordByWordMontgomery.length_mulmod
 WordByWordMontgomery.length_twosc_word_mod_m
 WordByWordMontgomery.length_addmod
 WordByWordMontgomery.length_oppmod
 UnsaturatedSolinas.length_addmod
 UnsaturatedSolinas.length_carrymod
 UnsaturatedSolinas.length_oppmod
 UnsaturatedSolinas.length_mulmod
 UnsaturatedSolinas.length_carry_mulmod
 UnsaturatedSolinas.length_encodemod
 UnsaturatedSolinas.word_to_solina_length
  : len.

#[global] Hint Extern 3 (_ < _) => lia : len.
#[global] Hint Extern 3 (_ <= _) => lia : len.
#[global] Hint Extern 3 (_ <= _ < _) => lia : len.
#[global] Hint Extern 4 (_ < _)%nat => lia : len.
#[global] Hint Extern 4 (_ <= _)%nat => lia : len.
#[global] Hint Extern 4 (_ <= _)%nat => progress autorewrite with length_distr; auto with len : len.
#[global] Hint Extern 3 (WordByWordMontgomery.valid _ _ _ _) => auto with valid : len.

#[global] Hint Resolve
 WordByWordMontgomery.select_valid
 WordByWordMontgomery.zero_valid
 WordByWordMontgomery.addmod_valid
 WordByWordMontgomery.oppmod_valid
 WordByWordMontgomery.mulmod_valid
 WordByWordMontgomery.twosc_word_mod_m_valid
 WordByWordMontgomery.one_valid
 WordByWordMontgomery.partition_valid
  : valid.

#[global] Hint Extern 3 (_ < _) => lia : valid.
#[global] Hint Extern 3 (_ <= _) => lia : valid.
#[global] Hint Extern 3 (_ <= _ < _) => lia : valid.
#[global] Hint Extern 4 (_ < _)%nat => lia : valid.
#[global] Hint Extern 4 (_ <= _)%nat => lia : valid.
#[global] Hint Extern 3 (length _ = _) => auto with len : valid.

#[global] Hint Resolve
 arithmetic_shiftr_in_bounded
 arithmetic_shiftr1_in_bounded
 tc_add_in_bounded
 select_in_bounded
 firstn_in_bounded
 partition_in_bounded : in_bounded.

#[global] Hint Extern 4 (_ < _) => lia : in_bounded.
#[global] Hint Extern 4 (_ <= _) => lia : in_bounded.
#[global] Hint Extern 4 (_ <= _ < _) => lia : in_bounded.
#[global] Hint Extern 3 (length _ = _) => auto with len : in_bounded.
