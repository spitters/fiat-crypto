Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModOps.

Require Import Crypto.Arithmetic.BYInv.Ref.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.ModExp.

Require Import Crypto.Util.LetIn.

Import Positional.
Import ListNotations.
Import Crypto.Util.ZUtil.Notations.

Local Open Scope Z.

Definition in_bounded machine_wordsize f :=
  forall z, In z f -> 0 <= z < 2 ^ machine_wordsize.

(*Evaluation function for multi-limb integers in twos complement *)
Definition tc_eval machine_wordsize n f :=
  Z.twos_complement (machine_wordsize * Z.of_nat n) (eval (uweight machine_wordsize) n f).

(*Saturated addition of multi-limb integers *)
Definition tc_add machine_wordsize n f g :=
  fst (Rows.add (uweight machine_wordsize) n f g).

Definition odd f :=
  Z.odd (nth_default 0 f 0).

Definition even f :=
  Z.even (nth_default 0 f 0).

(*Saturated (logical) right shift *)
Definition shiftr machine_wordsize n f :=
  (map
    (fun i =>
       Z.lor (Z.shiftr (nth_default 0 f i) 1)
             (Z.truncating_shiftl machine_wordsize
                           (nth_default 0 f (S i))
                           (machine_wordsize - 1)))
    (seq 0 (n - 1))) ++ [(nth_default 0 f (n - 1)) >> 1].

(* arithmetic right shift of saturated multi-limb integers *)
Definition arithmetic_shiftr1 machine_wordsize n f :=
  (map
     (fun i =>
        ((nth_default 0 f i) >> 1) |' (Z.truncating_shiftl machine_wordsize
                                                    (nth_default 0 f (i + 1))
                                                    (machine_wordsize - 1)))
     (seq 0 (n - 1)))
    ++ [Z.arithmetic_shiftr1 machine_wordsize (nth_default 0 f (n - 1))].

(* Multi-limb parity check *)
Definition mod2 f :=
  nth_default 0 f 0 mod 2.

Definition one n := cons 1 (zeros (n - 1)).

Definition tc_opp machine_wordsize n f :=
  tc_add machine_wordsize n
          (one n)
          (map (fun i => Z.lnot_modulo i (2^machine_wordsize)) f).

Definition zero n :=
  zeros n.

Definition ones m n :=
  repeat (2 ^ m - 1) n.
(* Definition ones m n := *)
(*   repeat (Z.ones m) n. *)

Definition tc_sign_bit machine_wordsize n a :=
  nth_default 0 a (n - 1) >> (machine_wordsize - 1).

(*Multiplication of saturated multi-limb integers *)
Definition sat_mul machine_wordsize n1 n2 f g :=
  fst (Rows.mul (uweight machine_wordsize) (2^machine_wordsize) n1 n2 f g).

Definition arithmetic_shiftr machine_wordsize n f k :=
  (map
     (fun i =>
        ((nth_default 0 f i) >> k) |' (Z.truncating_shiftl machine_wordsize
                                                           (nth_default 0 f (i + 1))
                                                           (machine_wordsize - k)))
     (seq 0 (n - 1)))
    ++ [Z.arithmetic_shiftr machine_wordsize (nth_default 0 f (n - 1)) k].

(* Extends a multi-limb integer in twos complement to a new base *)
Definition tc_sign_extend machine_wordsize old_base new_base a :=
  let high_limb := nth_default 0 a (old_base - 1) in
  let cond := Z.sign_bit machine_wordsize high_limb in
  dlet parity := Z.zselect cond 0 (2^machine_wordsize - 1) in
        let padding := repeat parity (new_base - old_base) in
        a ++ padding.

Definition tc_word_bits machine_wordsize a :=
  nth_default 0 a 0 mod 2^(machine_wordsize - 2).

Definition tc_mod_word machine_wordsize n a :=
  let cond := tc_sign_bit machine_wordsize n a in
  let a' := select cond a (tc_opp machine_wordsize n a) in
  let t := (nth_default 0 a' 0) in
  let res := Z.zselect cond t (Z.twos_complement_opp machine_wordsize t) in res.

Definition tc_mul machine_wordsize na nb nab a b :=
  firstn nab (fst (Rows.mul (uweight machine_wordsize) (2^machine_wordsize) nab (2 * nab)
                            (tc_sign_extend machine_wordsize na nab a) (tc_sign_extend machine_wordsize nb nab b))).

Definition tc_mul_full machine_wordsize na nb a b :=
  tc_mul machine_wordsize na nb (na + nb) a b.

Definition word_tc_mul machine_wordsize n (a : Z) b :=
  tc_mul_full machine_wordsize 1 n [a] b.

Definition twos_complement_word_full_divstep_aux machine_wordsize (data : Z * Z * Z * Z * Z * Z * Z) :=
  let '(d,f,g,u,v,q,r) := data in
  let cond := Z.land (Z.twos_complement_pos machine_wordsize d) (g mod 2) in
  dlet d' := Z.zselect cond d (Z.twos_complement_opp machine_wordsize d) in
  dlet f' := Z.zselect cond f g in
  dlet g' := Z.zselect cond g (Z.twos_complement_opp machine_wordsize f) in
  dlet u' := Z.zselect cond u q in
  dlet v' := Z.zselect cond v r in
  let u'':= (u' + u') mod 2^machine_wordsize in
  let v'':= (v' + v') mod 2^machine_wordsize in
  dlet q' := Z.zselect cond q (Z.twos_complement_opp machine_wordsize u) in
  dlet r' := Z.zselect cond r (Z.twos_complement_opp machine_wordsize v) in
  let g0 := g' mod 2 in
  let d'' := (1 + d') mod 2^machine_wordsize in
  dlet f'' := Z.zselect g0 0 f' in
  let g'' := Z.arithmetic_shiftr1 machine_wordsize ((g' + f'') mod 2^machine_wordsize) in
  dlet u''' := Z.zselect g0 0 u' in
  dlet v''' := Z.zselect g0 0 v' in
  let q'' := (q' + u''') mod 2^machine_wordsize in
  let r'' := (r' + v''') mod 2^machine_wordsize in
  (d'',f',g'',u'',v'',q'',r'').

Definition twos_complement_word_full_divstep machine_wordsize d f g u v q r :=
  twos_complement_word_full_divstep_aux machine_wordsize (d, f, g, u, v, q, r).

Definition twos_complement_word_full_divsteps machine_wordsize d f g u v q r n :=
  fold_left (fun data i => twos_complement_word_full_divstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r).

Definition twos_complement_word_full_hddivstep_aux machine_wordsize (data : Z * Z * Z * Z * Z * Z * Z) :=
  let '(d,f,g,u,v,q,r) := data in
  let cond := Z.land (Z.twos_complement_pos machine_wordsize d) (g mod 2) in
  dlet d' := Z.zselect cond d (Z.twos_complement_opp machine_wordsize d) in
  dlet f' := Z.zselect cond f g in
  dlet g' := Z.zselect cond g (Z.twos_complement_opp machine_wordsize f) in
  dlet u' := Z.zselect cond u q in
  dlet v' := Z.zselect cond v r in
  let u'':= (u' + u') mod 2^machine_wordsize in
  let v'':= (v' + v') mod 2^machine_wordsize in
  dlet q' := Z.zselect cond q (Z.twos_complement_opp machine_wordsize u) in
  dlet r' := Z.zselect cond r (Z.twos_complement_opp machine_wordsize v) in
  let g0 := g' mod 2 in
  let d'' := (2 + d') mod 2^machine_wordsize in
  dlet f'' := Z.zselect g0 0 f' in
  let g'' := Z.arithmetic_shiftr1 machine_wordsize ((g' + f'') mod 2^machine_wordsize) in
  dlet u''' := Z.zselect g0 0 u' in
  dlet v''' := Z.zselect g0 0 v' in
  let q'' := (q' + u''') mod 2^machine_wordsize in
  let r'' := (r' + v''') mod 2^machine_wordsize in
  (d'',f',g'',u'',v'',q'',r'').

Definition twos_complement_word_full_hddivstep machine_wordsize d f g u v q r :=
  twos_complement_word_full_hddivstep_aux machine_wordsize (d, f, g, u, v, q, r).

Definition twos_complement_word_full_hddivsteps machine_wordsize d f g u v q r n :=
  fold_left (fun data i => twos_complement_word_full_hddivstep_aux machine_wordsize data) (seq 0 n) (d,f,g,u,v,q,r).

Module Export WordByWordMontgomery.

  Import Positional.
  Import WordByWordMontgomery.WordByWordMontgomery.
  Import Partition.

  Section __.
    Context (machine_wordsize : Z)
            (mont_limbs : nat)
            (tc_limbs : nat)
            (word_tc_mul_limbs : nat)
            (m : Z)
            (r' : Z)
            (m' : Z).

    Local Notation twos_complement_pos' := (Z.twos_complement_pos' machine_wordsize).
    Local Notation twos_complement_opp' := (Z.twos_complement_opp' machine_wordsize).
    Local Notation tc_opp := (tc_opp machine_wordsize tc_limbs).
    Local Notation tc_add := (tc_add machine_wordsize).
    Local Notation arithmetic_shiftr1 := (arithmetic_shiftr1 machine_wordsize tc_limbs).
    Local Notation addmod := (addmod machine_wordsize mont_limbs m).
    Local Notation mulmod := (mulmod machine_wordsize mont_limbs m m').
    Local Notation oppmod := (oppmod machine_wordsize mont_limbs m).
    Local Notation word_tc_mul := (word_tc_mul machine_wordsize tc_limbs).
    Local Notation arithmetic_shiftr := (arithmetic_shiftr machine_wordsize word_tc_mul_limbs).

    Definition divstep_aux (data : Z * (list Z) * (list Z) * (list Z) * (list Z)) :=
      let '(d,f,g,v,r) := data in
      dlet cond := Z.land (twos_complement_pos' d) (mod2 g) in
      dlet d' := Z.zselect cond d (twos_complement_opp' d) in
      dlet f' := select cond f g in
      dlet g' := select cond g (tc_opp f) in
      dlet v' := select cond v r in
      let v'':= addmod v' v' in
      dlet r' := select cond r (oppmod v) in
      dlet g0 := mod2 g' in
      let d'' := (d' + 1) mod 2 ^ machine_wordsize in (* (fst (Z.add_get_carry_full (2^machine_wordsize) d' 1)) in *)
      dlet f'' := select g0 (zero tc_limbs) f' in
      let g'' := arithmetic_shiftr1 (tc_add tc_limbs g' f'') in
      dlet v''' := select g0 (zero mont_limbs) v' in
      let r'' := addmod r' v''' in
    (d'',f',g'',v'',r'').

    Definition divstep d f g v r :=
      divstep_aux (d, f, g, v, r).

    Definition divstep_precompmod :=
      let bits := (Z.log2 m) + 1 in
      let i := iterations bits in
      let k := (m + 1) / 2 in
      let precomp := (Z.modexp k i m) in
      let RN := (Z.modexp 2 (3 * machine_wordsize * Z.of_nat mont_limbs)) m in
      (RN * precomp) mod m.

    Definition partition_divstep_precomp :=
      Partition.partition (uweight machine_wordsize) mont_limbs divstep_precompmod.

    Definition by_inv g :=
      let bits := (Z.log2 m) + 1 in
      let msat := Partition.partition (uweight machine_wordsize) tc_limbs m in
      let its := iterations bits in
      let pc := partition_divstep_precomp in
      let '(_, fm, _, vm, _) :=
        fold_left (fun data i => divstep_aux data)
                  (seq 0 (Z.to_nat its))
                  (1,msat,g,zero mont_limbs,one mont_limbs) in
      let sign := tc_sign_bit machine_wordsize tc_limbs fm in
      let inv := mulmod pc vm in
      let inv := select sign inv (oppmod inv) in
      inv.

    (* Converts a wordsize integer to montgomery domain (without multiplying by R2) *)
    Definition twosc_word_mod_m a :=
      dlet cond := Z.twos_complement_neg machine_wordsize a in
      dlet a_opp := Z.twos_complement_opp machine_wordsize a in
      dlet a_enc := partition (uweight machine_wordsize) mont_limbs a in
      dlet a_opp_enc := partition (uweight machine_wordsize) mont_limbs a_opp in
      dlet a_opp_enc_opp := oppmod (a_opp_enc) in
                              dlet res := select cond a_enc a_opp_enc_opp in res.

    Definition jump_divstep_aux '(d, f, g, v, r) :=
      let '(d1,f1,g1,u1,v1,q1,r1) :=
        fold_right (fun i data => twos_complement_word_full_divstep_aux machine_wordsize data)
                   (d,nth_default 0 f 0,nth_default 0 g 0,1,0,0,1)
                   (seq 0 (Z.to_nat (machine_wordsize - 2))) in
      dlet f2 := word_tc_mul u1 f in
      dlet f3 := word_tc_mul v1 g in
      dlet g2 := word_tc_mul q1 f in
      dlet g3 := word_tc_mul r1 g in
      dlet f4 := tc_add word_tc_mul_limbs f2 f3 in
      dlet g4 := tc_add word_tc_mul_limbs g2 g3 in
      dlet f5 := arithmetic_shiftr f4 (machine_wordsize - 2) in
      dlet g5 := arithmetic_shiftr g4 (machine_wordsize - 2) in
      dlet f6 := firstn tc_limbs f5 in
      dlet g6 := firstn tc_limbs g5 in
      dlet u2 := twosc_word_mod_m u1 in
      dlet v02 := twosc_word_mod_m v1 in
      dlet q2 := twosc_word_mod_m q1 in
      dlet r02 := twosc_word_mod_m r1 in
      dlet v2 := mulmod u2 v in
      dlet v3 := mulmod v02 r in
      dlet r2 := mulmod q2 v in
      dlet r3 := mulmod r02 r in
      dlet v4 := addmod v2 v3 in
      dlet r4 := addmod r2 r3 in
    (d1,f6, g6, v4, r4).

    Definition inner_loop d f g :=
      let '(d1,_,_,u1,v1,q1,r1) := fold_right (fun i data => twos_complement_word_full_divstep_aux machine_wordsize data) (d,nth_default 0 f 0,nth_default 0 g 0,1,0,0,1) (seq 0 (Z.to_nat (machine_wordsize - 2))) in
      (d1, u1, v1, q1, r1).

    Definition inner_loop_hd d f g :=
      let '(d1,_,_,u1,v1,q1,r1) := fold_right (fun i data => twos_complement_word_full_hddivstep_aux machine_wordsize data) (d,nth_default 0 f 0,nth_default 0 g 0,1,0,0,1) (seq 0 (Z.to_nat (machine_wordsize - 2))) in
      (d1, u1, v1, q1, r1).

    Definition update_fg f g u1 v1 q1 r1 :=
      dlet f2 := word_tc_mul u1 f in
      dlet f3 := word_tc_mul v1 g in
      dlet g2 := word_tc_mul q1 f in
      dlet g3 := word_tc_mul r1 g in
      dlet f4 := tc_add word_tc_mul_limbs f2 f3 in
      dlet g4 := tc_add word_tc_mul_limbs g2 g3 in
      dlet f5 := arithmetic_shiftr f4 (machine_wordsize - 2) in
      dlet g5 := arithmetic_shiftr g4 (machine_wordsize - 2) in
      dlet f6 := firstn tc_limbs f5 in
      dlet g6 := firstn tc_limbs g5 in
    (f6, g6).

    Definition update_vr v r u1 v1 q1 r1 :=
      dlet u2 := twosc_word_mod_m u1 in
      dlet v02 := twosc_word_mod_m v1 in
      dlet q2 := twosc_word_mod_m q1 in
      dlet r02 := twosc_word_mod_m r1 in
      dlet v2 := mulmod u2 v in
      dlet v3 := mulmod v02 r in
      dlet r2 := mulmod q2 v in
      dlet r3 := mulmod r02 r in
      dlet v4 := addmod v2 v3 in
      dlet r4 := addmod r2 r3 in
    (v4, r4).

    Definition jump_divstep d f g v r := jump_divstep_aux (d, f, g, v, r).

    Definition jump_divstep_hd d f g (v r : list Z) :=
      let '(d1,f1,g1,u1,v1,q1,r1) := fold_right (fun i data => twos_complement_word_full_hddivstep_aux machine_wordsize data) (d,nth_default 0 f 0,nth_default 0 g 0,1,0,0,1) (seq 0 (Z.to_nat (machine_wordsize - 2))) in
      dlet f2 := word_tc_mul u1 f in
      dlet f3 := word_tc_mul v1 g in
      dlet g2 := word_tc_mul q1 f in
      dlet g3 := word_tc_mul r1 g in
      dlet f4 := tc_add word_tc_mul_limbs f2 f3 in
      dlet g4 := tc_add word_tc_mul_limbs g2 g3 in
      dlet f5 := arithmetic_shiftr f4 (machine_wordsize - 2) in
      dlet g5 := arithmetic_shiftr g4 (machine_wordsize - 2) in
      dlet f6 := firstn tc_limbs f5 in
      dlet g6 := firstn tc_limbs g5 in
      dlet u2 := twosc_word_mod_m u1 in
      dlet v02 := twosc_word_mod_m v1 in
      dlet q2 := twosc_word_mod_m q1 in
      dlet r02 := twosc_word_mod_m r1 in
      dlet v2 := mulmod u2 v in
      dlet v3 := mulmod v02 r in
      dlet r2 := mulmod q2 v in
      dlet r3 := mulmod r02 r in
      dlet v4 := addmod v2 v3 in
      dlet r4 := addmod r2 r3 in
    (d1, f6, g6, v4, r4).

    Definition jumpdivstep_precompmod :=
      let bits := (Z.log2 m) + 1 in
      let jump_its := jump_iterations bits machine_wordsize in
      let total_iterations := jump_its * (machine_wordsize - 2) in
      let k := (m + 1) / 2 in
      let precomp := (Z.modexp k total_iterations m) in
      let RN := (Z.modexp 2 (machine_wordsize * (Z.of_nat mont_limbs) * (jump_its + 3)) m) in
      (RN * precomp) mod m.

    Definition partition_jumpdivstep_precomp :=
      Partition.partition (uweight machine_wordsize) mont_limbs jumpdivstep_precompmod.

    Definition by_inv_jump g :=
      let bits := (Z.log2 m) + 1 in
      let msat := Partition.partition (uweight machine_wordsize) tc_limbs m in
      let jump_its := jump_iterations bits machine_wordsize in
      let total_iterations := jump_its * (machine_wordsize - 2) in
      let pc := partition_jumpdivstep_precomp in
      let '(_, fm, _, vm, _) :=
        fold_left (fun data i => jump_divstep_aux data)
                  (seq 0 (Z.to_nat jump_its))
                  (1,msat,g,zero mont_limbs,one mont_limbs) in
      let sign := tc_sign_bit machine_wordsize tc_limbs fm in
      let inv := mulmod pc vm in
      let inv := select sign inv (oppmod inv) in
      inv.

    Definition jumpdivstep_precompmod_hd :=
      let bits := (Z.log2 m) + 1 in
      let jump_its := ((iterations_hd bits) / (machine_wordsize - 2)) + 1 in
      let total_iterations := jump_its * (machine_wordsize - 2) in
      let k := (m + 1) / 2 in
      let precomp := (Z.modexp k total_iterations m) in
      let RN := (Z.modexp 2 (machine_wordsize * (Z.of_nat mont_limbs) * (jump_its + 3)) m) in
      (RN * precomp) mod m.
  End __.

End WordByWordMontgomery.

Module UnsaturatedSolinas.

  Section __.
    Local Definition zeromod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n 0.
    Local Definition onemod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n 1.
    Local Definition primemod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n (s - Associational.eval c).
    Local Definition bytes_evalmod s := Positional.eval (weight 8 1) (bytes_n s).

    Context (limbwidth_num limbwidth_den : Z)
            (machine_wordsize : Z)
            (s : Z)
            (c : list (Z*Z))
            (n : nat)
            (tc_limbs : nat)
            (word_tc_mul_limbs : nat)
            (idxs : list nat)
            (balance : list Z).
    Notation m := (s - Associational.eval c).

    Local Notation twos_complement_pos' := (Z.twos_complement_pos' machine_wordsize).
    Local Notation twos_complement_opp' := (Z.twos_complement_opp' machine_wordsize).
    Local Notation twos_complement_neg := (Z.twos_complement_neg machine_wordsize).
    Local Notation tc_opp := (tc_opp machine_wordsize tc_limbs).
    Local Notation tc_add := (tc_add machine_wordsize).
    Local Notation arithmetic_shiftr1 := (arithmetic_shiftr1 machine_wordsize tc_limbs).
    Local Notation addmod := (addmod limbwidth_num limbwidth_den n).
    Local Notation carry_mulmod := (carry_mulmod limbwidth_num limbwidth_den s c n idxs).
    Local Notation carrymod := (carrymod limbwidth_num limbwidth_den s c n idxs).
    Local Notation encodemod := (encodemod limbwidth_num limbwidth_den s c n).
    Local Notation oppmod := (oppmod limbwidth_num limbwidth_den n balance).
    Local Notation word_tc_mul := (word_tc_mul machine_wordsize tc_limbs).
    Local Notation arithmetic_shiftr := (arithmetic_shiftr machine_wordsize word_tc_mul_limbs).

    Definition divstep_aux (data : Z * (list Z) * (list Z) * (list Z) * (list Z)) :=
      let '(d,f,g,v,r) := data in
      dlet cond := Z.land (twos_complement_pos' d) (mod2 g) in
      dlet d' := Z.zselect cond d (twos_complement_opp' d) in
      dlet f' := select cond f g in
      dlet g' := select cond g (tc_opp f) in
      dlet v' := select cond v r in
      let v'':= addmod v' v' in
      dlet v''' := carrymod v'' in
      dlet oppv := oppmod v in
      dlet r' := select cond r (carrymod oppv) in
      dlet g0 := mod2 g' in
      let d'' := (d' + 1) mod 2 ^ machine_wordsize in
      dlet f'' := select g0 (zero tc_limbs) f' in
      let g'' := arithmetic_shiftr1 (tc_add tc_limbs g' f'') in
      dlet v'''' := select g0 (zero n) v' in
      let r'' := addmod r' v'''' in
      dlet r''' := carrymod r'' in
      (d'',f',g'',v''',r''').

    Definition divstep d f g v r :=
      divstep_aux (d, f, g, v, r).

    Definition divstep_precompmod :=
      let bits := (Z.log2 m) + 1 in
      let i := iterations bits in
      let k := (m + 1) / 2 in
      (Z.modexp k i m).

    Definition encodemod_divstep_precomp :=
      encodemod divstep_precompmod.

    Definition by_inv g :=
      let bits := (Z.log2 m) + 1 in
      let msat := Partition.partition (uweight machine_wordsize) tc_limbs m in
      let its := iterations bits in
      let pc := encodemod_divstep_precomp in
      let '(_, fm, _, vm, _) :=
        fold_left (fun data i => divstep_aux data)
                  (seq 0 (Z.to_nat its))
                  (1,msat,g,zero n,one n) in
      let sign := tc_sign_bit machine_wordsize tc_limbs fm in
      let inv := carry_mulmod pc vm in
      let oppinv := oppmod inv in
      let inv := select sign inv oppinv in
      carrymod inv.

    Definition word_to_solina a :=
      dlet cond := twos_complement_neg a in
      dlet a_opp := twos_complement_opp' a in
      dlet a_enc := encodemod a in
      dlet a_opp_enc := encodemod (a_opp) in
      dlet a_opp_enc_opp := oppmod (a_opp_enc) in
      dlet a_opp_enc_opp_carry := carrymod a_opp_enc_opp in
      dlet res := select cond a_enc a_opp_enc_opp_carry in res.

    Definition jump_divstep_aux '(d, f, g, v, r) :=
      let '(d1,f1,g1,u1,v1,q1,r1) := fold_right (fun i data => twos_complement_word_full_divstep_aux machine_wordsize data) (d,nth_default 0 f 0,nth_default 0 g 0,1,0,0,1) (seq 0 (Z.to_nat (machine_wordsize - 2))) in
      dlet f2 := word_tc_mul u1 f in
      dlet f3 := word_tc_mul v1 g in
      dlet g2 := word_tc_mul q1 f in
      dlet g3 := word_tc_mul r1 g in
      dlet f4 := tc_add word_tc_mul_limbs f2 f3 in
      dlet g4 := tc_add word_tc_mul_limbs g2 g3 in
      dlet f5 := arithmetic_shiftr f4 (machine_wordsize - 2) in
      dlet g5 := arithmetic_shiftr g4 (machine_wordsize - 2) in
      dlet f6 := firstn tc_limbs f5 in
      dlet g6 := firstn tc_limbs g5 in
      dlet u2 := word_to_solina u1 in
      dlet v02 := word_to_solina v1 in
      dlet q2 := word_to_solina q1 in
      dlet r02 := word_to_solina r1 in
      dlet v2 := carry_mulmod u2 v in
      dlet v3 := carry_mulmod v02 r in
      dlet r2 := carry_mulmod q2 v in
      dlet r3 := carry_mulmod r02 r in
      dlet v4 := addmod v2 v3 in
      dlet v5 := carrymod v4 in
      dlet r4 := addmod r2 r3 in
      dlet r5 := carrymod r4 in
    (d1, f6, g6, v5, r5).

    Definition inner_loop d f g :=
      let '(d1,_,_,u1,v1,q1,r1) := fold_right (fun i data => twos_complement_word_full_divstep_aux machine_wordsize data) (d,nth_default 0 f 0,nth_default 0 g 0,1,0,0,1) (seq 0 (Z.to_nat (machine_wordsize - 2))) in
      (d1, u1, v1, q1, r1).

    Definition inner_loop_hd d f g :=
      let '(d1,_,_,u1,v1,q1,r1) := fold_right (fun i data => twos_complement_word_full_hddivstep_aux machine_wordsize data) (d,nth_default 0 f 0,nth_default 0 g 0,1,0,0,1) (seq 0 (Z.to_nat (machine_wordsize - 2))) in
      (d1, u1, v1, q1, r1).

    Definition update_fg f g u1 v1 q1 r1 :=
      dlet f2 := word_tc_mul u1 f in
      dlet f3 := word_tc_mul v1 g in
      dlet g2 := word_tc_mul q1 f in
      dlet g3 := word_tc_mul r1 g in
      dlet f4 := tc_add word_tc_mul_limbs f2 f3 in
      dlet g4 := tc_add word_tc_mul_limbs g2 g3 in
      dlet f5 := arithmetic_shiftr f4 (machine_wordsize - 2) in
      dlet g5 := arithmetic_shiftr g4 (machine_wordsize - 2) in
      dlet f6 := firstn tc_limbs f5 in
      dlet g6 := firstn tc_limbs g5 in
    (f6, g6).

    Definition update_vr v r u1 v1 q1 r1 :=
      dlet u2 := word_to_solina u1 in
      dlet v02 := word_to_solina v1 in
      dlet q2 := word_to_solina q1 in
      dlet r02 := word_to_solina r1 in
      dlet v2 := carry_mulmod u2 v in
      dlet v3 := carry_mulmod v02 r in
      dlet r2 := carry_mulmod q2 v in
      dlet r3 := carry_mulmod r02 r in
      dlet v4 := addmod v2 v3 in
      dlet v5 := carrymod v4 in
      dlet r4 := addmod r2 r3 in
      dlet r5 := carrymod r4 in
    (v5, r5).

    Definition jump_divstep d f g v r := jump_divstep_aux (d, f, g, v, r).

    Definition jump_divstep_hd d f g (v r : list Z) :=
      let '(d1,f1,g1,u1,v1,q1,r1) := fold_right (fun i data => twos_complement_word_full_hddivstep_aux machine_wordsize data) (d,nth_default 0 f 0,nth_default 0 g 0,1,0,0,1) (seq 0 (Z.to_nat (machine_wordsize - 2))) in
      dlet f2 := word_tc_mul u1 f in
      dlet f3 := word_tc_mul v1 g in
      dlet g2 := word_tc_mul q1 f in
      dlet g3 := word_tc_mul r1 g in
      dlet f4 := tc_add word_tc_mul_limbs f2 f3 in
      dlet g4 := tc_add word_tc_mul_limbs g2 g3 in
      dlet f5 := arithmetic_shiftr f4 (machine_wordsize - 2) in
      dlet g5 := arithmetic_shiftr g4 (machine_wordsize - 2) in
      dlet f6 := firstn tc_limbs f5 in
      dlet g6 := firstn tc_limbs g5 in
      dlet u2 := word_to_solina u1 in
      dlet v02 := word_to_solina v1 in
      dlet q2 := word_to_solina q1 in
      dlet r02 := word_to_solina r1 in
      dlet v2 := carry_mulmod u2 v in
      dlet v3 := carry_mulmod v02 r in
      dlet r2 := carry_mulmod q2 v in
      dlet r3 := carry_mulmod r02 r in
      dlet v4 := addmod v2 v3 in
      dlet v5 := carrymod v4 in
      dlet r4 := addmod r2 r3 in
      dlet r5 := carrymod r4 in
    (d1, f6, g6, v5, r5).

    Definition jumpdivstep_precompmod :=
      let bits := (Z.log2 m) + 1 in
      let jump_its := jump_iterations bits machine_wordsize in
      let total_iterations := jump_its * (machine_wordsize - 2) in
      let k := (m + 1) / 2 in
      let precomp := (Z.modexp k total_iterations m) in
      precomp mod m.

    Definition encodemod_jumpdivstep_precomp :=
      encodemod jumpdivstep_precompmod.

    Definition by_inv_jump g :=
      let bits := (Z.log2 m) + 1 in
      let msat := Partition.partition (uweight machine_wordsize) tc_limbs m in
      let jump_its := jump_iterations bits machine_wordsize in
      let total_iterations := jump_its * (machine_wordsize - 2) in
      let pc := encodemod_jumpdivstep_precomp in
      let '(_, fm, _, vm, _) := fold_left (fun data i => jump_divstep_aux data) (seq 0 (Z.to_nat jump_its))
                                          (1,msat,g,zero n,one n) in
      let sign := tc_sign_bit machine_wordsize tc_limbs fm in
      let inv := carry_mulmod pc vm in
      let inv := select sign inv (oppmod inv) in
      carrymod inv.

    Definition jumpdivstep_precompmod_hd :=
      let bits := (Z.log2 m) + 1 in
      let jump_its := ((iterations_hd bits) / (machine_wordsize - 2)) + 1 in
      let total_iterations := jump_its * (machine_wordsize - 2) in
      let k := (m + 1) / 2 in
      let precomp := (Z.modexp k total_iterations m) in
      precomp mod m.
  End __.

End UnsaturatedSolinas.
