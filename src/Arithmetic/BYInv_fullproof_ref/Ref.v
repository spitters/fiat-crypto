Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Odd.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Div.

Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Lemma Nat_iter_S {A} n (f: A -> A) x : Nat.iter (S n) f x = f (Nat.iter n f x).
Proof. reflexivity. Qed.

Definition divstep '(d, f, g) :=
  if Z.odd g
  then if 0 <? d
       then (1 - d, g, (g - f) / 2)
       else (1 + d, f, (g + f) / 2 )
  else (1 + d, f, g / 2 ).

Definition divstep_vr '(d, f, g, v, r) :=
  if Z.odd g
  then if 0 <? d
       then (1 - d, g, (g - f) / 2, 2 * r, r - v)
       else (1 + d, f, (g + f) / 2, 2 * v, r + v)
  else (1 + d, f, g / 2, 2 * v, r).

Definition divstep_vr_mod m '(d, f, g, v, r) :=
  if Z.odd g
  then if 0 <? d
       then (1 - d, g, (g - f) / 2, (2 * r) mod m, (r - v) mod m)
       else (1 + d, f, (g + f) / 2, (2 * v) mod m, (r + v) mod m)
  else (1 + d, f, g / 2, (2 * v) mod m, r mod m).

Definition divstep_uvqr '(d, f, g, u, v, q, r) :=
  if Z.odd g
  then if 0 <? d
       then (1 - d, g, (g - f) / 2, 2 * q, 2 * r, q - u, r - v)
       else (1 + d, f, (g + f) / 2, 2 * u, 2 * v, q + u, r + v)
  else (1 + d, f, g / 2, 2 * u, 2 * v, q, r).

Definition hddivstep_vr_mod m '(d, f, g, v, r) :=
  if Z.odd g
  then if 0 <? d
       then (2 - d, g, (g - f) / 2, (2 * r) mod m, (r - v) mod m)
       else (2 + d, f, (g + f) / 2, (2 * v) mod m, (r + v) mod m)
  else (2 + d, f, g / 2, (2 * v) mod m, r mod m).

Definition hddivstep_uvqr '(d, f, g, u, v, q, r) :=
  if Z.odd g
  then if 0 <? d
       then (2 - d, g, (g - f) / 2, 2 * q, 2 * r, q - u, r - v)
       else (2 + d, f, (g + f) / 2, 2 * u, 2 * v, q + u, r + v)
  else (2 + d, f, g / 2, 2 * u, 2 * v, q, r).

Definition jump_divstep_vr n mw m '(d, f, g, v, r) :=
  let '(d1, f1, g1, u1, v1, q1, r1) := Nat.iter n divstep_uvqr (d, f mod 2 ^ mw, g mod 2 ^ mw, 1, 0, 0, 1) in
  let f1' := (u1 * f + v1 * g) / 2 ^ n in
  let g1' := (q1 * f + r1 * g) / 2 ^ n in
  let v1' := (u1 * v + v1 * r) mod m in
  let r1' := (q1 * v + r1 * r) mod m in
  (d1, f1', g1', v1', r1').

Definition iterations d :=
  if d <? 46 then (49 * d + 80) / 17 else (49 * d + 57) / 17.
Definition iterations_hd d :=
  (45907 * d + 26313) / 19929.

Definition jump_iterations b mw :=
  ((iterations b) / (mw - 2)) + 1.

Definition by_inv_full f g its pc :=
  let '(_, fm, _, vm, _) := Nat.iter its (divstep_vr_mod f) (1, f, g, 0, 1)  in
  let sign := if fm <? 0 then (-1) else 1 in
  sign * pc * vm mod f.

Definition by_inv_ref f g :=
  let bits := Z.log2 f + 1 in
  let i := iterations bits in
  let k := (f + 1) / 2 in
  let pc := (Zpower_nat k (Z.to_nat i)) mod f in
  by_inv_full f g (Z.to_nat i) pc.

Definition by_inv_jump_full f g n mw its pc :=
  let '(_, fm, _, vm, _) := Nat.iter its (jump_divstep_vr n mw f) (1, f, g, 0, 1)  in
  let sign := if fm <? 0 then (-1) else 1 in
  sign * pc * vm mod f.

Definition by_inv_jump_ref f g mw :=
  let bits := (Z.log2 f) + 1 in
  let jump_its := jump_iterations bits mw in
  let total_iterations := jump_its * (mw - 2) in
  let k := (f + 1) / 2 in
  let pc := (Zpower_nat k (Z.to_nat total_iterations)) mod f in
  by_inv_jump_full f g (Z.to_nat (mw - 2)%Z) mw (Z.to_nat jump_its) pc.

Lemma iterations_pos i :
  (0 <= i) -> 0 <= iterations i.
Proof.
  intros.
  unfold iterations.
  destruct (i <? 46).
  - apply Z_div_pos. lia. lia.
  - apply Z_div_pos. lia. lia.
Qed.

Lemma jump_iterations_pos b mw :
  0 <= b -> (0 < mw - 2) -> 0 <= jump_iterations b mw.
Proof.
  intros.
  unfold jump_iterations.
  unshelve epose proof Z.div_pos (iterations b) (mw - 2) _ _.
  apply iterations_pos.
  assumption. assumption.
  lia.
Qed.

Lemma divstep_vr_divstep d f g v r :
  let '(d1, f1, g1, _, _) := divstep_vr (d, f, g, v, r) in
  divstep (d, f, g) = (d1, f1, g1).
Proof. unfold divstep, divstep_vr; destruct (0 <? _), (Z.odd _); reflexivity. Qed.

Lemma iter_divstep_vr_iter_divstep d f g v r n :
  let '(dn, fn, gn, _, _) := Nat.iter n divstep_vr (d, f, g, v, r) in
  Nat.iter n divstep (d, f, g) = (dn, fn, gn).
Proof.
  induction n; simpl. reflexivity.
  destruct (Nat.iter _ _ _) as [[[[? ?] ? ]? ]?].
  rewrite IHn. apply divstep_vr_divstep.
Qed.

Lemma iter_divstep_vr_mod_iter_divstep_uvqr m d f g u2 v1 v2 q2 r1 r2 n :
  let '(d1,f1,g1,_,_) :=
      Nat.iter n (divstep_vr_mod m) (d, f, g, v1, r1) in
  (d1,f1,g1)
  = let '(d2,f2,g2,_,_,_,_) := Nat.iter n divstep_uvqr (d, f, g, u2, v2, q2, r2) in
    (d2,f2,g2).
Proof.
  induction n; simpl.
  - reflexivity.
  - destruct (Nat.iter _ _ _) as [[[[?]?]?]?].
    destruct (Nat.iter _ _ _) as [[[[[[?]?]?]?]?]?].
    rewrite IHn. unfold divstep_vr_mod, divstep_uvqr.
    destruct (0 <? _), (Z.odd _); reflexivity.
Qed.

Lemma iter_divstep_f_odd d f g n
  (fodd : Z.odd f = true) :
  let '(_,f,_) := Nat.iter n divstep (d, f, g) in Z.odd f = true.
Proof.
  induction n; simpl.
  - assumption.
  - unfold divstep.
    destruct (Nat.iter _ _ _) as [[d1 f1] g1].
    destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption.
Qed.

Lemma iter_divstep_vr_mod_f_odd m d f g v r n
  (fodd : Z.odd f = true) :
  let '(_,f,_,_,_) := Nat.iter n (divstep_vr_mod m) (d, f, g, v, r) in Z.odd f = true.
Proof.
  induction n; simpl.
  - assumption.
  - unfold divstep_vr_mod.
    destruct (Nat.iter _ _ _) as [[[[d1 f1]g1]v1]r1].
    destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption.
Qed.

Lemma iter_divstep_uvqr_f_odd d f g u v q r n
  (fodd : Z.odd f = true) :
  let '(_,f,_,_,_,_,_) := Nat.iter n divstep_uvqr (d, f, g, u, v, q, r) in Z.odd f = true.
Proof.
  induction n; simpl.
  - assumption.
  - unfold divstep_uvqr.
    destruct (Nat.iter _ _ _) as [[[[[[d1 f1]g1]u1]v1]q1]r1].
    destruct (0 <? d1); destruct (Z.odd g1) eqn:E; assumption.
Qed.

Lemma divstep_uvqr_important_bits d f f0 g g0 u v q r n k
      (Hk : (0 <= n < k)%nat)
      (fodd : Z.odd f = true)
      (fmod : f mod 2 ^ Z.of_nat k = f0 mod 2 ^ Z.of_nat k)
      (gmod : g mod 2 ^ Z.of_nat k = g0 mod 2 ^ Z.of_nat k) :
  let '(d1,f1,g1,u1,v1,q1,r1) := Nat.iter n divstep_uvqr (d, f,  g,  u, v, q, r) in
  let '(d2,f2,g2,u2,v2,q2,r2) := Nat.iter n divstep_uvqr (d, f0, g0, u, v, q, r) in
  g1 mod 2 ^ (k - n) = g2 mod 2 ^ (k - n) /\
  f1 mod 2 ^ (k - n) = f2 mod 2 ^ (k - n) /\
  d1 = d2 /\
  (u1,v1,q1,r1) = (u2,v2,q2,r2).
Proof.
  induction n.
  - cbn in *. rewrite !Z.sub_0_r. repeat split; assumption.
  - rewrite !Nat_iter_S.
    assert (f0_odd : Z.odd f0 = true).
    { rewrite <- Z.odd_mod2m with (m:=k), <- fmod, Z.odd_mod2m; try assumption; lia. }

    pose proof iter_divstep_uvqr_f_odd d f g u v q r n fodd.
    pose proof iter_divstep_uvqr_f_odd d f0 g0 u v q r n f0_odd.

    destruct (Nat.iter _ _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1].
    destruct (Nat.iter _ _ _) as [[[[[[d2 f2] g2] u2] v2] q2] r2].

    assert (g1 mod 2 ^ (Z.of_nat k - Z.of_nat n) = g2 mod 2 ^ (Z.of_nat k - Z.of_nat n) /\
            f1 mod 2 ^ (Z.of_nat k - Z.of_nat n) = f2 mod 2 ^ (Z.of_nat k - Z.of_nat n) /\
            d1 = d2 /\ (u1, v1, q1, r1) = (u2, v2, q2, r2)) by (apply IHn; lia).

    destruct H1 as [H2 [H3 [H4 H5]]].

    assert (Z.odd g1 = Z.odd g2 /\ d1 = d2) as [].
    { rewrite <- Z.odd_mod2m with (m:=k - n), H2, Z.odd_mod2m by lia; split; reflexivity || lia. }

    unfold divstep_uvqr.
    inversion H5. subst. rewrite H1.

    destruct (0 <? d2); destruct (Z.odd g2) eqn:odd; cbn -[Z.mul Z.add Z.div Z.of_nat].
    + split; [|split;[|split]]; try lia; try congruence.
      * rewrite !Z.mod_pull_div by lia; f_equal.
        replace 2 with (2 ^ 1) at 2 4 by reflexivity. rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat k - S n + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        rewrite <- Zminus_mod_idemp_r, <- Zminus_mod_idemp_l, H2, H3, Zminus_mod_idemp_r, Zminus_mod_idemp_l.
        reflexivity.
      * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H2, Z.mod_pow_same_base_smaller; lia.
    + split; [|split;[|split]]; try lia; try congruence.
      * rewrite !Z.mod_pull_div by lia. f_equal.
        replace 2 with (2 ^ 1) at 2 4 by reflexivity. rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat k - S n + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        apply H2.
      * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H3, Z.mod_pow_same_base_smaller; lia.
    + split; [|split;[|split]]; try lia; try congruence.
      * rewrite !Z.mod_pull_div by lia. f_equal.
        replace 2 with (2 ^ 1) at 2 4 by reflexivity. rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat k - S n + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        rewrite <- Zplus_mod_idemp_r, <- Zplus_mod_idemp_l, H2, H3, Zplus_mod_idemp_r, Zplus_mod_idemp_l.
        reflexivity.
      * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H3, Z.mod_pow_same_base_smaller; lia.
    + split; [|split;[|split]]; try lia; try congruence.
      * rewrite !Z.mod_pull_div by lia. f_equal.
        replace 2 with (2 ^ 1) at 2 4 by reflexivity. rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat k - S n + 1) with (Z.of_nat k - Z.of_nat n) by lia.
        apply H2.
      * rewrite <- Z.mod_pow_same_base_smaller with (n:=(Z.of_nat k - Z.of_nat n)), H3, Z.mod_pow_same_base_smaller; lia.
Qed.

Lemma jump_divstep_lemma m d f g v r n
      (fodd : Z.odd f = true)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m)
  :
    let '(d1, f1, g1, v1, r1) := Nat.iter n (divstep_vr_mod m) (d, f, g, v, r) in
    (d1,2 ^ n * f1,2 ^ n * g1,v1 ,r1)
  = let '(d1', f1', g1', u1', v1', q1', r1') := Nat.iter n divstep_uvqr (d, f, g, 1, 0, 0, 1) in
    (d1', (u1' * f + v1' * g), (q1' * f + r1' * g), (u1' * v + v1' * r) mod m, (q1' * v + r1' * r) mod m).
Proof.
  induction n.
  - cbn -[Z.add Z.mul].
    repeat match goal with
           | [ |- (_, _) = (_, _) ] => apply f_equal2; rewrite ?Z.div_1_r, ?Z.mod_small by lia; try lia
           end.
  - rewrite !Nat_iter_S.
    pose proof iter_divstep_vr_mod_iter_divstep_uvqr m d f g 1 v 0 0 r 1 n.
    pose proof iter_divstep_vr_mod_f_odd m d f g v r n fodd as fodd1.
    destruct (Nat.iter _ _ _) as [[[[d2 f2] g2] v2] r2].
    destruct (Nat.iter _ _ _) as [[[[[[d1 f1] g1] u1] v1] q1] r1].

    replace (Z.of_nat (S n)) with ((Z.of_nat n) + 1) by lia. rewrite Z.pow_add_r by lia.
    replace (2 ^ 1) with 2 by reflexivity.
    unfold divstep_vr_mod, divstep_uvqr.
    inversion H; inversion IHn; subst.
    destruct (0 <? d1); destruct (Z.odd g1) eqn:godd; cbn -[Z.mul Z.add Z.div Z.of_nat];
      repeat match goal with
             | [ |- (_, _) = (_, _) ] => apply f_equal2
             end; try lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, Z.mul_div_eq, Zmod_odd, Z.odd_sub, godd, fodd1; cbn; lia.
    rewrite Zmult_mod_idemp_r. f_equal; lia.
    rewrite Zminus_mod_idemp_r, Zminus_mod_idemp_l. f_equal; lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, Z.mul_div_eq, !Zmod_odd, godd, Z.sub_0_r, <- H6; lia.
    rewrite Zmult_mod_idemp_r. f_equal; lia.
    rewrite Z.mod_mod by lia. f_equal; lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, Z.mul_div_eq, !Zmod_odd, Z.odd_add, godd, fodd1, Z.sub_0_r; lia.
    rewrite Zmult_mod_idemp_r. f_equal; lia.
    rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l. f_equal; lia.
    rewrite <- Z.mul_assoc, Z.mul_comm, Z.mul_div_eq, Zmod_odd, godd, <- H6; lia.
    rewrite Zmult_mod_idemp_r. f_equal; lia.
    rewrite Z.mod_mod by lia. f_equal; lia.
Qed.

Lemma jump_divstep_full m d f f0 g g0 v r n
      (fodd : Z.odd f = true)
      (Hm : 1 < m)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m)
      (Hf : f mod 2 ^ (Z.of_nat (S n)) = f0 mod 2 ^ (Z.of_nat (S n)))
      (Hg : g mod 2 ^ (Z.of_nat (S n)) = g0 mod 2 ^ (Z.of_nat (S n)))
  :
  Nat.iter n (divstep_vr_mod m) (d, f, g, v, r)
  = let '(d1, f1, g1, u1, v1, q1, r1) := Nat.iter n divstep_uvqr (d, f0, g0, 1, 0, 0, 1) in
    let f1' := (u1 * f + v1 * g) / 2 ^ n in
    let g1' := (q1 * f + r1 * g) / 2 ^ n in
    let v1' := (u1 * v + v1 * r) mod m in
    let r1' := (q1 * v + r1 * r) mod m in
    (d1, f1', g1', v1', r1').
Proof.
  assert (f0odd : Z.odd f0 = true).
  { rewrite <- Z.odd_mod2m with (m:=S n), <- Hf, Z.odd_mod2m; try assumption; lia. }

  pose proof jump_divstep_lemma m d f g v r n fodd Hv Hr.
  pose proof divstep_uvqr_important_bits d f f0 g g0 1 0 0 1 n (S n) ltac:(lia) fodd Hf Hg.

  destruct (Nat.iter _ _ _) as [[[[d1 f1] g1] v1] r1].
  destruct (Nat.iter _ _ _) as [[[[[[d1' f1'] g1'] u1'] v1'] q1'] r1'].
  destruct (Nat.iter _ _ _) as [[[[[[d1'' f1''] g1''] u1''] v1''] q1''] r1''].
  destruct H0 as [H1 [H2 [H3 H4]]].

  inversion H; inversion H4; subst.

  apply (f_equal (fun i => Z.div i (2 ^ Z.of_nat n))) in H6.
  apply (f_equal (fun i => Z.div i (2 ^ Z.of_nat n))) in H7.
  rewrite Z.div_mul' in * by (apply Z.pow_nonzero; lia).
  congruence.
Qed.

Lemma jump_divstep_spec mw m d f g v r (n : nat)
      (fodd : Z.odd f = true)
      (Hmw : n < mw)
      (Hm : 1 < m)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m) :
  jump_divstep_vr n mw m (d, f, g, v, r) =
    Nat.iter n (divstep_vr_mod m) (d, f, g, v, r).
Proof.
  symmetry.
  apply jump_divstep_full; try assumption;
    rewrite Z.mod_pow_same_base_smaller; lia.
Qed.

Lemma jump_divstep_vr_invariants (n : nat) mw m d f g v r Kd K
      (f_odd : Z.odd f = true)
      (Hmw : n < mw)
      (Hm : 1 < m)
      (Hd : - Kd < d < Kd)
      (Hf : - K < f < K)
      (Hg : - K < g < K)
      (Hv : 0 <= v < m)
      (Hr : 0 <= r < m) :
  let '(d1,f1,g1,v1,r1) := jump_divstep_vr n mw m (d, f, g, v, r) in
  Z.odd f1 = true
  /\ - (Kd + n) < d1 < Kd + n
  /\ - K < f1 < K
  /\ - K < g1 < K
  /\ 0 <= v1 < m
  /\ 0 <= r1 < m.
Proof.
  rewrite jump_divstep_spec by assumption.
  induction n; simpl; [rewrite Z.add_0_r; easy|].
  specialize (IHn ltac:(lia)).
  destruct Nat.iter as [[[[dn fn]gn]vn]rn].
  destruct IHn as [fn_odd [vn_bounds rn_bounds]]; cbn -[Z.sub Z.of_nat Z.to_nat Z.add Z.mul].
  destruct (Z.odd gn) eqn:E; destruct (0 <? dn);
  repeat match goal with
         | |- 0 <= _ mod _ < _ => apply Z.mod_pos_bound
         | |- _ /\ _ => split
         | |- _ < _ / _ => apply Z.div_lt_lower_bound
         | |- _ / _ < _ => apply Z.div_lt_upper_bound
         | _ => assumption
         | _ => lia
         end.
Qed.

Lemma nat_iter_jump_divstep_vr_mul mw m d f g v r n k q :
  Nat.iter n (jump_divstep_vr k mw m) (d, f, g, v * q mod m, r * q mod m) =
    let '(d1, f1, g1, v1, r1) := Nat.iter n (jump_divstep_vr k mw m) (d, f, g, v mod m, r mod m) in
    (d1, f1, g1, v1 * q mod m, r1 * q mod m).
Proof.
  induction n.
  - simpl. push_Zmod; pull_Zmod. reflexivity.
  -  simpl. rewrite IHn. clear IHn.
     destruct Nat.iter as [[[[d1 f1] g1] r1] v1].
     simpl.
     destruct Nat.iter as [[[[[[dn fn] gn] un] vn] qn] rn].
     repeat match goal with
            | [ |- (_, _) = (_, _) ] => apply f_equal2
            end.
     + reflexivity.
     + reflexivity.
     + reflexivity.
     + push_Zmod; pull_Zmod. apply f_equal2; lia.
     + push_Zmod; pull_Zmod. apply f_equal2; lia.
Qed.
