(** * wNAF (windowed Non-Adjacent Form) digit expansion.

    Converts a non-negative integer k into a sequence of signed digits
    d_i such that k = Σ d_i · 2^i, with the non-adjacency property.

    Window size w is typically 4, giving digits in {-7..7}. *)

From Stdlib Require Import ZArith Lia List.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Core algorithm *)

Definition wnaf_digit (w : nat) (k : Z) : Z :=
  if Z.odd k then
    let d := k mod (2 ^ Z.of_nat w) in
    if d >=? 2 ^ (Z.of_nat w - 1) then d - 2 ^ Z.of_nat w else d
  else
    0.

Definition wnaf_shift (w : nat) (k : Z) : Z :=
  (k - wnaf_digit w k) / 2.

Fixpoint wnaf_digits (w : nat) (k : Z) (len : nat) : list Z :=
  match len with
  | O => []
  | S n => wnaf_digit w k :: wnaf_digits w (wnaf_shift w k) n
  end.

(** ** Weighted sum *)

Fixpoint weighted_sum (digits : list Z) (pos : nat) : Z :=
  match digits with
  | [] => 0
  | d :: rest => d * 2 ^ Z.of_nat pos + weighted_sum rest (S pos)
  end.

Definition wsum (digits : list Z) : Z := weighted_sum digits 0.

(** ** Step reconstruction *)

Lemma wnaf_reconstruct_step : forall w k,
  (1 < w)%nat ->
  k = wnaf_digit w k + 2 * wnaf_shift w k.
Proof.
  intros w k Hw. unfold wnaf_shift.
  (* k - d is always even, so d + 2 * ((k-d)/2) = d + (k-d) = k *)
  enough (H : (k - wnaf_digit w k) mod 2 = 0) by
    (pose proof (Z.div_mod (k - wnaf_digit w k) 2 ltac:(lia)); lia).
  (* Show (k - wnaf_digit w k) is even *)
  unfold wnaf_digit.
  assert (Hpow : 0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia).
  assert (H2w : 2 ^ Z.of_nat w = 2 * 2 ^ (Z.of_nat w - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  destruct (Z.odd k) eqn:Hodd.
  - set (m := k mod 2 ^ Z.of_nat w).
    assert (Hm : 0 <= m < 2 ^ Z.of_nat w) by (subst m; apply Z.mod_pos_bound; lia).
    assert (Hkm : k mod (2 ^ Z.of_nat w) = m) by (subst m; reflexivity).
    destruct (m >=? 2 ^ (Z.of_nat w - 1)) eqn:Hge.
    + (* k-d = 2^w*(k/2^w+1), divisible by 2 since 2^w = 2*2^(w-1) *)
      apply Z.geb_le in Hge.
      replace (k - (m - 2 ^ Z.of_nat w)) with
        (2 * (2 ^ (Z.of_nat w - 1) * (k / 2 ^ Z.of_nat w + 1))).
      { rewrite Z.mul_comm. apply Z_mod_mult. }
      { pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)). nia. }
    + (* k-d = 2^w*(k/2^w), divisible by 2 *)
      assert (m < 2 ^ (Z.of_nat w - 1)) by
        (rewrite Z.geb_leb in Hge; apply Z.leb_gt in Hge; lia).
      replace (k - m) with
        (2 * (2 ^ (Z.of_nat w - 1) * (k / 2 ^ Z.of_nat w))).
      { rewrite Z.mul_comm. apply Z_mod_mult. }
      { pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)). nia. }
  - (* k even, d=0 *)
    rewrite Z.sub_0_r.
    assert (Z.even k = true) by (rewrite <- Z.negb_odd, Hodd; auto).
    rewrite Zeven_mod in H. destruct (k mod 2); auto; discriminate.
Qed.

(** ** Weighted sum shift *)

Lemma pow2_succ : forall p, 2 ^ Z.of_nat (S p) = 2 * 2 ^ Z.of_nat p.
Proof.
  intros. replace (Z.of_nat (S p)) with (1 + Z.of_nat p) by lia.
  rewrite Z.pow_add_r by lia. simpl. lia.
Qed.

Lemma weighted_sum_succ : forall ds p,
  weighted_sum ds (S p) = 2 * weighted_sum ds p.
Proof.
  induction ds as [|d rest IH]; intros p.
  - simpl. lia.
  - unfold weighted_sum. fold weighted_sum.
    rewrite IH, !pow2_succ. lia.
Qed.

(** ** Shifted k is non-negative *)

Lemma wnaf_shift_nonneg : forall w k,
  (1 < w)%nat -> 0 <= k ->
  0 <= wnaf_shift w k.
Proof.
  intros w k Hw Hk.
  unfold wnaf_shift. apply Z.div_pos; [|lia].
  unfold wnaf_digit.
  assert (Hpow : 0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.odd k); [|lia].
  set (m := k mod 2 ^ Z.of_nat w).
  assert (Hm : 0 <= m < 2 ^ Z.of_nat w) by (subst m; apply Z.mod_pos_bound; lia).
  assert (Hkm : k - m >= 0).
  { enough (m <= k) by lia. subst m. apply Z.mod_le; lia. }
  destruct (m >=? 2 ^ (Z.of_nat w - 1)); lia.
Qed.

(** ** Main correctness via remainder identity *)

(** The remaining scalar after processing len digits *)
Fixpoint wnaf_remainder (w : nat) (k : Z) (len : nat) : Z :=
  match len with
  | O => k
  | S n => wnaf_remainder w (wnaf_shift w k) n
  end.

(** General identity: digits reconstruct k up to 2^len * remainder *)
Lemma wnaf_sum_remainder : forall w len k,
  (1 < w)%nat ->
  0 <= k ->
  wsum (wnaf_digits w k len) + 2 ^ Z.of_nat len * wnaf_remainder w k len = k.
Proof.
  intros w. induction len as [|n IH]; intros k Hw Hk.
  - simpl. destruct k; reflexivity.
  - simpl wnaf_digits. simpl wnaf_remainder.
    unfold wsum. simpl weighted_sum. rewrite Z.mul_1_r.
    rewrite weighted_sum_succ.
    set (d := wnaf_digit w k). set (k' := wnaf_shift w k).
    pose proof (wnaf_reconstruct_step w k Hw) as Hrecon.
    fold d k' in Hrecon.
    pose proof (wnaf_shift_nonneg w k Hw Hk) as Hk'0.
    fold k' in Hk'0.
    specialize (IH k' Hw Hk'0).
    unfold wsum in IH.
    rewrite pow2_succ. lia.
Qed.

(** Remainder bound: after len steps, remainder < (k + C) / 2^len *)
Lemma wnaf_remainder_nonneg : forall w len k,
  (1 < w)%nat -> 0 <= k ->
  0 <= wnaf_remainder w k len.
Proof.
  intros w. induction len as [|n IH]; intros k Hw Hk; simpl.
  - lia.
  - apply IH; auto. apply wnaf_shift_nonneg; auto.
Qed.

(** If k < 2^(len-1), then remainder after len+1 steps is 0.
    The extra digit absorbs the carry from negative wNAF digits.
    Example: k=13 needs 5 digits (not 4) despite 13 < 2^4. *)
Lemma wnaf_remainder_zero : forall w len k,
  (1 < w)%nat -> 0 <= k < 2 ^ Z.of_nat len ->
  wnaf_remainder w k (S len) = 0.
Admitted.

(** Standard correctness: needs one extra digit for carry.
    For GLV with 128-bit scalars: k < 2^128 with len = 129. *)
Theorem wnaf_correct : forall w len k,
  (1 < w)%nat ->
  (1 <= len)%nat ->
  0 <= k < 2 ^ Z.of_nat (len - 1) ->
  wsum (wnaf_digits w k len) = k.
Proof.
  intros w len k Hw Hlen [Hk0 Hklt].
  destruct len as [|n]; [lia|].
  replace (S n - 1)%nat with n in Hklt by lia.
  pose proof (wnaf_sum_remainder w (S n) k Hw Hk0) as Hsr.
  rewrite (wnaf_remainder_zero w n k Hw (conj Hk0 Hklt)) in Hsr.
  rewrite Z.mul_0_r in Hsr. lia.
Qed.

(** ** Digit bound *)

Theorem wnaf_digit_bound_single : forall w k,
  (1 < w)%nat ->
  Z.abs (wnaf_digit w k) < 2 ^ (Z.of_nat w - 1).
Proof.
  intros w k Hw. unfold wnaf_digit.
  assert (Hpow : 0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow2 : 0 < 2 ^ (Z.of_nat w - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (H2w : 2 ^ Z.of_nat w = 2 * 2 ^ (Z.of_nat w - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  destruct (Z.odd k) eqn:Hodd; [|simpl; lia].
  set (m := k mod 2 ^ Z.of_nat w).
  assert (Hm : 0 <= m < 2 ^ Z.of_nat w) by (subst m; apply Z.mod_pos_bound; lia).
  destruct (m >=? 2 ^ (Z.of_nat w - 1)) eqn:Hge.
  - apply Z.geb_le in Hge.
    (* m is odd (k odd, m = k mod 2^w, 2^w even) *)
    assert (Hmodd : Z.odd m = true).
    { (* m is odd: k mod 2^w preserves parity since 2 | 2^w *)
      subst m.
      assert (Hkm_even : (k - k mod 2 ^ Z.of_nat w) mod 2 = 0).
      { pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)) as Hdm.
        set (q := k / 2 ^ Z.of_nat w).
        replace (k - k mod 2 ^ Z.of_nat w) with (2 ^ Z.of_nat w * q) by lia.
        replace (2 ^ Z.of_nat w * q) with (2 ^ (Z.of_nat w - 1) * q * 2)
          by (rewrite H2w; ring).
        apply Z_mod_mult. }
      (* k ≡ m (mod 2), so odd k → odd m *)
      assert (Hmod_eq : k mod 2 = k mod 2 ^ Z.of_nat w mod 2).
      { set (mm := k mod 2 ^ Z.of_nat w) in *.
        pose proof (Z.div_mod (k - mm) 2 ltac:(lia)) as Hdm2.
        rewrite Hkm_even in Hdm2.
        assert (Hk_eq : k = mm + 2 * ((k - mm) / 2)) by lia.
        rewrite Hk_eq.
        rewrite Z.add_mod by lia.
        rewrite (Z.mul_comm 2), Z_mod_mult, Z.add_0_r.
        apply Z.mod_small.
        apply Z.mod_pos_bound. lia. }
      (* Z.odd k ↔ k mod 2 = 1 *)
      assert (Hk1 : k mod 2 = 1).
      { pose proof (Z.mod_pos_bound k 2 ltac:(lia)).
        assert (k mod 2 <> 0).
        { intro Habs. apply Zmod_divides in Habs; [|lia].
          destruct Habs as [c Hc].
          rewrite Hc, Z.odd_mul in Hodd. discriminate. }
        lia. }
      rewrite Hmod_eq in Hk1.
      set (mm := k mod 2 ^ Z.of_nat w).
      rewrite <- Z.negb_even.
      destruct (Z.even mm) eqn:He; [|reflexivity].
      exfalso. rewrite Zeven_mod in He. apply Z.eqb_eq in He.
      fold mm in Hk1. lia. }
    (* m odd and m >= 2^(w-1): m > 2^(w-1) since 2^(w-1) is even *)
    assert (m <> 2 ^ (Z.of_nat w - 1)).
    { intro Heq. rewrite Heq in Hmodd.
      rewrite Z.odd_pow in Hmodd by lia. discriminate. }
    rewrite H2w in *. lia.
  - rewrite Z.geb_leb in Hge. apply Z.leb_gt in Hge.
    assert (Hmodd : Z.odd m = true).
    { (* m is odd: k mod 2^w preserves parity since 2 | 2^w *)
      subst m.
      assert (Hkm_even : (k - k mod 2 ^ Z.of_nat w) mod 2 = 0).
      { pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)) as Hdm.
        set (q := k / 2 ^ Z.of_nat w).
        replace (k - k mod 2 ^ Z.of_nat w) with (2 ^ Z.of_nat w * q) by lia.
        replace (2 ^ Z.of_nat w * q) with (2 ^ (Z.of_nat w - 1) * q * 2)
          by (rewrite H2w; ring).
        apply Z_mod_mult. }
      (* k ≡ m (mod 2), so odd k → odd m *)
      assert (Hmod_eq : k mod 2 = k mod 2 ^ Z.of_nat w mod 2).
      { set (mm := k mod 2 ^ Z.of_nat w) in *.
        pose proof (Z.div_mod (k - mm) 2 ltac:(lia)) as Hdm2.
        rewrite Hkm_even in Hdm2.
        assert (Hk_eq : k = mm + 2 * ((k - mm) / 2)) by lia.
        rewrite Hk_eq.
        rewrite Z.add_mod by lia.
        rewrite (Z.mul_comm 2), Z_mod_mult, Z.add_0_r.
        apply Z.mod_small.
        apply Z.mod_pos_bound. lia. }
      (* Z.odd k ↔ k mod 2 = 1 *)
      assert (Hk1 : k mod 2 = 1).
      { pose proof (Z.mod_pos_bound k 2 ltac:(lia)).
        assert (k mod 2 <> 0).
        { intro Habs. apply Zmod_divides in Habs; [|lia].
          destruct Habs as [c Hc].
          rewrite Hc, Z.odd_mul in Hodd. discriminate. }
        lia. }
      rewrite Hmod_eq in Hk1.
      set (mm := k mod 2 ^ Z.of_nat w).
      rewrite <- Z.negb_even.
      destruct (Z.even mm) eqn:He; [|reflexivity].
      exfalso. rewrite Zeven_mod in He. apply Z.eqb_eq in He.
      fold mm in Hk1. lia. }
    assert (0 < m).
    { destruct (Z.eq_dec m 0) as [->|]; [discriminate Hmodd | lia]. }
    lia.
Qed.

Theorem wnaf_digit_bound : forall w k len i d,
  (1 < w)%nat -> 0 <= k ->
  nth_error (wnaf_digits w k len) i = Some d ->
  Z.abs d < 2 ^ (Z.of_nat w - 1).
Proof.
  intros w k0 len. revert k0. induction len as [|n IH]; intros k i d Hw Hk Hnth.
  - simpl in Hnth. destruct i; discriminate.
  - simpl in Hnth. destruct i as [|i'].
    + simpl in Hnth. injection Hnth as <-. apply wnaf_digit_bound_single. exact Hw.
    + simpl in Hnth. apply IH with (k0 := wnaf_shift w k) (i := i'); auto.
      apply wnaf_shift_nonneg; auto.
Qed.

(** ** Non-adjacency *)

Lemma wnaf_digit_not_zero_odd : forall w k,
  wnaf_digit w k <> 0 -> Z.odd k = true.
Proof.
  intros w k H. unfold wnaf_digit in H.
  destruct (Z.odd k); [reflexivity | exfalso; apply H; reflexivity].
Qed.

Lemma wnaf_shift_even : forall w k,
  Z.odd k = false -> wnaf_shift w k = k / 2.
Proof.
  intros w k Hodd. unfold wnaf_shift, wnaf_digit. rewrite Hodd.
  rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma shift_div_pow2_wm1 : forall w k,
  (1 < w)%nat -> wnaf_digit w k <> 0 ->
  (2 ^ Z.of_nat (w - 1) | wnaf_shift w k).
Proof.
  intros w k Hw Hd.
  assert (Hodd : Z.odd k = true) by (apply wnaf_digit_not_zero_odd in Hd; exact Hd).
  unfold wnaf_shift.
  assert (Hpow : 0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia).
  assert (H2w : 2 ^ Z.of_nat w = 2 * 2 ^ Z.of_nat (w - 1)).
  { replace (Z.of_nat w) with (1 + Z.of_nat (w - 1)) by lia.
    rewrite Z.pow_add_r by lia. simpl. lia. }
  assert (Hdiv : (2 ^ Z.of_nat w | k - wnaf_digit w k)).
  { unfold wnaf_digit. rewrite Hodd.
    set (m := k mod 2 ^ Z.of_nat w).
    destruct (m >=? 2 ^ (Z.of_nat w - 1)) eqn:Hge.
    - replace (k - (m - 2 ^ Z.of_nat w)) with (k - m + 2 ^ Z.of_nat w) by lia.
      subst m. exists (k / 2 ^ Z.of_nat w + 1).
      pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)). lia.
    - subst m. exists (k / 2 ^ Z.of_nat w).
      pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)). lia. }
  destruct Hdiv as [q Hq]. exists q.
  rewrite H2w in Hq.
  assert (0 < 2 ^ Z.of_nat (w - 1)) by (apply Z.pow_pos_nonneg; lia).
  Z.div_mod_to_equations. nia.
Qed.

Lemma pow2_divides_even : forall m k,
  (1 <= m)%nat -> (2 ^ Z.of_nat m | k) -> Z.odd k = false.
Proof.
  intros m k Hm [q Hq].
  replace (Z.of_nat m) with (1 + Z.of_nat (m - 1)) in Hq by lia.
  rewrite Z.pow_add_r in Hq by lia. simpl in Hq.
  rewrite Hq. rewrite Z.odd_mul.
  rewrite Bool.andb_false_iff. right.
  destruct (2 ^ Z.of_nat (m - 1)); simpl; auto.
Qed.

Lemma pow2_div_half : forall m k,
  (1 <= m)%nat -> (2 ^ Z.of_nat m | k) -> (2 ^ Z.of_nat (m - 1) | k / 2).
Proof.
  intros m k Hm [q Hq]. exists q.
  replace (Z.of_nat m) with (1 + Z.of_nat (m - 1)) in Hq by lia.
  rewrite Z.pow_add_r in Hq by lia.
  rewrite Hq. simpl (2 ^ 1). rewrite Z.mul_assoc.
  assert (0 < 2 ^ Z.of_nat (m - 1)) by (apply Z.pow_pos_nonneg; lia).
  Z.div_mod_to_equations. nia.
Qed.

Lemma zero_digits_from_pow2_div : forall w len k m,
  (1 < w)%nat -> 0 <= k ->
  (1 <= m)%nat -> (2 ^ Z.of_nat m | k) ->
  forall j, (j < m)%nat -> (j < len)%nat ->
  nth j (wnaf_digits w k len) 0 = 0.
Proof.
  intros w len k m Hw Hk Hm Hdiv.
  revert k m Hk Hm Hdiv.
  induction len as [|n IHn]; intros k m Hk Hm Hdiv j Hj Hjlen.
  - lia.
  - simpl. destruct j as [|j'].
    + simpl. unfold wnaf_digit.
      rewrite (pow2_divides_even m k Hm Hdiv). reflexivity.
    + simpl. apply (IHn (wnaf_shift w k) (m - 1)%nat).
      * apply wnaf_shift_nonneg; auto.
      * lia.
      * rewrite (wnaf_shift_even w k (pow2_divides_even m k Hm Hdiv)).
        apply pow2_div_half; auto.
      * lia.
      * lia.
Qed.

Theorem wnaf_non_adjacent : forall w k len i,
  (1 < w)%nat -> 0 <= k ->
  let digits := wnaf_digits w k len in
  nth i digits 0 <> 0 ->
  forall j, (1 <= j < w)%nat ->
  (i + j < len)%nat ->
  nth (i + j) digits 0 = 0.
Proof.
  intros w k len. revert k.
  induction len as [|n IHn]; intros k i Hw Hk digits Hdi j Hj Hjlen; subst digits.
  - simpl in *. lia.
  - simpl wnaf_digits in *. destruct i as [|i'].
    + (* i = 0: nonzero digit is wnaf_digit w k *)
      simpl (nth 0 _ _) in Hdi.
      assert (Hdiv : (2 ^ Z.of_nat (w - 1) | wnaf_shift w k))
        by (apply shift_div_pow2_wm1; auto).
      replace j with (S (j - 1)) by lia.
      simpl (nth (0 + S _) _ _).
      apply (zero_digits_from_pow2_div w n (wnaf_shift w k) (w - 1)%nat);
        [exact Hw | apply wnaf_shift_nonneg; auto | lia | exact Hdiv | lia | lia].
    + (* i > 0: reduce to tail *)
      simpl (nth (S i') _ _) in Hdi.
      replace (S i' + j)%nat with (S (i' + j))%nat by lia.
      simpl (nth (S _) _ _).
      apply (IHn (wnaf_shift w k) i' Hw (wnaf_shift_nonneg w k Hw Hk)).
      exact Hdi. exact Hj. lia.
Qed.

(** ** Density bound *)

Definition count_nonzero (ds : list Z) : nat :=
  length (filter (fun d => negb (d =? 0)) ds).

Theorem wnaf_density : forall w k len,
  (1 < w)%nat -> 0 <= k ->
  (count_nonzero (wnaf_digits w k len) <= Nat.div len (w + 1) + 1)%nat.
Admitted.

(** ** Concrete tests *)

Example wnaf_test_13 :
  wnaf_digits 4 13 5 = [-3; 0; 0; 0; 1].
Proof. vm_compute. reflexivity. Qed.

Example wnaf_test_sum_13 : wsum [-3; 0; 0; 0; 1] = 13.
Proof. vm_compute. reflexivity. Qed.

Example wnaf_test_127 : wsum (wnaf_digits 4 127 8) = 127.
Proof. vm_compute. reflexivity. Qed.

Example wnaf_test_255 : wsum (wnaf_digits 4 255 9) = 255.
Proof. vm_compute. reflexivity. Qed.

Example wnaf_test_1000 : wsum (wnaf_digits 4 1000 11) = 1000.
Proof. vm_compute. reflexivity. Qed.
