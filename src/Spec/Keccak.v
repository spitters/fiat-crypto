(** * Keccak-f[1600] and SHAKE-128 — pure Gallina specification.

    Replaces the SHAKE128 axiom with a concrete Definition.
    Only used in proofs (vm_compute); runtime uses Jasmin assembly. *)

From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List Strings.Byte Lia.
Import ListNotations.

(** State: 25 lanes of 64 bits each, stored as flat list of N. *)
Definition state := list N.
Definition zero_state : state := List.repeat 0%N 25.
Definition mask64 : N := N.ones 64.

Definition rotl64 (x : N) (n : N) : N :=
  N.land (N.lor (N.shiftl x n) (N.shiftr x (64 - n))) mask64.

Definition get (s : state) (i : nat) : N := List.nth i s 0%N.

Definition set_at (s : state) (i : nat) (v : N) : state :=
  List.firstn i s ++ [v] ++ List.skipn (S i) s.

(** Round constants (FIPS 202 Table 4). *)
Definition RC : list N :=
  [0x0000000000000001; 0x0000000000008082; 0x800000000000808A;
   0x8000000080008000; 0x000000000000808B; 0x0000000080000001;
   0x8000000080008081; 0x8000000000008009; 0x000000000000008A;
   0x0000000000000088; 0x0000000080008009; 0x000000008000000A;
   0x000000008000808B; 0x800000000000008B; 0x8000000000008089;
   0x8000000000008003; 0x8000000000008002; 0x8000000000000080;
   0x000000000000800A; 0x800000008000000A; 0x8000000080008081;
   0x8000000000008080; 0x0000000080000001; 0x8000000080008008]%N.

(** Rotation offsets r[x+5y] (FIPS 202 Table 2). *)
Definition rho_off : list N :=
  [ 0; 1;62;28;27; 36;44; 6;55;20;  3;10;43;25;39; 41;45;15;21; 8; 18; 2;61;56;14]%N.

(** π permutation: dest index → source index. *)
Definition pi_src : list nat :=
  [0; 6;12;18;24; 3; 9;10;16;22; 1; 7;13;19;20; 4; 5;11;17;23; 2; 8;14;15;21]%nat.

(** θ step. *)
Definition theta (a : state) : state :=
  let c i := N.lxor (get a i) (N.lxor (get a (i+5)) (N.lxor (get a (i+10)) (N.lxor (get a (i+15)) (get a (i+20))))) in
  let d i := N.lxor (c ((i+4) mod 5)) (rotl64 (c ((i+1) mod 5)) 1) in
  List.map (fun i => N.lxor (get a i) (d (i mod 5))) (List.seq 0 25).

(** ρ step: rotate each lane. *)
Definition rho (a : state) : state :=
  List.map (fun i => rotl64 (get a i) (List.nth i rho_off 0%N)) (List.seq 0 25).

(** π step: permute lanes. *)
Definition pi (a : state) : state :=
  List.map (fun i => get a (List.nth i pi_src 0%nat)) (List.seq 0 25).

(** χ step. *)
Definition chi (a : state) : state :=
  List.map (fun i =>
    let x := (i mod 5)%nat in
    let row := (i - x)%nat in
    N.lxor (get a i) (N.land (N.lxor (get a (row + (x+1) mod 5)) mask64)
                              (get a (row + (x+2) mod 5)))) (List.seq 0 25).

(** ι step: XOR round constant into lane 0. *)
Definition iota (a : state) (rc : N) : state :=
  match a with a0 :: rest => N.lxor a0 rc :: rest | _ => a end.

(** One Keccak round. *)
Definition keccak_round (a : state) (rc : N) : state :=
  iota (chi (pi (rho (theta a)))) rc.

(** Keccak-f[1600]: 24 rounds. *)
Definition keccak_f (a : state) : state :=
  List.fold_left keccak_round RC a.

(* ================================================================== *)
(** * Sponge                                                           *)
(* ================================================================== *)

(** Bytes ↔ lanes (little-endian, 8 bytes per lane). *)
Fixpoint bytes_to_lane (bs : list Byte.byte) (shift : N) : N :=
  match bs with
  | [] => 0%N
  | b :: rest => N.lor (N.shiftl (Byte.to_N b) shift) (bytes_to_lane rest (shift + 8))
  end.

Fixpoint to_lanes_aux (fuel : nat) (bs : list Byte.byte) : list N :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match bs with
    | [] => []
    | _ => bytes_to_lane (List.firstn 8 bs) 0 :: to_lanes_aux fuel' (List.skipn 8 bs)
    end
  end.

Definition to_lanes (bs : list Byte.byte) : list N :=
  to_lanes_aux (List.length bs) bs.

Definition lane_to_bytes (v : N) : list Byte.byte :=
  List.map (fun i =>
    match Byte.of_N (N.land (N.shiftr v (N.of_nat (i * 8))) 255) with
    | Some b => b | None => Byte.x00 end) (List.seq 0 8).

Definition lanes_to_bytes (n : nat) (ls : list N) : list Byte.byte :=
  List.firstn n (List.concat (List.map lane_to_bytes ls)).

(** pad10*1 with domain separator. *)
Definition keccak_pad (rate : nat) (dsep : Byte.byte) (msg : list Byte.byte) : list Byte.byte :=
  let q := (rate - (List.length msg mod rate))%nat in
  if Nat.eqb q 1 then
    msg ++ [match Byte.of_N (N.lor (Byte.to_N dsep) 128) with Some b => b | None => Byte.x00 end]
  else
    msg ++ [dsep] ++ List.repeat Byte.x00 (q - 2) ++ [Byte.x80].

(** Absorb one block: XOR rate_lanes into state, then permute. *)
Definition absorb1 (a : state) (block : list N) (rate_lanes : nat) : state :=
  keccak_f (List.map (fun i =>
    if Nat.ltb i rate_lanes
    then N.lxor (get a i) (List.nth i block 0%N)
    else get a i) (List.seq 0 25)).

(** Absorb all blocks. *)
Fixpoint absorb_aux (fuel : nat) (a : state) (lanes : list N) (rl : nat) : state :=
  match fuel with
  | 0 => a
  | S fuel' =>
    match lanes with
    | [] => a
    | _ => absorb_aux fuel' (absorb1 a (List.firstn rl lanes) rl) (List.skipn rl lanes) rl
    end
  end.

Definition absorb (a : state) (lanes : list N) (rl : nat) : state :=
  absorb_aux (List.length lanes) a lanes rl.

(** Squeeze output. *)
Fixpoint squeeze_aux (fuel : nat) (a : state) (rem : nat) (rate : nat) : list Byte.byte :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match rem with
    | 0 => []
    | _ =>
      let blk := lanes_to_bytes rate a in
      if Nat.leb rem rate then List.firstn rem blk
      else blk ++ squeeze_aux fuel' (keccak_f a) (rem - rate) rate
    end
  end.

Definition squeeze (a : state) (rem : nat) (rate : nat) : list Byte.byte :=
  squeeze_aux (S (rem / rate)) a rem rate.

(** Keccak sponge. *)
Definition keccak_sponge (rate : nat) (dsep : Byte.byte)
  (msg : list Byte.byte) (outlen : nat) : list Byte.byte :=
  let padded := keccak_pad rate dsep msg in
  let rl := (rate / 8)%nat in
  let lanes := to_lanes padded in
  let absorbed := absorb zero_state lanes rl in
  squeeze absorbed outlen rate.

(** SHAKE-128: rate = 168, domain separator = 0x1F. *)
Definition SHAKE128 (msg : list Byte.byte) (outlen : nat) : list Byte.byte :=
  keccak_sponge 168 Byte.x1f msg outlen.

(* ================================================================== *)
(** * Length preservation lemmas                                        *)
(* ================================================================== *)

Lemma theta_length : forall a, length (theta a) = 25.
Proof. intro. unfold theta. rewrite List.map_length, List.seq_length. reflexivity. Qed.

Lemma rho_length : forall a, length (rho a) = 25.
Proof. intro. unfold rho. rewrite List.map_length, List.seq_length. reflexivity. Qed.

Lemma pi_length : forall a, length (pi a) = 25.
Proof. intro. unfold pi. rewrite List.map_length, List.seq_length. reflexivity. Qed.

Lemma chi_length : forall a, length (chi a) = 25.
Proof. intro. unfold chi. rewrite List.map_length, List.seq_length. reflexivity. Qed.

Lemma iota_length : forall a rc, length (iota a rc) = length a.
Proof. intros [|a0 rest] rc; simpl; reflexivity. Qed.

Lemma keccak_round_length : forall a rc, length (keccak_round a rc) = 25.
Proof. intros. unfold keccak_round. rewrite iota_length, chi_length. reflexivity. Qed.

Lemma fold_keccak_round_length : forall rcs s,
  length s = 25 -> length (List.fold_left keccak_round rcs s) = 25.
Proof.
  induction rcs; intros s Hs; simpl; [exact Hs|].
  apply IHrcs. apply keccak_round_length.
Qed.

Lemma keccak_f_length : forall s, length (keccak_f s) = 25.
Proof.
  intro s0. unfold keccak_f.
  (* RC is non-empty: fold_left f (x::xs) a = fold_left f xs (f a x) *)
  assert (Hrc : RC = List.hd 0%N RC :: List.tl RC) by reflexivity.
  rewrite Hrc. cbn [List.fold_left].
  apply fold_keccak_round_length. apply keccak_round_length.
Qed.

Lemma lane_to_bytes_length : forall v, length (lane_to_bytes v) = 8.
Proof. intro. unfold lane_to_bytes. rewrite List.map_length, List.seq_length. reflexivity. Qed.

Lemma concat_map_lane_length : forall ls,
  length (List.concat (List.map lane_to_bytes ls)) = (8 * length ls)%nat.
Proof.
  induction ls as [|l ls' IH]; [reflexivity|].
  cbn [List.map List.concat]. rewrite length_app, lane_to_bytes_length, IH. simpl. lia.
Qed.

Lemma firstn_length_le : forall {A} n (l : list A),
  (n <= length l)%nat -> length (List.firstn n l) = n.
Proof.
  intros A n. induction n; intros [|x l'] H; cbn; try reflexivity.
  - inversion H.
  - f_equal. apply IHn. cbn in H. lia.
Qed.

Lemma lanes_to_bytes_length : forall n ls,
  (n <= 8 * length ls)%nat -> length (lanes_to_bytes n ls) = n.
Proof.
  intros. unfold lanes_to_bytes.
  apply firstn_length_le. rewrite concat_map_lane_length. exact H.
Qed.

Lemma absorb1_length : forall a block rl,
  length (absorb1 a block rl) = 25.
Proof.
  intros. unfold absorb1. rewrite keccak_f_length. reflexivity.
Qed.

Lemma absorb_aux_length : forall fuel a lanes rl,
  length a = 25 -> length (absorb_aux fuel a lanes rl) = 25.
Proof.
  induction fuel; intros; simpl; [exact H|].
  destruct lanes; [exact H|].
  apply IHfuel. apply absorb1_length.
Qed.

Lemma squeeze_aux_length : forall fuel a rem rate,
  (0 < rate)%nat -> length a = 25 -> (rate <= 200)%nat ->
  (rem <= fuel * rate)%nat ->
  length (squeeze_aux fuel a rem rate) = rem.
Proof.
  induction fuel; intros a rem rate Hrate Halen Hrate200 Hle; simpl.
  - assert (rem = 0)%nat by lia. subst. reflexivity.
  - destruct rem; [reflexivity|].
    destruct (Nat.leb (S rem) rate) eqn:Hleb.
    + apply Nat.leb_le in Hleb.
      apply firstn_length_le.
      rewrite lanes_to_bytes_length by (rewrite Halen; lia). lia.
    + apply Nat.leb_gt in Hleb.
      rewrite app_length.
      rewrite lanes_to_bytes_length by (rewrite Halen; lia).
      rewrite IHfuel; [lia | exact Hrate | rewrite keccak_f_length; reflexivity | exact Hrate200 | lia].
Qed.

Lemma squeeze_length : forall a rem rate,
  (0 < rate)%nat -> length a = 25 -> (rate <= 200)%nat ->
  length (squeeze a rem rate) = rem.
Proof.
  intros. unfold squeeze. apply squeeze_aux_length; try assumption.
  (* rem ≤ S (rem / rate) * rate *)
  assert (Hrnz : rate <> 0) by lia.
  pose proof (Nat.div_mod_eq rem rate) as Hdm.
  pose proof (Nat.mod_upper_bound rem rate Hrnz).
  (* rem = rate * (rem/rate) + rem mod rate, and rem mod rate < rate *)
  (* S (rem/rate) * rate = rate + rem/rate * rate ≥ rate + (rem - rem mod rate) = rem + (rate - rem mod rate) ≥ rem *)
  nia.
Qed.

Lemma keccak_sponge_length : forall rate dsep msg outlen,
  (0 < rate)%nat -> (rate <= 200)%nat ->
  length (keccak_sponge rate dsep msg outlen) = outlen.
Proof.
  intros. unfold keccak_sponge.
  apply squeeze_length; try assumption.
  apply absorb_aux_length.
  unfold zero_state. rewrite List.repeat_length. reflexivity.
Qed.

Lemma SHAKE128_length : forall msg outlen,
  length (SHAKE128 msg outlen) = outlen.
Proof. intros. unfold SHAKE128. apply keccak_sponge_length; lia. Qed.
