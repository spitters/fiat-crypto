(** * SHA-256 spec + RFC 9380 expand_message_xmd / hash_to_field.

    SHA-256 itself is axiomatized (the only trust assumption);
    expand_message_xmd and hash_to_field are defined as Gallina
    functions on top of SHA-256, following RFC 9380 §5.3.1 and §5.2.

    For a fully verified SHA-256 implementation, see the plan in
    docs/PLAN_verified_sha256.md (Path A: VST spec + bedrock2 proof).
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Strings.Byte.
From Stdlib Require Import Lia.
Require Import Crypto.Spec.ModularArithmetic.
Import ListNotations.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * SHA-256 axiomatization                                           *)
(* ================================================================== *)

(** SHA-256 produces a 32-byte (256-bit) digest from arbitrary-length input. *)
Axiom SHA256 : list Byte.byte -> list Byte.byte.

(** The output is always exactly 32 bytes. *)
Axiom SHA256_length : forall msg, length (SHA256 msg) = 32%nat.

(* ================================================================== *)
(** * Byte string helpers                                              *)
(* ================================================================== *)

(** I2OSP(n, k): integer-to-octet-string primitive (RFC 8017 §4.1).
    Encodes n as a k-byte big-endian octet string. Truncates if n
    doesn't fit in k bytes (caller is responsible for checking). *)
Fixpoint I2OSP_aux (n : nat) (x : N) : list Byte.byte :=
  match n with
  | O => []
  | S n' =>
    let lo := N.land x 255 in
    let hi := N.shiftr x 8 in
    I2OSP_aux n' hi ++
    [match Byte.of_N lo with Some b => b | None => Byte.x00 end]
  end.

Definition I2OSP (x : N) (k : nat) : list Byte.byte := I2OSP_aux k x.

(** strxor: bytewise XOR of two equal-length byte strings.
    Pads with zeros on the right if lengths differ (caller should
    ensure equal lengths). *)
Definition byte_xor (a b : Byte.byte) : Byte.byte :=
  match Byte.of_N (N.lxor (Byte.to_N a) (Byte.to_N b)) with
  | Some c => c
  | None => Byte.x00
  end.

Fixpoint strxor (a b : list Byte.byte) : list Byte.byte :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | a0 :: a', b0 :: b' => byte_xor a0 b0 :: strxor a' b'
  end.

(** Take the first n bytes of a list (pad with zeros if too short). *)
Fixpoint take_bytes (n : nat) (l : list Byte.byte) : list Byte.byte :=
  match n, l with
  | O, _ => []
  | S n', [] => Byte.x00 :: take_bytes n' []
  | S n', x :: l' => x :: take_bytes n' l'
  end.

(** Ceiling division. *)
Definition ceil_div (a b : nat) : nat :=
  Nat.div (a + b - 1) b.

(* ================================================================== *)
(** * expand_message_xmd (RFC 9380 §5.3.1)                              *)
(* ================================================================== *)

(** SHA-256 parameters: output is 32 bytes, block size is 64 bytes. *)
Definition b_in_bytes : nat := 32.
Definition s_in_bytes : nat := 64.

(** DST_prime = DST || I2OSP(len(DST), 1). *)
Definition DST_prime (dst : list Byte.byte) : list Byte.byte :=
  dst ++ I2OSP (N.of_nat (length dst)) 1.

(** msg_prime = Z_pad || msg || l_i_b_str || I2OSP(0, 1) || DST_prime *)
Definition msg_prime (msg : list Byte.byte) (dst : list Byte.byte)
                      (len_in_bytes : nat) : list Byte.byte :=
  let Z_pad := I2OSP 0%N s_in_bytes in
  let l_i_b_str := I2OSP (N.of_nat len_in_bytes) 2 in
  Z_pad ++ msg ++ l_i_b_str ++ I2OSP 0%N 1 ++ DST_prime dst.

(** Compute b_i for i ≥ 1. b_0 is computed separately.
    Recurrence: b_i = SHA256(strxor(b_0, b_{i-1}) || I2OSP(i, 1) || DST_prime).

    We build the list b_1, b_2, ..., b_ell by iterating, carrying b_{i-1}. *)
Fixpoint expand_blocks_aux
  (b0 : list Byte.byte)        (* b_0, fixed *)
  (b_prev : list Byte.byte)    (* b_{i-1} *)
  (dst : list Byte.byte)
  (i : nat)                    (* current index, starting at 1 *)
  (count : nat)                (* number of remaining blocks to produce *)
  : list (list Byte.byte) :=
  match count with
  | O => []
  | S count' =>
    let input :=
      (if Nat.eqb i 1
       then b0
       else strxor b0 b_prev)
      ++ I2OSP (N.of_nat i) 1
      ++ DST_prime dst in
    let b_i := SHA256 input in
    b_i :: expand_blocks_aux b0 b_i dst (S i) count'
  end.

Definition expand_message_xmd
  (msg : list Byte.byte) (dst : list Byte.byte) (len_in_bytes : nat)
  : list Byte.byte :=
  let ell := ceil_div len_in_bytes b_in_bytes in
  let b0 := SHA256 (msg_prime msg dst len_in_bytes) in
  let blocks := expand_blocks_aux b0 [] dst 1 ell in
  take_bytes len_in_bytes (concat blocks).

(* ================================================================== *)
(** * hash_to_field (RFC 9380 §5.2)                                     *)
(* ================================================================== *)

(** L = ceil((ceil(log2(p)) + k) / 8), where k is the security parameter
    (we use k = 128). For BLS12-381 G1: ceil(log2 p) = 381, so L = 64.

    Caller is responsible for passing the correct L for their prime. *)

(** OS2IP: octet-string-to-integer primitive (RFC 8017 §4.2).
    Big-endian decoding of a byte string into a nonnegative integer. *)
Fixpoint OS2IP_aux (acc : N) (l : list Byte.byte) : N :=
  match l with
  | [] => acc
  | b :: l' => OS2IP_aux (N.add (N.shiftl acc 8) (Byte.to_N b)) l'
  end.

Definition OS2IP (l : list Byte.byte) : N := OS2IP_aux 0%N l.

(** Take a sublist [start..start+len) from a byte list. *)
Fixpoint drop_bytes (n : nat) (l : list Byte.byte) : list Byte.byte :=
  match n, l with
  | O, _ => l
  | S _, [] => []
  | S n', _ :: l' => drop_bytes n' l'
  end.

Definition substr (l : list Byte.byte) (start len : nat) : list Byte.byte :=
  take_bytes len (drop_bytes start l).

(** Build a list of `count` field elements from `uniform_bytes` by
    chunking into L-byte blocks and reducing modulo p. *)
Fixpoint build_field_elements
  (p : positive) (uniform : list Byte.byte) (L : nat) (count : nat) (start : nat)
  : list (F p) :=
  match count with
  | O => []
  | S count' =>
    let chunk := substr uniform start L in
    let n := OS2IP chunk in
    F.of_Z p (Z.of_N n)
      :: build_field_elements p uniform L count' (start + L)
  end.

(** hash_to_field for prime fields (m = 1 case of RFC 9380 §5.2).
    The L parameter encodes the per-element output length in bytes;
    for BLS12-381 G1, L = 64 (giving k = 128 bits of security margin). *)
Definition hash_to_field_L
  (p : positive) (L : nat)
  (msg : list Byte.byte) (dst : list Byte.byte) (count : nat)
  : list (F p) :=
  let len_in_bytes := (count * L)%nat in
  let uniform := expand_message_xmd msg dst len_in_bytes in
  build_field_elements p uniform L count 0.

(** Default L for BLS12-381 G1 (and G2). *)
Definition L_bls12_381 : nat := 64.

Definition hash_to_field
  (p : positive)
  (msg : list Byte.byte) (dst : list Byte.byte) (count : nat)
  : list (F p) :=
  hash_to_field_L p L_bls12_381 msg dst count.

(* ================================================================== *)
(** * Length lemmas                                                    *)
(* ================================================================== *)

Lemma I2OSP_aux_length : forall k x, length (I2OSP_aux k x) = k.
Proof.
  induction k as [|k' IH]; intro x; [reflexivity|].
  simpl. rewrite app_length. simpl. rewrite IH. lia.
Qed.

Lemma I2OSP_length : forall x k, length (I2OSP x k) = k.
Proof. intros. apply I2OSP_aux_length. Qed.

Lemma take_bytes_length : forall n l, length (take_bytes n l) = n.
Proof.
  induction n as [|n' IH]; intros [|x l']; simpl;
    try reflexivity; rewrite IH; reflexivity.
Qed.

Lemma expand_message_xmd_length :
  forall msg dst len, length (expand_message_xmd msg dst len) = len.
Proof.
  intros. unfold expand_message_xmd. apply take_bytes_length.
Qed.

Lemma build_field_elements_length :
  forall p uniform L count start,
    length (build_field_elements p uniform L count start) = count.
Proof.
  intros p uniform L count.
  induction count as [|count' IH]; intro start; [reflexivity|].
  simpl. f_equal. apply IH.
Qed.

Lemma hash_to_field_length :
  forall p msg dst count,
    length (hash_to_field p msg dst count) = count.
Proof.
  intros. unfold hash_to_field, hash_to_field_L.
  apply build_field_elements_length.
Qed.
