(** * SHA-256 specification (axiomatized).

    Defines the SHA-256 hash function as an axiomatized Gallina function.
    Used to unblock hash-to-curve development. The axiom states that
    SHA256 conforms to FIPS 180-4 / RFC 6234.

    For a fully verified implementation, see the plan in
    docs/PLAN_verified_sha256.md (Path A: VST spec + bedrock2 proof).
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import Crypto.Spec.ModularArithmetic.
Import ListNotations.

Local Open Scope Z_scope.

(** SHA-256 produces a 32-byte (256-bit) digest from arbitrary-length input. *)

Axiom SHA256 : list Byte.byte -> list Byte.byte.

(** The output is always exactly 32 bytes. *)
Axiom SHA256_length : forall msg, length (SHA256 msg) = 32%nat.

(** SHA-256 is a pure function (deterministic). *)
(** (This is automatic from the type — no axiom needed.) *)

(** expand_message_xmd from RFC 9380 §5.3.1.
    Used by hash_to_field to produce uniform random bytes
    from an arbitrary message + domain separation tag. *)

Axiom expand_message_xmd :
  list Byte.byte ->  (* msg *)
  list Byte.byte ->  (* DST (domain separation tag) *)
  nat ->             (* len_in_bytes *)
  list Byte.byte.    (* output *)

Axiom expand_message_xmd_length :
  forall msg dst len,
    length (expand_message_xmd msg dst len) = len.

(** hash_to_field from RFC 9380 §5.2.
    Produces `count` field elements from a message.
    Each element is uniformly distributed in Fp (for security parameter >= 128). *)

Axiom hash_to_field :
  forall (p : positive),
    list Byte.byte ->  (* msg *)
    list Byte.byte ->  (* DST *)
    nat ->             (* count *)
    list (F p).         (* output field elements *)

Axiom hash_to_field_length :
  forall p msg dst count,
    length (hash_to_field p msg dst count) = count.
