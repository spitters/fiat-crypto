From Stdlib Require Import ZArith Lia List.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF.
Import ListNotations.
Local Open Scope Z_scope.
Section WNAFShamir2.
Context {G : Type}.
Context {add : G -> G -> G} {zero : G} {opp : G -> G}.
Context {mul : Z -> G -> G}.
Context (add_assoc : forall a b c, add a (add b c) = add (add a b) c).
Context (add_comm : forall a b, add a b = add b a).
Context (add_zero_r : forall a, add a zero = a).
Context (add_zero_l : forall a, add zero a = a).
Context (mul_0 : forall P, mul 0 P = zero).
Context (mul_1 : forall P, mul 1 P = P).
Context (mul_add : forall a b P, mul (a + b) P = add (mul a P) (mul b P)).
Context (mul_opp : forall n P, mul (-n) P = opp (mul n P)).
Context (mul_mul : forall a b P, mul a (mul b P) = mul (a * b) P).
Context (mul_distr_add : forall n P Q, mul n (add P Q) = add (mul n P) (mul n Q)).
Context (mul_zero_r : forall n, mul n zero = zero).
Local Infix "+" := add : G_scope.
Local Infix "*" := mul : G_scope.
Local Open Scope G_scope.
