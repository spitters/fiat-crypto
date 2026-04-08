(** * Real Jasmin bridge — proves Jasmin [psem.sem] imports work.
 *
 * This file demonstrates that our development can successfully
 * import Jasmin's core Coq types ([estate], [sem], [cmd]) and
 * access their fields.  It does NOT yet provide a full
 * [JasminSemantics] instance (that requires a mechanical
 * [to_jasmin_cmd] translation).
 *
 * What it proves: the jasmin-lang Coq library (mathcomp-based)
 * and our bedrock2/fiat-crypto development coexist on the same
 * Rocq loadpath.
 *
 * Build:
 *   rocq compile -R src Crypto -R rewriter/src Rewriter \
 *     -R jasmin/proofs/{lang,arch,compiler,3rdparty,ssrmisc,itrees} Jasmin \
 *     -w "-all" src/Bedrock/Field/FieldExtensions/JasminBridgeReal.v
 *)

From Jasmin Require Import expr psem_defs.
From mathcomp Require Import ssreflect.

From Stdlib Require Import String ZArith.
Require Import Crypto.Bedrock.Field.FieldExtensions.ToJasmin.

Local Open Scope Z_scope.

(** We can reference Jasmin's core types: *)
Check @estate.
Check @Estate.
Check @emem.
Check @evm.

(** And the [sem] inductive from [psem]: *)
From Jasmin Require Import psem.
Check @sem.

(** Demonstrate that our [jasmin_cmd] and Jasmin's types coexist. *)
Definition jasmin_cmd_example : jasmin_cmd := JCskip.

(** The path to a full instantiation:
 *
 * Module RealJasminSem <: JasminBridge.JasminSemantics.
 *   Definition jstate := @estate syscall_state ep.
 *
 *   Fixpoint to_jasmin_cmd (j : jasmin_cmd) : Jasmin.expr.cmd := ...
 *
 *   Definition jsem s1 j s2 := sem P ev s1 (to_jasmin_cmd j) s2.
 *   Definition jlocals_get s x :=
 *     match Vm.get s.(evm) {| ... |} with ... end.
 *   ...
 *   Lemma jsem_skip s : jsem s JCskip s.
 *   Proof. apply Eskip. Qed.
 *   ...
 * End RealJasminSem.
 *
 * Module RealBridge := JasminBridge.Bridge RealJasminSem.
 * (* gives: RealBridge.bridge_simulation *)
 *)
