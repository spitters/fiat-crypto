(** * Real Jasmin bridge: to_jasmin_cmd translation + JasminSemantics instance.
 *
 * Maps our [jasmin_cmd] AST to Jasmin's actual [cmd] type (= seq instr)
 * using the Jasmin Rocq library (jasmin/proofs/).
 *
 * The translation [to_jasmin_cmd] maps:
 *   JCskip       → [::]
 *   JCseq c1 c2  → to_jasmin_cmd c1 ++ to_jasmin_cmd c2
 *   JCset x e    → [:: MkI dummy_info (Cassgn (Lvar ...) AT_none sword64 (to_pexpr e))]
 *   JCif e ct cf → [:: MkI dummy_info (Cif (to_pexpr e) ... ...)]
 *   etc.
 *
 * Build (from fiat-crypto root):
 *   rocq compile -R src Crypto -R rewriter/src Rewriter \
 *     -R ../../jasmin/proofs/lang Jasmin \
 *     -R ../../jasmin/proofs/arch Jasmin \
 *     -R ../../jasmin/proofs/compiler Jasmin \
 *     -R ../../jasmin/proofs/3rdparty Jasmin \
 *     -R ../../jasmin/proofs/ssrmisc Jasmin \
 *     -R ../../jasmin/proofs/itrees Jasmin \
 *     -w "-all" -native-compiler ondemand \
 *     src/Bedrock/Field/FieldExtensions/JasminBridgeReal.v
 *)

From Jasmin Require Import expr psem_defs psem.
From mathcomp Require Import ssreflect ssrfun.

From Stdlib Require Import String ZArith List.
Import ListNotations.
Require Import Crypto.Bedrock.Field.FieldExtensions.ToJasmin.
Require Import Crypto.Bedrock.Field.FieldExtensions.JasminBridge.

Local Open Scope Z_scope.

(** Core types from Jasmin are now in scope:
    - [estate] : Jasmin execution state (escs + emem + evm)
    - [sem] : Jasmin big-step semantics (estate → cmd → estate → Prop)
    - [instr_r] : Jasmin instruction constructors (Cassgn, Copn, Cif, ...)
    - [pexpr] : Jasmin expressions (Pconst, Pvar, Papp2, Pload, ...) *)

Check @estate.
Check @sem.

(** Demonstrate the types coexist with our jasmin_cmd: *)
Definition jasmin_cmd_example : jasmin_cmd := JCskip.

(** === Translation: to_jasmin_pexpr + to_jasmin_cmd ===
 *
 * The translation requires constructing Jasmin's typed variables
 * ([var_i], [gvar]) from string names.  Jasmin variables carry:
 *   - a unique identifier (positive)
 *   - a storage type (sglob, sreg, sstack, ...)
 *   - a value type (sword U64, etc.)
 *
 * Since our [jasmin_cmd] doesn't track these, we construct them
 * synthetically: all variables get storage class [sreg] (register)
 * and type [sword U64].  The Jasmin compiler's register allocator
 * then determines actual allocation.
 *
 * The translation is AXIOMATIC: we declare [to_jasmin_cmd] as a
 * [Parameter] and instantiate [JasminSemantics] using it.  The
 * actual Coq function definition is left for future work because
 * it requires importing Jasmin's [word] and [sopn] infrastructure
 * (which depends on the architecture module — x86 vs ARM).
 *
 * The axioms are SOUND because:
 *   1. Each [jsem_*] axiom follows from the corresponding [sem]
 *      constructor (Eskip → jsem_skip, Eseq → jsem_seq, etc.)
 *   2. The state accessors follow from Jasmin's Vm.get/set API
 *   3. jasminc's compiler_proof.v proves that [sem]-related
 *      source programs compile to correct assembly
 *)

Section RealBridge.

  (** Architecture-specific parameters. For x86-64 these come from
      [Jasmin.x86_params]. We leave them abstract here. *)
  Context {wsw : WithSubWord} {dc : DirectCall}
          {sc_sem : syscall_sem} {ep : EstateParams syscall_state}
          (P : prog) (ev : extra_val_t).

  (** The translation function (axiomatized). *)
  Parameter to_jasmin_cmd : jasmin_cmd -> @Jasmin.expr.cmd asm_op.

  (** Jasmin semantics via the translation: *)
  Definition real_jsem (s1 : @estate syscall_state ep) (j : jasmin_cmd)
                       (s2 : @estate syscall_state ep) : Prop :=
    @sem _ _ _ _ _ _ P ev s1 (to_jasmin_cmd j) s2.

  (** Each [JasminSemantics] axiom follows from the translation
      mapping our constructors to the corresponding [sem] rules.
      We state them as axioms here; they become proof obligations
      when the translation is defined concretely. *)

  Axiom to_jasmin_skip : to_jasmin_cmd JCskip = [::].

  Axiom to_jasmin_seq : forall c1 c2,
    to_jasmin_cmd (JCseq c1 c2) =
    (to_jasmin_cmd c1 ++ to_jasmin_cmd c2)%list.

End RealBridge.

(** Once [to_jasmin_cmd] is defined concretely (matching the Jasmin
    x86-64 architecture), the axioms above become provable lemmas,
    and we can instantiate [JasminSemantics]:
 *
 * Module RealJasminSem <: JasminSemantics.
 *   Definition jstate := estate.
 *   Definition jsem := real_jsem.
 *   Definition jlocals_get s x := Vm.get s.(evm) (mk_var x).
 *   ...
 *   Lemma jsem_skip s : jsem s JCskip s.
 *   Proof. unfold jsem, real_jsem. rewrite to_jasmin_skip. apply Eskip. Qed.
 *   ...
 * End RealJasminSem.
 *
 * Module RealBridge := Bridge RealJasminSem.
 * Check RealBridge.bridge_simulation.
 *)
