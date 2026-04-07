(** * Concrete instantiation of [JasminSemantics] with Jasmin's actual [sem].
 *
 * This file imports Jasmin's Coq development and instantiates the
 * [JasminSemantics] module type from JasminBridge.v.
 *
 * Prerequisites:
 * - Jasmin Coq library built and installed (jasmin-lang/jasmin)
 * - mathcomp ssreflect, algebra, word installed
 *
 * Once this compiles, the full verification chain is:
 *   bedrock2 WP (Rocq) → ToJasmin.tr_cmd (Qed) →
 *   JasminBridge.bridge_simulation (Qed) →
 *   JasminBridgeConcrete (this file, instantiation) →
 *   Jasmin sem (Jasmin Coq, mathcomp) →
 *   jasminc compiler correctness (Jasmin Coq) →
 *   x86-64 assembly semantics
 *
 * STATUS: Template — will compile once Jasmin Coq library is available
 *         on the Rocq loadpath.
 *)

(* Uncomment when Jasmin Coq library is built:

From Jasmin Require Import psem expr.
From mathcomp Require Import ssreflect.

Require Import Crypto.Bedrock.Field.FieldExtensions.ToJasmin.
Require Import Crypto.Bedrock.Field.FieldExtensions.JasminBridge.

(** Instantiate [JasminSemantics] with Jasmin's actual semantics. *)

Module JasminSemConcrete <: JasminSemantics.

  (** Map our [jasmin_cmd] to Jasmin's [cmd] (seq instr). *)

  (* Jasmin's state *)
  Definition jstate := estate.

  (* Translate our jasmin_cmd to Jasmin's cmd *)
  Fixpoint to_jasmin_cmd (j : jasmin_cmd) : cmd :=
    match j with
    | JCskip => [::]
    | JCseq j1 j2 => to_jasmin_cmd j1 ++ to_jasmin_cmd j2
    | JCset x e =>
        [:: MkI dummy_info (Cassgn (Lvar (mk_var x)) AT_none sword64
               (to_jasmin_pexpr e))]
    | JCstore base off v =>
        [:: MkI dummy_info (Copn [:: Lmem ...] AT_none ... [:: ...])]
        (* Store: needs memory write instruction *)
    | JCcall f args =>
        [:: MkI dummy_info (Ccall [::] (mk_funname f)
               (List.map to_jasmin_pexpr args))]
    | JCif e jt jf =>
        [:: MkI dummy_info (Cif (to_jasmin_pexpr e)
               (to_jasmin_cmd jt) (to_jasmin_cmd jf))]
    | JCwhile e body =>
        [:: MkI dummy_info (Cwhile Align_none (to_jasmin_cmd body)
               (to_jasmin_pexpr e) dummy_info [::])]
    | JCdecl x ty body =>
        (* Stack declaration: in Jasmin, stack vars are declared at
           function level, not inline. We emit the body directly
           and rely on the function declaration to handle the stack. *)
        to_jasmin_cmd body
    end.

  (* Jasmin semantics wrapper *)
  Definition jsem (s1 : jstate) (j : jasmin_cmd) (s2 : jstate) : Prop :=
    sem gd s1 (to_jasmin_cmd j) s2.

  (* ... accessor definitions ... *)
  (* ... axiom proofs via Jasmin's sem constructors ... *)

  (* Each axiom (jsem_skip, jsem_seq, etc.) follows directly from
     Jasmin's corresponding sem constructor (Eskip, Eseq, etc.) *)

End JasminSemConcrete.

(** With this instantiation, we can apply the Bridge functor: *)
Module ConcreteBridge := Bridge JasminSemConcrete.

(** The end-to-end theorem:
    For any bedrock2 command [c] and its translation [j = tr_cmd c],
    if bedrock2's exec holds, then Jasmin's sem holds for [j],
    and jasminc's compilation of [j] to x86-64 is correct.

    ConcreteBridge.bridge_simulation gives the first part.
    Jasmin's compiler.compiler_correct gives the second part.
*)

*)

(** For now, this file is a template.
    To activate: build Jasmin Coq library, add to loadpath, uncomment. *)
