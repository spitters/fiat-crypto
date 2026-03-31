(** * Copy elimination for bedrock2 tower arithmetic.
 *
 * Eliminates the pattern:
 *   stackalloc x N; felem_copy(x, src); ...body using x...
 * Replaces with:
 *   x := src; ...body using x...
 *
 * Sound when body only READS from x (never writes through x),
 * which holds for componentwise tower operations (add, sub, opp).
 *)

Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
From Stdlib Require Import String List ZArith.
Import ListNotations.
Local Open Scope string_scope.

Section CopyElimAST.

  (** Check if a command is felem_copy: cmd.call [] fn [x; src] *)
  Definition is_felem_copy (copy_fns : list string) (c : cmd) : option (string * string) :=
    match c with
    | cmd.call nil fn (expr.var dst :: expr.var src :: nil) =>
        if List.existsb (String.eqb fn) copy_fns then Some (dst, src) else None
    | _ => None
    end.

  (** Eliminate stackalloc+copy patterns.
      Rewrites:  stackalloc x N (seq (call copy [x; src]) rest)
      To:        seq (set x (var src)) rest *)
  Fixpoint elim_copies (copy_fns : list string) (c : cmd) : cmd :=
    match c with
    | cmd.stackalloc x n (cmd.seq copy_call rest) =>
        match is_felem_copy copy_fns copy_call with
        | Some (dst, src) =>
            if String.eqb dst x
            then cmd.seq (cmd.set x (expr.var src)) (elim_copies copy_fns rest)
            else cmd.stackalloc x n (cmd.seq copy_call (elim_copies copy_fns rest))
        | None =>
            cmd.stackalloc x n (cmd.seq (elim_copies copy_fns copy_call)
                                        (elim_copies copy_fns rest))
        end
    | cmd.seq c1 c2 => cmd.seq (elim_copies copy_fns c1) (elim_copies copy_fns c2)
    | cmd.stackalloc x n body => cmd.stackalloc x n (elim_copies copy_fns body)
    | cmd.cond e t f => cmd.cond e (elim_copies copy_fns t) (elim_copies copy_fns f)
    | cmd.while e body => cmd.while e (elim_copies copy_fns body)
    | _ => c
    end.

  (** Apply to a function definition. *)
  Definition elim_copies_func (copy_fns : list string)
      (f : string * (list string * list string * cmd)) :=
    let '(name, (args, rets, body)) := f in
    (name, (args, rets, elim_copies copy_fns body)) : string * (list string * list string * cmd).

  (** Apply to selected functions from a list. *)
  Definition elim_copies_selected (copy_fns safe_fns : list string)
      (fs : list (string * (list string * list string * cmd)))
      : list (string * (list string * list string * cmd)) :=
    List.map (fun f =>
      if List.existsb (String.eqb (fst f)) safe_fns
      then elim_copies_func copy_fns f
      else f) fs.

End CopyElimAST.

Section CopyElimProof.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width}
          {mem : Interface.map.map word Byte.byte}
          {locals : Interface.map.map String.string word}
          {ext_spec : ExtSpec}.
  Let env := Semantics.env.

  (** Memory region equivalence: two maps agree on all keys in [base, base+n). *)
  Definition region_eq (base : word) (n : Z) (m1 m2 : mem) : Prop :=
    forall k, word.unsigned (word.sub k base) < n ->
              Interface.map.get m1 k = Interface.map.get m2 k.

  (** A command is "read-only" on region [base, base+n) if executing it
      does not change the bytes in that region. Formally: for any execution
      that satisfies post, the memory in [base, base+n) is unchanged. *)
  (** A command preserves a memory region: executing it doesn't change
      the bytes in [base, base+n). *)
  Definition cmd_preserves_region (functions : env) (base : word) (n : Z) (c : cmd) : Prop :=
    forall t m l post,
      @exec.exec _ _ _ _ _ _ functions c t m l post ->
      @exec.exec _ _ _ _ _ _ functions c t m l
        (fun t' m' l' => post t' m' l' /\ region_eq base n m m').

  (** The core lemma: if a command is read-only on a region, and two memories
      agree on that region (and everywhere else), then the command produces
      the same result on both memories.

      This is "memory indistinguishability for read-only regions." *)

  (* This requires proving a simulation relation on exec, which is
     non-trivial. The key steps:
     1. Induction on exec derivation
     2. For each constructor, show that loads from the read-only region
        return the same values in both memories
     3. For stores (which by hypothesis don't touch the read-only region),
        the memories diverge only outside the region

     For now, we state the key property and leave it as future work. *)

  (** Simplified correctness statement for practical use.
      For componentwise functions where the safety is obvious from
      the structure, we can state the per-function theorem directly. *)

  (** For a componentwise function f(out, inx, iny) that:
      1. Reads inx[i*stride..(i+1)*stride) and iny[i*stride..(i+1)*stride)
      2. Writes out[i*stride..(i+1)*stride)
      3. For each i independently (no cross-component reads after writes)

      Copy elimination is sound: the function produces the same result
      whether it operates on copies of inx/iny or the originals, EVEN
      when out aliases inx or iny.

      The proof: each sub-operation i reads only from slice i of the input.
      Before sub-operation i executes, slice i of the input has not been
      written (because output slices and input slices at the same index
      don't interact, and previous sub-operations wrote to different
      output slices). Therefore reading from the original gives the
      same value as reading from the copy. *)

  Definition componentwise (stride : Z) (num_components : nat)
      (f : cmd) : Prop :=
    (* f is a sequence of num_components sub-calls, each operating
       on a stride-sized slice at offset i*stride *)
    True. (* Placeholder — the real definition would inspect the AST *)

  (* The per-function approach is more practical: for each function on
     the allowlist, the WP proof without copies is strictly SIMPLER than
     the proof with copies (fewer proof obligations). So we don't need
     a generic simulation theorem — we just prove each optimized function
     directly against its spec. *)

End CopyElimProof.

(** * Correctness theorem (generic).
 *
 * The transformation preserves the operational semantics under the
 * condition that the body does not modify the copied region.
 *
 * Theorem statement (informal):
 *
 *   Let body be a bedrock2 command that reads from address x but never
 *   stores to addresses in [x, x+N). Let copy_fn be a function that
 *   copies N bytes from src to x. Then:
 *
 *     exec(stackalloc x N; copy_fn(x, src); body) post
 *     <->
 *     exec(x := src; body) post
 *
 * Proof sketch:
 *
 * Forward direction (original => optimized):
 *   1. stackalloc gives us: for all fresh mStack with anybytes a N mStack,
 *      the body holds on mCombined = m ∪ mStack.
 *   2. After copy: mStack contains same bytes as src's region in m.
 *   3. body reads from x (= a, pointing to mStack) and gets same values
 *      as reading from src (pointing to m), because the bytes are identical.
 *   4. body doesn't write to [a, a+N), so mStack is unchanged.
 *   5. For the optimized version: x := src makes x point to src's region in m.
 *      body reads from x (= src) and gets the same values as step 3.
 *   6. body's writes to other regions produce the same output.
 *   7. The postconditions match.
 *
 * The backward direction is similar.
 *
 * Key lemma needed: if two memory regions have the same byte contents,
 * then any command that only reads from those regions (and writes elsewhere)
 * produces the same result regardless of which region it reads from.
 * This is a form of "memory indistinguishability" for read-only regions.
 *
 * Formalization status: The AST transformation above is TRUSTED (same status
 * as ToCString.v). The correctness argument is sound but not yet mechanized
 * in Rocq. A full mechanization would require ~300 lines of map reasoning
 * and a formal definition of "read-only on region [a, a+N)".
 *)
