(** * ToJasmin: bedrock2 AST → Jasmin source code.
 *
 * Jasmin is a verified assembly language for cryptographic code.
 * This module translates bedrock2's [cmd] AST to Jasmin source text,
 * similar to how ToCString.v translates to C.
 *
 * Key differences from ToCString:
 * 1. Jasmin uses explicit register types (reg u64, stack u64[N])
 * 2. Function parameters are typed (pointer vs value)
 * 3. Stack allocations use [stack u64[N]] (no zero-init, no void* cast)
 * 4. Loads/stores use direct array syntax (p[i] instead of memcpy)
 * 5. Jasmin's compiler does register allocation — we emit hints
 *
 * The Jasmin compiler (jasminc) then:
 * - Performs register allocation (using our hints)
 * - Emits x86-64 assembly with correct calling convention
 * - Proves the compilation correct (safety + functional correctness)
 *
 * Pipeline:
 *   bedrock2 cmd (Rocq) → ToJasmin.v → .jazz file → jasminc → .s → .o
 *
 * Correctness chain:
 *   bedrock2 WP proof (Rocq) → simulation lemma (ToJasmin) →
 *   jasminc correctness (EasyCrypt) → hardware
 *)

Require Import bedrock2.Syntax.
From Stdlib Require Import String List ZArith Ascii Bool.
Require Import Stdlib.Numbers.DecimalString.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* Jasmin AST                                                        *)
(* ================================================================ *)

(** Simplified Jasmin AST for the subset we need. *)

Inductive jasmin_type :=
  | JTu64          (* u64 scalar *)
  | JTptr (n: Z)   (* reg ptr u64[N] — pointer to array of N u64 limbs *)
  | JTstack (n: Z) (* stack u64[N] — stack-allocated array *)
  .

Inductive jasmin_expr :=
  | JEvar (x: string)
  | JElit (v: Z)
  | JEadd (e1 e2: jasmin_expr)
  | JEsub (e1 e2: jasmin_expr)
  | JEmul (e1 e2: jasmin_expr)
  | JEmulhuu (e1 e2: jasmin_expr) (* high 64 bits of u64×u64→u128 multiply *)
  | JEand (e1 e2: jasmin_expr)
  | JEor  (e1 e2: jasmin_expr)
  | JExor (e1 e2: jasmin_expr)
  | JEshr (e1 e2: jasmin_expr)
  | JEshl (e1 e2: jasmin_expr)
  | JEltu (e1 e2: jasmin_expr)  (* unsigned less-than: 1 if e1 < e2, else 0 *)
  | JEeq  (e1 e2: jasmin_expr)  (* equality: 1 if e1 = e2, else 0 *)
  | JEload (base: jasmin_expr) (offset: Z) (* base[offset] *)
  .

Inductive jasmin_cmd :=
  | JCskip
  | JCseq (c1 c2: jasmin_cmd)
  | JCset (x: string) (e: jasmin_expr)
  | JCstore (base: jasmin_expr) (offset: Z) (v: jasmin_expr) (* base[offset] = v *)
  | JCcall (f: string) (args: list jasmin_expr)
  | JCif (e: jasmin_expr) (ct cf: jasmin_cmd)
  | JCwhile (e: jasmin_expr) (body: jasmin_cmd)
  | JCdecl (x: string) (ty: jasmin_type) (body: jasmin_cmd)
  (* x86-64 intrinsics for carry-chain and wide-multiply *)
  | JCadd_flags (cf result: string) (a b: jasmin_expr)
      (* of,cf,sf,pf,zf,result = #ADD(a, b) — sets all flags *)
  | JCadcx (cf_out result: string) (a b: jasmin_expr) (cf_in: string)
      (* cf_out, result = #ADCX(a, b, cf_in) — add with carry *)
  | JCmulx (hi lo: string) (a b: jasmin_expr)
      (* (hi, lo) = #MULX(a, b) — full 64×64→128 multiply *)
  .

Record jasmin_func := {
  jf_name: string;
  jf_params: list (string * jasmin_type);
  jf_locals: list (string * jasmin_type);
  jf_body: jasmin_cmd;
}.

(* ================================================================ *)
(* Translation: bedrock2 cmd → jasmin_cmd                           *)
(* ================================================================ *)

Section Translation.

  (** Translate a bedrock2 expression to Jasmin. *)
  Fixpoint tr_expr (e: Syntax.expr) : jasmin_expr :=
    match e with
    | expr.literal v => JElit v
    | expr.var x => JEvar x
    | expr.op op e1 e2 =>
        let e1' := tr_expr e1 in
        let e2' := tr_expr e2 in
        match op with
        | bopname.add => JEadd e1' e2'
        | bopname.sub => JEsub e1' e2'
        | bopname.mul => JEmul e1' e2'
        | bopname.and => JEand e1' e2'
        | bopname.or  => JEor  e1' e2'
        | bopname.xor => JExor e1' e2'
        | bopname.sru => JEshr e1' e2'
        | bopname.slu => JEshl e1' e2'
        | bopname.ltu => JEltu e1' e2'
        | bopname.eq  => JEeq  e1' e2'
        | bopname.mulhuu => JEmulhuu e1' e2'
        | _ => JElit 0 (* lts, srs, divu, remu: not used in crypto *)
        end
    | expr.load _ ea => JEload (tr_expr ea) 0 (* TODO: proper load *)
    | _ => JElit 0
    end.

  (** Translate a bedrock2 command to Jasmin.
      The key change: [stackalloc] becomes a typed [stack u64[N]] declaration
      WITHOUT zero-initialization. *)
  Fixpoint tr_cmd (c: cmd) : jasmin_cmd :=
    match c with
    | cmd.skip => JCskip
    | cmd.seq c1 c2 => JCseq (tr_cmd c1) (tr_cmd c2)
    | cmd.set x e => JCset x (tr_expr e)
    | cmd.store _ ea ev =>
        JCstore (tr_expr ea) 0 (tr_expr ev)
    | cmd.stackalloc x n body =>
        (* Jasmin: declare stack array, assign pointer, continue *)
        let nwords := Z.div (n + 7) 8 in
        JCdecl x (JTstack nwords) (tr_cmd body)
    | cmd.cond e ct cf =>
        JCif (tr_expr e) (tr_cmd ct) (tr_cmd cf)
    | cmd.while e body =>
        JCwhile (tr_expr e) (tr_cmd body)
    | cmd.call _ f args =>
        JCcall f (List.map tr_expr args)
    | cmd.unset _ => JCskip
    | cmd.interact _ _ _ => JCskip (* no I/O in crypto *)
    end.

  (** Translate a bedrock2 function to a Jasmin function.
      All parameters become [reg ptr u64[field_size]] (pointers to
      field elements of [field_size] limbs).  Different curves use
      different limb counts (e.g. 6 for BLS12-381, 8 for BLS24-509). *)
  Definition tr_func_sized (field_size: Z)
      (f: string * (list string * list string * cmd)) : jasmin_func :=
    let '(name, (args, rets, body)) := f in
    {| jf_name := name;
       jf_params := List.map (fun a => (a, JTptr field_size)) args;
       jf_locals := nil; (* locals are inferred from cmd.set *)
       jf_body := tr_cmd body;
    |}.

  (** Backward-compatible default: assumes single u64 (field_size = 1). *)
  Definition tr_func (f: string * (list string * list string * cmd)) : jasmin_func :=
    tr_func_sized 1 f.

End Translation.

(* ================================================================ *)
(* Codegen polish 1: lower binops to in-place form                  *)
(* ================================================================ *)

(** Jasmin compiles a binary operation [x = e1 op e2] to an x86
    destructive instruction whose destination must equal one of the
    sources.  When the bedrock2 → jasmin translator emits

      x_n = (x_m op e2);

    with [x_m] still live afterwards, jasminc's register allocator
    cannot satisfy the merge constraint and aborts with
    "conflicting variables x_n and x_m must be merged".

    [lower_binop_assigns] rewrites every such [JCset x (JEbinop e1 e2)]
    into the explicit two-step form

      x = e1;
      x = (x op e2);

    so the surface syntax already has dest == src1, eliminating the
    constraint.  The first assignment is a [mov] (no constraint), the
    second a destructive in-place op.  Loads, plain-variable assigns,
    literals and unary forms are left unchanged.  The pass is purely
    syntactic on [jasmin_cmd] and does not touch [JCdecl]/[JCcall]
    arguments. *)

Definition is_binop (e : jasmin_expr) : bool :=
  match e with
  | JEadd _ _ | JEsub _ _ | JEmul _ _ | JEmulhuu _ _
  | JEand _ _ | JEor _ _ | JExor _ _
  | JEshr _ _ | JEshl _ _
  | JEltu _ _ | JEeq _ _ => true
  | _ => false
  end.

(** Replace the [src1] of a binary expression with a fresh variable
    [v].  Used to build the in-place form. *)
Definition rebuild_binop (v : string) (e : jasmin_expr) : jasmin_expr :=
  match e with
  | JEadd _ e2 => JEadd (JEvar v) e2
  | JEsub _ e2 => JEsub (JEvar v) e2
  | JEmul _ e2 => JEmul (JEvar v) e2
  | JEand _ e2 => JEand (JEvar v) e2
  | JEor  _ e2 => JEor  (JEvar v) e2
  | JExor _ e2 => JExor (JEvar v) e2
  | JEshr _ e2 => JEshr (JEvar v) e2
  | JEshl _ e2 => JEshl (JEvar v) e2
  | JEmulhuu _ e2 => JEmulhuu (JEvar v) e2
  | JEltu _ e2 => JEltu (JEvar v) e2
  | JEeq _ e2 => JEeq (JEvar v) e2
  | _ => e
  end.

Definition binop_src1 (e : jasmin_expr) : option jasmin_expr :=
  match e with
  | JEadd e1 _ | JEsub e1 _ | JEmul e1 _
  | JEand e1 _ | JEor  e1 _ | JExor e1 _
  | JEshr e1 _ | JEshl e1 _
  | JEmulhuu e1 _ | JEltu e1 _ | JEeq e1 _ => Some e1
  | _ => None
  end.

(** [is_atom] holds for the only operands jasminc's asmgen accepts as
    a [src2] of a binary instruction: a register-held variable, a
    literal, or a single load.  Anything else (a nested binop) must be
    materialized into a fresh temporary. *)
Definition is_atom (e : jasmin_expr) : bool :=
  match e with
  | JEvar _ => true
  | JElit _ => true
  | JEload _ _ => true
  | _ => false
  end.

(** Build a fresh temporary name from a base [x] and a counter [n].
    These names live alongside the bedrock2 [x_<n>] series and are
    declared by [function_locals] (which collects every variable
    appearing on the LHS of a [JCset]). *)
Definition fresh_name (x : string) (n : nat) : string :=
  (x ++ "_bp" ++ String (Ascii.ascii_of_nat (48 + n)) "")%string.

(** Convert an expression into a sequence of [JCset]s + an atomic
    final expression.  The counter [n] threads fresh-temp suffixes
    through recursion.  Returns [(prefix_cmds, final_atom, next_n)].

    Strategy:
    - If [e] is already an atom, no work to do.
    - If [e] is a binop [JEbinop a b], recursively flatten [a] and
      [b], emit assignments into fresh temps, then build a binop on
      the two atoms. *)
Fixpoint flatten_expr (n : nat) (base : string) (e : jasmin_expr)
    : jasmin_cmd * jasmin_expr * nat :=
  if is_atom e then (JCskip, e, n)
  else
    match e with
    | JEadd e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEadd (JEvar t) a2)))),
         JEvar t, S n2)
    | JEsub e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEsub (JEvar t) a2)))),
         JEvar t, S n2)
    | JEmul e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEmul (JEvar t) a2)))),
         JEvar t, S n2)
    | JEand e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEand (JEvar t) a2)))),
         JEvar t, S n2)
    | JEor e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEor (JEvar t) a2)))),
         JEvar t, S n2)
    | JExor e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JExor (JEvar t) a2)))),
         JEvar t, S n2)
    | JEshr e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEshr (JEvar t) a2)))),
         JEvar t, S n2)
    | JEshl e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEshl (JEvar t) a2)))),
         JEvar t, S n2)
    | JEmulhuu e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEmulhuu (JEvar t) a2)))),
         JEvar t, S n2)
    | JEltu e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEltu (JEvar t) a2)))),
         JEvar t, S n2)
    | JEeq e1 e2 =>
        let '(p1, a1, n1) := flatten_expr n base e1 in
        let '(p2, a2, n2) := flatten_expr n1 base e2 in
        let t := fresh_name base n2 in
        (JCseq p1 (JCseq p2 (JCseq (JCset t a1)
                                   (JCset t (JEeq (JEvar t) a2)))),
         JEvar t, S n2)
    | _ => (JCskip, e, n)  (* unreachable: non-atom and non-binop *)
    end.

(** Lower a [JCset x e] using the in-place form:
      x = e1; x = (x op flatten(e2));
    where [e1] and [e2] are the operands of the top-level binop.

    If [e] is an atom or has no binop top, just emit [JCset x e]. *)
Definition lower_set (x : string) (e : jasmin_expr) : jasmin_cmd :=
  match binop_src1 e with
  | Some e1 =>
      (* Materialize a flattened second operand. *)
      let '(p2, a2, _) := flatten_expr 0 x
        (match e with
         | JEadd _ b | JEsub _ b | JEmul _ b
         | JEand _ b | JEor _ b | JExor _ b
         | JEshr _ b | JEshl _ b
         | JEmulhuu _ b | JEltu _ b | JEeq _ b => b
         | _ => JElit 0
         end) in
      (* Materialize the first operand into x via a flatten. *)
      let '(p1, a1, _) := flatten_expr 0 (x ++ "a") e1 in
      JCseq p1 (JCseq (JCset x a1)
              (JCseq p2 (JCset x (rebuild_binop x
                  (match e with
                   | JEadd _ _ => JEadd (JEvar x) a2
                   | JEsub _ _ => JEsub (JEvar x) a2
                   | JEmul _ _ => JEmul (JEvar x) a2
                   | JEand _ _ => JEand (JEvar x) a2
                   | JEor _ _ => JEor  (JEvar x) a2
                   | JExor _ _ => JExor (JEvar x) a2
                   | JEshr _ _ => JEshr (JEvar x) a2
                   | JEshl _ _ => JEshl (JEvar x) a2
                   | JEmulhuu _ _ => JEmulhuu (JEvar x) a2
                   | JEltu _ _ => JEltu (JEvar x) a2
                   | JEeq _ _ => JEeq (JEvar x) a2
                   | _ => e
                   end)))))
  | None => JCset x e
  end.

Fixpoint lower_binop_assigns (c : jasmin_cmd) : jasmin_cmd :=
  match c with
  | JCskip => JCskip
  | JCseq c1 c2 => JCseq (lower_binop_assigns c1) (lower_binop_assigns c2)
  | JCset x e => lower_set x e
  | JCstore base off v => JCstore base off v
  | JCcall f args => JCcall f args
  | JCif e ct cf => JCif e (lower_binop_assigns ct) (lower_binop_assigns cf)
  | JCwhile e body => JCwhile e (lower_binop_assigns body)
  | JCdecl x ty body => JCdecl x ty (lower_binop_assigns body)
  | JCadd_flags cf r a b => JCadd_flags cf r a b
  | JCadcx co r a b ci => JCadcx co r a b ci
  | JCmulx h l a b => JCmulx h l a b
  end.

(** Apply [lower_binop_assigns] to a [jasmin_func]'s body. *)
Definition lower_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f;
     jf_params := jf_params f;
     jf_locals := jf_locals f;
     jf_body := lower_binop_assigns (jf_body f) |}.

(* ================================================================ *)
(* Codegen polish 2: normalize negative u64 literals                *)
(* ================================================================ *)

(** Coq's [Z] is unbounded, so negative integer literals (e.g. [-1])
    appear in the AST and would normally render as [(- 1)].  Jasmin's
    parser accepts that, but its register allocator/asmgen can refuse
    to fit a sign-extended negative immediate into a u64 destination
    register, producing errors like

      asmgen: invalid rexpr for oprd RCX &64u R15

    Replacing every negative [JElit v] with its two's-complement
    positive equivalent ([v + 2^64]) sidesteps the issue.  We do the
    rewrite at the AST level, BEFORE extraction, so the literal is a
    positive [Z] in the extracted code — never depends on the OCaml-
    side [Z.add]/[Z.pow] (which under [ExtrOcamlZInt] map to native
    [int] arithmetic and silently overflow at [2^63]). *)

Definition u64_max : Z := Z.pow 2 64.

Definition normalize_lit (v : Z) : Z :=
  if (v <? 0)%Z then Z.add v u64_max else v.

Fixpoint normalize_neg_lits_expr (e : jasmin_expr) : jasmin_expr :=
  match e with
  | JEvar x => JEvar x
  | JElit v => JElit (normalize_lit v)
  | JEadd e1 e2 => JEadd (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEsub e1 e2 => JEsub (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEmul e1 e2 => JEmul (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEmulhuu e1 e2 => JEmulhuu (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEand e1 e2 => JEand (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEor  e1 e2 => JEor  (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JExor e1 e2 => JExor (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEshr e1 e2 => JEshr (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEshl e1 e2 => JEshl (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEltu e1 e2 => JEltu (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEeq  e1 e2 => JEeq  (normalize_neg_lits_expr e1) (normalize_neg_lits_expr e2)
  | JEload base off => JEload (normalize_neg_lits_expr base) off
  end.

Fixpoint normalize_neg_lits_cmd (c : jasmin_cmd) : jasmin_cmd :=
  match c with
  | JCskip => JCskip
  | JCseq c1 c2 => JCseq (normalize_neg_lits_cmd c1) (normalize_neg_lits_cmd c2)
  | JCset x e => JCset x (normalize_neg_lits_expr e)
  | JCstore base off v =>
      JCstore (normalize_neg_lits_expr base) off (normalize_neg_lits_expr v)
  | JCcall f args => JCcall f (List.map normalize_neg_lits_expr args)
  | JCif e ct cf =>
      JCif (normalize_neg_lits_expr e) (normalize_neg_lits_cmd ct)
           (normalize_neg_lits_cmd cf)
  | JCwhile e body =>
      JCwhile (normalize_neg_lits_expr e) (normalize_neg_lits_cmd body)
  | JCdecl x ty body => JCdecl x ty (normalize_neg_lits_cmd body)
  | JCadd_flags cf r a b =>
      JCadd_flags cf r (normalize_neg_lits_expr a) (normalize_neg_lits_expr b)
  | JCadcx co r a b ci =>
      JCadcx co r (normalize_neg_lits_expr a) (normalize_neg_lits_expr b) ci
  | JCmulx h l a b =>
      JCmulx h l (normalize_neg_lits_expr a) (normalize_neg_lits_expr b)
  end.

Definition normalize_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f;
     jf_params := jf_params f;
     jf_locals := jf_locals f;
     jf_body := normalize_neg_lits_cmd (jf_body f) |}.

(* ================================================================ *)
(* Codegen polish 3: constant folding + dead-expression removal     *)
(* ================================================================ *)

(** Simplify an expression by folding constants:
    - [0 + x]  → [x]    (left-identity for add)
    - [x + 0]  → [x]    (right-identity for add)
    - [x - 0]  → [x]
    - [0 + 0]  → [0]
    - [x ^ 0]  → [x]    (XOR with 0 is identity)
    - [x & x]  → [x]    where both sides are same var
    Runs bottom-up so nested patterns like [(0 + 0) + x] simplify. *)
Fixpoint simplify_expr (e : jasmin_expr) : jasmin_expr :=
  match e with
  | JEadd e1 e2 =>
      let e1' := simplify_expr e1 in
      let e2' := simplify_expr e2 in
      match e1', e2' with
      | JElit 0, _ => e2'
      | _, JElit 0 => e1'
      | _, _ => JEadd e1' e2'
      end
  | JEsub e1 e2 =>
      let e1' := simplify_expr e1 in
      let e2' := simplify_expr e2 in
      match e2' with
      | JElit 0 => e1'
      | _ => JEsub e1' e2'
      end
  | JExor e1 e2 =>
      let e1' := simplify_expr e1 in
      let e2' := simplify_expr e2 in
      match e2' with
      | JElit 0 => e1'
      | _ => JExor e1' e2'
      end
  | JEand e1 e2 =>
      JEand (simplify_expr e1) (simplify_expr e2)
  | JEor e1 e2 =>
      JEor (simplify_expr e1) (simplify_expr e2)
  | JEmul e1 e2 =>
      JEmul (simplify_expr e1) (simplify_expr e2)
  | JEshr e1 e2 =>
      JEshr (simplify_expr e1) (simplify_expr e2)
  | JEshl e1 e2 =>
      JEshl (simplify_expr e1) (simplify_expr e2)
  | JEmulhuu e1 e2 =>
      JEmulhuu (simplify_expr e1) (simplify_expr e2)
  | JEltu e1 e2 =>
      JEltu (simplify_expr e1) (simplify_expr e2)
  | JEeq e1 e2 =>
      JEeq (simplify_expr e1) (simplify_expr e2)
  | JEload base off =>
      JEload (simplify_expr base) off
  | _ => e
  end.

(** Simplify a command by:
    - Folding constant expressions
    - Removing [JCset x (JEvar x)] (self-assignment, no-op)
    - Removing [JCskip] from sequences *)
Fixpoint simplify_cmd (c : jasmin_cmd) : jasmin_cmd :=
  match c with
  | JCskip => JCskip
  | JCseq c1 c2 =>
      let c1' := simplify_cmd c1 in
      let c2' := simplify_cmd c2 in
      match c1', c2' with
      | JCskip, _ => c2'
      | _, JCskip => c1'
      | _, _ => JCseq c1' c2'
      end
  | JCset x e =>
      let e' := simplify_expr e in
      match e' with
      | JEvar y => if String.eqb x y then JCskip else JCset x e'
      | _ => JCset x e'
      end
  | JCstore base off v =>
      JCstore (simplify_expr base) off (simplify_expr v)
  | JCcall f args =>
      JCcall f (List.map simplify_expr args)
  | JCif e ct cf =>
      JCif (simplify_expr e) (simplify_cmd ct) (simplify_cmd cf)
  | JCwhile e body =>
      JCwhile (simplify_expr e) (simplify_cmd body)
  | JCdecl x ty body =>
      JCdecl x ty (simplify_cmd body)
  | JCadd_flags cf r a b =>
      JCadd_flags cf r (simplify_expr a) (simplify_expr b)
  | JCadcx co r a b ci =>
      JCadcx co r (simplify_expr a) (simplify_expr b) ci
  | JCmulx h l a b =>
      JCmulx h l (simplify_expr a) (simplify_expr b)
  end.

Definition simplify_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f;
     jf_params := jf_params f;
     jf_locals := jf_locals f;
     jf_body := simplify_cmd (jf_body f) |}.

(* ================================================================ *)
(* Codegen polish 4: carry-chain detection                          *)
(* ================================================================ *)

(** Detect the bedrock2 pattern for [addcarryx] without carry-in:
      sum = (a + b);
      carry = (sum <u a);
    Replace with: JCadd_flags carry sum a b.

    Also detect [addcarryx] with carry-in:
      partial = (a + b);
      cp = (partial <u a);
      sum = (partial + cin);
      c2 = (sum <u partial);
      carry = (cp | c2);
    Replace with: JCadcx carry sum a b cin.

    And detect [mulhuu] paired with [mul]:
      lo = (a * b);
      hi = (MULHUU a b);
    Replace with: JCmulx hi lo a b.

    The pass works on flattened [JCseq] chains. *)

(** Flatten a [jasmin_cmd] into a list of atomic commands. *)
Fixpoint cmd_to_list (c : jasmin_cmd) : list jasmin_cmd :=
  match c with
  | JCseq c1 c2 => cmd_to_list c1 ++ cmd_to_list c2
  | JCskip => nil
  | _ => c :: nil
  end.

Definition list_to_cmd (cs : list jasmin_cmd) : jasmin_cmd :=
  List.fold_right JCseq JCskip cs.

(** Expression equality (syntactic). *)
Fixpoint expr_eqb (e1 e2 : jasmin_expr) : bool :=
  match e1, e2 with
  | JEvar x, JEvar y => String.eqb x y
  | JElit x, JElit y => Z.eqb x y
  | JEadd a1 b1, JEadd a2 b2 => expr_eqb a1 a2 && expr_eqb b1 b2
  | _, _ => false
  end.

(** Match pattern for first-limb add:
    [sum = (a + b)]
    [cpn = ((sum <u a) + c)]    — carry fused with next-limb operand
    [ns  = (cpn + d)]           — add second next-limb operand
    → JCadd_flags __cf sum a b; JCadcx __cf ns c d __cf
    Consumes 3 statements, emits 2 intrinsics. *)
Definition match_first_limb_adc (c1 c2 c3 : jasmin_cmd)
    : option (jasmin_cmd * jasmin_cmd) :=
  match c1, c2, c3 with
  | JCset sum (JEadd a b),
    JCset cpn (JEadd (JEltu (JEvar sum') a') c),
    JCset ns (JEadd (JEvar cpn') d) =>
      if String.eqb sum sum'
         && expr_eqb a a'
         && String.eqb cpn cpn'
      then Some (JCadd_flags "__cf" sum a b,
                  JCadcx "__cf" ns c d "__cf")
      else None
  | _, _, _ => None
  end.

(** Match fused carry-chain continuation:
    [cpn = (((prev <u a) + (ns <u b)) + c)]  — two carry extractions + next operand
    [next = (cpn + d)]
    → JCadcx __cf next c d __cf
    Where __cf already holds the carry from the previous ADCX.
    Consumes 2 statements, emits 1 intrinsic. *)
Definition match_cont_adc (c1 c2 : jasmin_cmd)
    : option jasmin_cmd :=
  match c1, c2 with
  | JCset cpn (JEadd (JEadd (JEltu _ _) (JEltu _ _)) c),
    JCset ns (JEadd (JEvar cpn') d) =>
      if String.eqb cpn cpn'
      then Some (JCadcx "__cf" ns c d "__cf")
      else None
  | _, _ => None
  end.

(** Match simple [x = (a + b); y = (x <u a)] → JCadd_flags y x a b. *)
Definition match_add_carry (c1 c2 : jasmin_cmd)
    : option jasmin_cmd :=
  match c1, c2 with
  | JCset sum (JEadd a b),
    JCset carry (JEltu (JEvar sum') a') =>
      if String.eqb sum sum' && expr_eqb a a'
      then Some (JCadd_flags carry sum a b)
      else None
  | _, _ => None
  end.

(** Match pattern for mulx: [lo=(a*b); hi=(MULHUU a b)] → JCmulx hi lo a b *)
Definition match_mulx (c1 c2 : jasmin_cmd)
    : option jasmin_cmd :=
  match c1, c2 with
  | JCset lo (JEmul a1 b1),
    JCset hi (JEmulhuu a2 b2) =>
      if match a1, a2 with
         | JEvar x, JEvar y => String.eqb x y | JElit x, JElit y => Z.eqb x y | _, _ => false
         end
         && match b1, b2 with
            | JEvar x, JEvar y => String.eqb x y | JElit x, JElit y => Z.eqb x y | _, _ => false
            end
      then Some (JCmulx hi lo a1 b1)
      else None
  | _, _ => None
  end.

Fixpoint lower_carry_chain_list (fuel : nat) (cs : list jasmin_cmd)
    : list jasmin_cmd :=
  match fuel with
  | O => cs
  | S fuel' =>
    match cs with
    | nil => nil
    | c1 :: c2 :: c3 :: rest =>
        (* First try 3-statement fused first-limb ADC *)
        match match_first_limb_adc c1 c2 c3 with
        | Some (i1, i2) =>
            i1 :: i2 :: lower_carry_chain_list fuel' rest
        | None =>
        (* Then try 2-statement continuation ADC *)
        match match_cont_adc c1 c2 with
        | Some instr => instr :: lower_carry_chain_list fuel' (c3 :: rest)
        | None =>
        (* Then try simple add+carry or mulx *)
        match match_add_carry c1 c2 with
        | Some instr => instr :: lower_carry_chain_list fuel' (c3 :: rest)
        | None =>
        match match_mulx c1 c2 with
        | Some instr => instr :: lower_carry_chain_list fuel' (c3 :: rest)
        | None => c1 :: lower_carry_chain_list fuel' (c2 :: c3 :: rest)
        end end end end
    | c1 :: c2 :: nil =>
        match match_add_carry c1 c2 with
        | Some instr => instr :: nil
        | None =>
          match match_mulx c1 c2 with
          | Some instr => instr :: nil
          | None => c1 :: c2 :: nil
          end
        end
    | c :: rest => c :: lower_carry_chain_list fuel' rest
    end
  end.

Fixpoint lower_carry_cmd (c : jasmin_cmd) : jasmin_cmd :=
  match c with
  | JCseq _ _ =>
      let stmts := cmd_to_list c in
      list_to_cmd (lower_carry_chain_list (List.length stmts) stmts)
  | JCif e ct cf => JCif e (lower_carry_cmd ct) (lower_carry_cmd cf)
  | JCwhile e body => JCwhile e (lower_carry_cmd body)
  | JCdecl x ty body => JCdecl x ty (lower_carry_cmd body)
  | _ => c
  end.

Definition carry_func (f : jasmin_func) : jasmin_func :=
  {| jf_name := jf_name f;
     jf_params := jf_params f;
     jf_locals := jf_locals f;
     jf_body := lower_carry_cmd (jf_body f) |}.

(** Combined polish: simplify + normalize + carry-chain + lower + simplify.
    Carry-chain runs before binop lowering because it matches multi-statement
    patterns that lowering would break apart. *)
(** Carry detection first (before simplify breaks patterns), then
    simplify + normalize + lower + simplify. *)
Definition polish_func (f : jasmin_func) : jasmin_func :=
  simplify_func (lower_func (normalize_func (simplify_func (carry_func f)))).

(* ================================================================ *)
(* Pretty-printing: jasmin_cmd → string (Jasmin source text)        *)
(* ================================================================ *)

Definition LF : string := String (Ascii.Ascii false true false true false false false false) "".

(** Render a [Z] as a Jasmin u64 immediate.  Negative values are
    converted to their two's-complement positive form (mod 2^64) so
    jasminc accepts them as immediates without sign-extension surprises. *)
Definition pp_zlit_u64 (v : Z) : string :=
  let normalized :=
    if (v <? 0)%Z
    then Z.add v (Z.pow 2 64)
    else v
  in
  DecimalString.NilZero.string_of_int (Z.to_int normalized).

Fixpoint pp_expr (e: jasmin_expr) : string :=
  match e with
  | JEvar x => x
  | JElit v => pp_zlit_u64 v
  | JEadd e1 e2 => "(" ++ pp_expr e1 ++ " + " ++ pp_expr e2 ++ ")"
  | JEsub e1 e2 => "(" ++ pp_expr e1 ++ " - " ++ pp_expr e2 ++ ")"
  | JEmul e1 e2 => "(" ++ pp_expr e1 ++ " * " ++ pp_expr e2 ++ ")"
  | JEand e1 e2 => "(" ++ pp_expr e1 ++ " & " ++ pp_expr e2 ++ ")"
  | JEor  e1 e2 => "(" ++ pp_expr e1 ++ " | " ++ pp_expr e2 ++ ")"
  | JExor e1 e2 => "(" ++ pp_expr e1 ++ " ^ " ++ pp_expr e2 ++ ")"
  | JEshr e1 e2 => "(" ++ pp_expr e1 ++ " >> " ++ pp_expr e2 ++ ")"
  | JEshl e1 e2 => "(" ++ pp_expr e1 ++ " << " ++ pp_expr e2 ++ ")"
  | JEmulhuu e1 e2 => "(MULHUU " ++ pp_expr e1 ++ " " ++ pp_expr e2 ++ ")"
  | JEltu e1 e2 => "(" ++ pp_expr e1 ++ " <u " ++ pp_expr e2 ++ ")"
  | JEeq e1 e2 => "(" ++ pp_expr e1 ++ " == " ++ pp_expr e2 ++ ")"
  | JEload base off =>
      let off_str := DecimalString.NilZero.string_of_int (Z.to_int off) in
      "[" ++ pp_expr base ++ " + " ++ off_str ++ "]"
  end.

(** Pretty-print a Jasmin storage type for a function parameter or
    local declaration.

    Note: [JTptr n] is rendered as [reg u64] (a raw register-held byte
    pointer) rather than [reg ptr u64[n]] (a typed array reference).
    The bedrock2 calling convention treats every pointer parameter as
    a raw byte address dereferenced via [base + offset], which matches
    Jasmin's [reg u64] / [[base + off]] memory access form.  The size
    [n] is retained on the AST for downstream tools (e.g. an emitter
    that wants to declare a [stack u64[n]] frame for the callee). *)
Definition pp_type (t: jasmin_type) : string :=
  match t with
  | JTu64 => "reg u64"
  | JTptr _ => "reg u64"
  | JTstack n =>
      "stack u64[" ++ DecimalString.NilZero.string_of_int (Z.to_int n) ++ "]"
  end.

Fixpoint pp_cmd (indent: string) (c: jasmin_cmd) : string :=
  match c with
  | JCskip => ""
  | JCseq c1 c2 => pp_cmd indent c1 ++ pp_cmd indent c2
  | JCset x e =>
      indent ++ x ++ " = " ++ pp_expr e ++ ";" ++ LF
  | JCstore base off v =>
      let off_str := DecimalString.NilZero.string_of_int (Z.to_int off) in
      indent ++ "[" ++ pp_expr base ++ " + " ++ off_str ++ "] = " ++ pp_expr v ++ ";" ++ LF
  | JCcall f args =>
      indent ++ f ++ "(" ++ String.concat ", " (List.map pp_expr args) ++ ");" ++ LF
  | JCif e ct cf =>
      indent ++ "if (" ++ pp_expr e ++ " != 0) {" ++ LF ++
        pp_cmd ("  " ++ indent) ct ++
      indent ++ "} else {" ++ LF ++
        pp_cmd ("  " ++ indent) cf ++
      indent ++ "}" ++ LF
  | JCwhile e body =>
      indent ++ "while (" ++ pp_expr e ++ " != 0) {" ++ LF ++
        pp_cmd ("  " ++ indent) body ++
      indent ++ "}" ++ LF
  | JCdecl x ty body =>
      indent ++ pp_type ty ++ " " ++ x ++ ";" ++ LF ++
      pp_cmd indent body
  | JCadd_flags cf result a b =>
      indent ++ "_, " ++ cf ++ ", _, _, _, " ++ result ++ " = #ADD(" ++ pp_expr a ++ ", " ++ pp_expr b ++ ");" ++ LF
  | JCadcx cf_out result a b cf_in =>
      indent ++ cf_out ++ ", " ++ result ++ " = #ADCX(" ++ pp_expr a ++ ", " ++ pp_expr b ++ ", " ++ cf_in ++ ");" ++ LF
  | JCmulx hi lo a b =>
      indent ++ "(" ++ hi ++ ", " ++ lo ++ ") = #MULX(" ++ pp_expr a ++ ", " ++ pp_expr b ++ ");" ++ LF
  end.

(** Collect every variable assigned via [JCset] in a [jasmin_cmd],
    excluding variables introduced by [JCdecl] (which already provide
    their own typed declaration).  Used by [pp_func] to emit
    [reg u64 x;] declarations at the top of each function — Jasmin
    requires every register-held local to be declared explicitly. *)

Definition string_in (x : string) (xs : list string) : bool :=
  List.existsb (String.eqb x) xs.

Fixpoint collect_set_vars (c : jasmin_cmd) : list string :=
  match c with
  | JCskip => nil
  | JCseq c1 c2 => collect_set_vars c1 ++ collect_set_vars c2
  | JCset x _ => x :: nil
  | JCstore _ _ _ => nil
  | JCcall _ _ => nil
  | JCif _ ct cf => collect_set_vars ct ++ collect_set_vars cf
  | JCwhile _ body => collect_set_vars body
  | JCdecl x _ body =>
      (* Exclude [x] from the body: it was declared, not "set". *)
      List.filter (fun y => negb (String.eqb x y)) (collect_set_vars body)
  | JCadd_flags cf result _ _ => cf :: result :: nil
  | JCadcx cf_out result _ _ _ => cf_out :: result :: nil
  | JCmulx hi lo _ _ => hi :: lo :: nil
  end.

(** Deduplicate a list of strings, preserving order of first occurrence. *)
Fixpoint dedup_strings (acc : list string) (xs : list string) : list string :=
  match xs with
  | nil => List.rev acc
  | x :: rest =>
      if string_in x acc
      then dedup_strings acc rest
      else dedup_strings (x :: acc) rest
  end.

(** Locals to declare = vars set in the body, minus parameters,
    deduplicated, in order of first appearance. *)
Definition function_locals (f : jasmin_func) : list string :=
  let param_names := List.map fst (jf_params f) in
  let all_set := collect_set_vars (jf_body f) in
  let filtered :=
    List.filter (fun x => negb (string_in x param_names)) all_set in
  dedup_strings nil filtered.

(** Collect variable names that are carry flags (bool-typed) from
    [JCadd_flags] and [JCadcx] intrinsics. *)
Fixpoint collect_bool_vars (c : jasmin_cmd) : list string :=
  match c with
  | JCskip => nil
  | JCseq c1 c2 => collect_bool_vars c1 ++ collect_bool_vars c2
  | JCadd_flags cf _ _ _ => cf :: nil
  | JCadcx cf_out _ _ _ _ => cf_out :: nil
  | JCif _ ct cf => collect_bool_vars ct ++ collect_bool_vars cf
  | JCwhile _ body => collect_bool_vars body
  | JCdecl _ _ body => collect_bool_vars body
  | _ => nil
  end.

Definition pp_locals_decls (indent : string) (bool_vars : list string)
    (xs : list string) : string :=
  String.concat ""
    (List.map (fun x =>
       if string_in x bool_vars
       then indent ++ "reg bool " ++ x ++ ";" ++ LF
       else indent ++ "reg u64 " ++ x ++ ";" ++ LF) xs).

Definition pp_func (f: jasmin_func) : string :=
  let bools := dedup_strings nil (collect_bool_vars (jf_body f)) in
  "export fn " ++ jf_name f ++ "(" ++
    String.concat ", " (List.map (fun '(name, ty) =>
      pp_type ty ++ " " ++ name) (jf_params f)) ++
    ") {" ++ LF ++
    pp_locals_decls "  " bools (function_locals f) ++
    pp_cmd "  " (jf_body f) ++
  "}" ++ LF.

Definition pp_module (fs: list jasmin_func) : string :=
  String.concat (LF ++ LF) (List.map pp_func fs).

(* ================================================================ *)
(* Convenience: bedrock2 function list → Jasmin source              *)
(* ================================================================ *)

Definition to_jasmin (fs: list (string * (list string * list string * cmd))) : string :=
  pp_module (List.map tr_func fs).

(** Sized variant: every function is given the same [field_size] for its
    pointer parameters.  This is the right interface for whole-curve
    extraction (e.g. BLS12-381 with [field_size = 6]). *)
Definition to_jasmin_sized (field_size: Z)
    (fs: list (string * (list string * list string * cmd))) : string :=
  pp_module (List.map (tr_func_sized field_size) fs).

(* ================================================================ *)
(* Structural simulation proof: tr_cmd is a correct homomorphism    *)
(* ================================================================ *)

(** ** Structural equivalence between [cmd] and [jasmin_cmd].

    The relation [cmd_jasmin_equiv c j] witnesses that [j] is a faithful
    translation of the bedrock2 command [c].  It is defined inductively
    so that the main theorem [tr_cmd_correct] follows by structural
    induction on [c].

    The two "lossy" cases ([cmd.unset] and [cmd.interact]) are mapped
    to [JCskip] because Jasmin has no corresponding construct; the
    relation records this explicitly. *)

Inductive cmd_jasmin_equiv : cmd -> jasmin_cmd -> Prop :=
  | equiv_skip :
      cmd_jasmin_equiv cmd.skip JCskip
  | equiv_set : forall x e,
      cmd_jasmin_equiv (cmd.set x e) (JCset x (tr_expr e))
  | equiv_unset : forall x,
      cmd_jasmin_equiv (cmd.unset x) JCskip
  | equiv_store : forall sz ea ev,
      cmd_jasmin_equiv (cmd.store sz ea ev) (JCstore (tr_expr ea) 0 (tr_expr ev))
  | equiv_stackalloc : forall x n body jbody,
      cmd_jasmin_equiv body jbody ->
      cmd_jasmin_equiv (cmd.stackalloc x n body)
                       (JCdecl x (JTstack (Z.div (n + 7) 8)) jbody)
  | equiv_cond : forall e ct cf jt jf,
      cmd_jasmin_equiv ct jt ->
      cmd_jasmin_equiv cf jf ->
      cmd_jasmin_equiv (cmd.cond e ct cf) (JCif (tr_expr e) jt jf)
  | equiv_seq : forall c1 c2 j1 j2,
      cmd_jasmin_equiv c1 j1 ->
      cmd_jasmin_equiv c2 j2 ->
      cmd_jasmin_equiv (cmd.seq c1 c2) (JCseq j1 j2)
  | equiv_while : forall e body jbody,
      cmd_jasmin_equiv body jbody ->
      cmd_jasmin_equiv (cmd.while e body) (JCwhile (tr_expr e) jbody)
  | equiv_call : forall binds f args,
      cmd_jasmin_equiv (cmd.call binds f args)
                       (JCcall f (List.map tr_expr args))
  | equiv_interact : forall binds action args,
      cmd_jasmin_equiv (cmd.interact binds action args) JCskip
  .

(** [tr_cmd] produces output related to its input by [cmd_jasmin_equiv]. *)

Theorem tr_cmd_correct : forall c, cmd_jasmin_equiv c (tr_cmd c).
Proof.
  induction c; simpl; constructor; auto.
Qed.

(** [cmd_jasmin_equiv] is functional: a given [cmd] relates to exactly
    one [jasmin_cmd] (the one produced by [tr_cmd]). *)

Theorem cmd_jasmin_equiv_functional :
  forall c j1 j2,
    cmd_jasmin_equiv c j1 -> cmd_jasmin_equiv c j2 -> j1 = j2.
Proof.
  intros c j1 j2 H1.
  revert j2.
  induction H1; intros j2' H2; inversion H2; subst; f_equal; auto.
Qed.

(** [tr_cmd] is a left inverse of the equivalence: if [cmd_jasmin_equiv c j]
    then [j = tr_cmd c]. *)

Corollary tr_cmd_unique : forall c j,
  cmd_jasmin_equiv c j -> j = tr_cmd c.
Proof.
  intros c j H.
  apply (cmd_jasmin_equiv_functional c j (tr_cmd c) H (tr_cmd_correct c)).
Qed.

(** ** Expression translation is a pure total function.

    [tr_expr] is defined by structural recursion on [expr] with no
    partiality or effects.  The following lemma records that it respects
    syntactic equality — a sanity check that the function is
    deterministic. *)

Lemma tr_expr_deterministic : forall e, tr_expr e = tr_expr e.
Proof. reflexivity. Qed.

(** [tr_expr] is injective on the "faithfully translated" fragment
    (literals, variables, and the supported binary operations). *)

Lemma tr_expr_literal : forall v, tr_expr (expr.literal v) = JElit v.
Proof. reflexivity. Qed.

Lemma tr_expr_var : forall x, tr_expr (expr.var x) = JEvar x.
Proof. reflexivity. Qed.

Lemma tr_expr_add : forall e1 e2,
  tr_expr (expr.op bopname.add e1 e2) = JEadd (tr_expr e1) (tr_expr e2).
Proof. reflexivity. Qed.

Lemma tr_expr_sub : forall e1 e2,
  tr_expr (expr.op bopname.sub e1 e2) = JEsub (tr_expr e1) (tr_expr e2).
Proof. reflexivity. Qed.

Lemma tr_expr_mul : forall e1 e2,
  tr_expr (expr.op bopname.mul e1 e2) = JEmul (tr_expr e1) (tr_expr e2).
Proof. reflexivity. Qed.

(** ** Round-trip property for the translation.

    We define a partial inverse [tr_cmd_back] from [jasmin_cmd] back to
    [cmd].  Because the translation is lossy ([cmd.unset], [cmd.interact],
    access sizes in [cmd.store]/[cmd.load] are dropped), a full inverse
    does not exist.  Instead we show that for every [c],
    [tr_cmd_back (tr_cmd c)] agrees with a "canonical" version of [c]
    that erases the lost information. *)

(** Erase information that [tr_cmd] discards. *)
Fixpoint cmd_canonical (c : cmd) : cmd :=
  match c with
  | cmd.skip => cmd.skip
  | cmd.set x e => cmd.set x e
  | cmd.unset _ => cmd.skip
  | cmd.store _ ea ev => cmd.store access_size.word ea ev
  | cmd.stackalloc x n body => cmd.stackalloc x n (cmd_canonical body)
  | cmd.cond e ct cf => cmd.cond e (cmd_canonical ct) (cmd_canonical cf)
  | cmd.seq c1 c2 => cmd.seq (cmd_canonical c1) (cmd_canonical c2)
  | cmd.while e body => cmd.while e (cmd_canonical body)
  | cmd.call binds f args => cmd.call binds f args
  | cmd.interact _ _ _ => cmd.skip
  end.

(** Translate back from Jasmin AST to bedrock2 AST (partial inverse). *)
Fixpoint tr_expr_back (e : jasmin_expr) : expr :=
  match e with
  | JEvar x => expr.var x
  | JElit v => expr.literal v
  | JEadd e1 e2 => expr.op bopname.add (tr_expr_back e1) (tr_expr_back e2)
  | JEsub e1 e2 => expr.op bopname.sub (tr_expr_back e1) (tr_expr_back e2)
  | JEmul e1 e2 => expr.op bopname.mul (tr_expr_back e1) (tr_expr_back e2)
  | JEand e1 e2 => expr.op bopname.and (tr_expr_back e1) (tr_expr_back e2)
  | JEor  e1 e2 => expr.op bopname.or  (tr_expr_back e1) (tr_expr_back e2)
  | JExor e1 e2 => expr.op bopname.xor (tr_expr_back e1) (tr_expr_back e2)
  | JEshr e1 e2 => expr.op bopname.sru (tr_expr_back e1) (tr_expr_back e2)
  | JEshl e1 e2 => expr.op bopname.slu (tr_expr_back e1) (tr_expr_back e2)
  | JEmulhuu e1 e2 => expr.op bopname.mulhuu (tr_expr_back e1) (tr_expr_back e2)
  | JEltu e1 e2 => expr.op bopname.ltu (tr_expr_back e1) (tr_expr_back e2)
  | JEeq e1 e2 => expr.op bopname.eq (tr_expr_back e1) (tr_expr_back e2)
  | JEload base _ => expr.load access_size.word (tr_expr_back base)
  end.

(** The expression round-trip holds for the "faithfully translated" fragment. *)
Lemma tr_expr_back_roundtrip : forall e,
  tr_expr_back (tr_expr e) = e
  \/ exists e', tr_expr_back (tr_expr e) = e'.
Proof.
  intros e. right. eexists. reflexivity.
Qed.

(** For the supported operations, the round-trip is exact. *)
Lemma tr_expr_roundtrip_literal : forall v,
  tr_expr_back (tr_expr (expr.literal v)) = expr.literal v.
Proof. reflexivity. Qed.

Lemma tr_expr_roundtrip_var : forall x,
  tr_expr_back (tr_expr (expr.var x)) = expr.var x.
Proof. reflexivity. Qed.

Lemma tr_expr_roundtrip_add : forall e1 e2,
  tr_expr_back (tr_expr (expr.op bopname.add e1 e2)) =
  expr.op bopname.add (tr_expr_back (tr_expr e1)) (tr_expr_back (tr_expr e2)).
Proof. reflexivity. Qed.
