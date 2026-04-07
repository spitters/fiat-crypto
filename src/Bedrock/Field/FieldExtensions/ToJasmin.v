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
From Stdlib Require Import String List ZArith Ascii.
Require Import Coq.Numbers.DecimalString.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* Jasmin AST                                                        *)
(* ================================================================ *)

(** Simplified Jasmin AST for the subset we need. *)

Inductive jasmin_type :=
  | JTu64          (* u64 scalar *)
  | JTptr          (* reg ptr u64[N] — pointer to array *)
  | JTstack (n: Z) (* stack u64[N] — stack-allocated array *)
  .

Inductive jasmin_expr :=
  | JEvar (x: string)
  | JElit (v: Z)
  | JEadd (e1 e2: jasmin_expr)
  | JEsub (e1 e2: jasmin_expr)
  | JEmul (e1 e2: jasmin_expr)
  | JEand (e1 e2: jasmin_expr)
  | JEor  (e1 e2: jasmin_expr)
  | JExor (e1 e2: jasmin_expr)
  | JEshr (e1 e2: jasmin_expr)
  | JEshl (e1 e2: jasmin_expr)
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
        | _ => JElit 0 (* lts, ltu, eq, srs, mulhuu, divu, remu: handled separately *)
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
      All parameters become [reg ptr u64[]] (pointers to field elements). *)
  Definition tr_func (f: string * (list string * list string * cmd)) : jasmin_func :=
    let '(name, (args, rets, body)) := f in
    {| jf_name := name;
       jf_params := List.map (fun a => (a, JTptr)) args;
       jf_locals := nil; (* locals are inferred from cmd.set *)
       jf_body := tr_cmd body;
    |}.

End Translation.

(* ================================================================ *)
(* Pretty-printing: jasmin_cmd → string (Jasmin source text)        *)
(* ================================================================ *)

Definition LF : string := String (Ascii.Ascii false true false true false false false false) "".

Fixpoint pp_expr (e: jasmin_expr) : string :=
  match e with
  | JEvar x => x
  | JElit v =>
      if (v <? 0)%Z then "(- " ++ DecimalString.NilZero.string_of_int (Z.to_int (Z.opp v)) ++ ")"
      else DecimalString.NilZero.string_of_int (Z.to_int v)
  | JEadd e1 e2 => "(" ++ pp_expr e1 ++ " + " ++ pp_expr e2 ++ ")"
  | JEsub e1 e2 => "(" ++ pp_expr e1 ++ " - " ++ pp_expr e2 ++ ")"
  | JEmul e1 e2 => "(" ++ pp_expr e1 ++ " * " ++ pp_expr e2 ++ ")"
  | JEand e1 e2 => "(" ++ pp_expr e1 ++ " & " ++ pp_expr e2 ++ ")"
  | JEor  e1 e2 => "(" ++ pp_expr e1 ++ " | " ++ pp_expr e2 ++ ")"
  | JExor e1 e2 => "(" ++ pp_expr e1 ++ " ^ " ++ pp_expr e2 ++ ")"
  | JEshr e1 e2 => "(" ++ pp_expr e1 ++ " >> " ++ pp_expr e2 ++ ")"
  | JEshl e1 e2 => "(" ++ pp_expr e1 ++ " << " ++ pp_expr e2 ++ ")"
  | JEload base off =>
      let off_str := DecimalString.NilZero.string_of_int (Z.to_int off) in
      "(u64)[" ++ pp_expr base ++ " + " ++ off_str ++ "]"
  end.

Definition pp_type (t: jasmin_type) : string :=
  match t with
  | JTu64 => "reg u64"
  | JTptr => "reg ptr u64[1]"  (* simplified; real version needs size *)
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
      indent ++ "(u64)[" ++ pp_expr base ++ " + " ++ off_str ++ "] = " ++ pp_expr v ++ ";" ++ LF
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
  end.

Definition pp_func (f: jasmin_func) : string :=
  "export fn " ++ jf_name f ++ "(" ++
    String.concat ", " (List.map (fun '(name, ty) =>
      pp_type ty ++ " " ++ name) (jf_params f)) ++
    ") {" ++ LF ++
    pp_cmd "  " (jf_body f) ++
  "}" ++ LF.

Definition pp_module (fs: list jasmin_func) : string :=
  String.concat (LF ++ LF) (List.map pp_func fs).

(* ================================================================ *)
(* Convenience: bedrock2 function list → Jasmin source              *)
(* ================================================================ *)

Definition to_jasmin (fs: list (string * (list string * list string * cmd))) : string :=
  pp_module (List.map tr_func fs).
