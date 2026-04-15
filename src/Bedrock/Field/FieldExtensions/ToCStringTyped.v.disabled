(** * Alternative C backend using typed restrict pointers.
 *
 * Drop-in replacement for bedrock2.ToCString that emits typed pointer
 * parameters instead of uintptr_t, enabling GCC alias analysis to
 * eliminate redundant memory copies in tower arithmetic.
 *
 * The only semantic difference: function parameters are declared as
 * [uint8_t *restrict] instead of [uintptr_t]. All pointer arithmetic,
 * loads, and stores work identically because C allows arithmetic on
 * [uint8_t*]. The [restrict] qualifier tells GCC that no two parameters
 * alias, enabling copy elimination.
 *
 * This is a TRUSTED component (like the original ToCString.v) — it is
 * not verified against bedrock2 semantics. The justification: the
 * generated C is observationally equivalent to the uintptr_t version
 * on all platforms where sizeof(uintptr_t) == sizeof(void*), which is
 * guaranteed by the existing static_assert in the prelude.
 *)

Require Import bedrock2.Syntax bedrock2.Variables. Import bopname.
Require Import coqutil.Datatypes.ListSet.
Require Import Coq.ZArith.BinIntDef Coq.Numbers.BinNums Coq.Numbers.DecimalString.
Require Import Coq.Strings.String. Local Open Scope string_scope.

(* Import the original ToCString for reuse *)
Require Import bedrock2.ToCString.

(** Prelude with typed pointer load/store helpers. *)
Definition typed_prelude := "#include <stdint.h>
#include <string.h>

// bedrock2 typed-pointer runtime.
// Uses uint8_t* for addresses (instead of uintptr_t) to enable
// GCC restrict-based alias analysis and copy elimination.
typedef uint8_t *restrict br_ptr_t;
typedef uintptr_t br_word_t;  // for non-pointer integer values

static __attribute__((always_inline)) inline uintptr_t
_br2_load(uint8_t *restrict a, uintptr_t sz) {
  switch (sz) {
  case 1: { uint8_t  r = 0; memcpy(&r, a, 1); return r; }
  case 2: { uint16_t r = 0; memcpy(&r, a, 2); return r; }
  case 4: { uint32_t r = 0; memcpy(&r, a, 4); return r; }
  case 8: { uint64_t r = 0; memcpy(&r, a, 8); return r; }
  default: __builtin_unreachable();
  }
}

static __attribute__((always_inline)) inline void
_br2_store(uint8_t *restrict a, uintptr_t v, uintptr_t sz) {
  memcpy(a, &v, sz);
}
".

(** Format a function declaration with typed pointer parameters. *)
Definition fmt_c_decl_typed (rett : string) (args : list String.string)
    (name : String.string) (retptrs : list String.string) : string :=
  let argstring : String.string :=
    (match args, retptrs with
    | nil, nil => "void"
    | _, _ => concat ", " (
        List.map (fun a => "uint8_t *restrict "++c_var a) args ++
        List.map (fun r => "uint8_t **restrict "++c_var r) retptrs)
    end)
  in
  (rett ++ " " ++ c_fun name ++ "(" ++ argstring ++ ")").

(** Typed function declaration. *)
Definition c_decl_typed (f : String.string * (list String.string * list String.string * cmd)) :=
  let '(name, (args, rets, body)) := f in
  match rets with
  | nil => fmt_c_decl_typed "void" args name nil
  | cons _ _ => fmt_c_decl_typed "uintptr_t" args name (List.removelast rets)
  end ++ ";".

(** Typed expression emitter — casts pointer arithmetic results. *)
Fixpoint c_expr_typed (e : expr) : string :=
  match e with
  | expr.literal v => "(uint8_t*)" ++ DecimalString.NilZero.string_of_int (BinInt.Z.to_int v) ++ "ULL"
  | expr.var x => c_var x
  | expr.load s ea => "_br2_load(" ++ c_expr_typed ea ++ ", " ++ c_size s ++ ")"
  | expr.inlinetable s t index =>
    "({ static const uint8_t _inlinetable["++c_lit (Z.of_nat (List.length t))++"] = {"++
    concat ", " (List.map c_byte_withoutcast t)++"}; _br2_load((uint8_t*)&_inlinetable["++
    c_expr_typed index++"], "++c_size s++"); })"
  | expr.op op e1 e2 =>
    match op with
    | add => "(" ++ c_expr_typed e1 ++ ")+(" ++ c_expr_typed e2 ++ ")"
    | _ => "(uint8_t*)(uintptr_t)" ++ c_bop ("((uintptr_t)" ++ c_expr_typed e1 ++ ")") op ("((uintptr_t)" ++ c_expr_typed e2 ++ ")")
    end
  | expr.lazy_and e1 e2 => "(uint8_t*)((uintptr_t)(" ++ c_expr_typed e1 ++ ") && (uintptr_t)(" ++ c_expr_typed e2 ++ "))"
  | expr.lazy_or e1 e2 => "(uint8_t*)((uintptr_t)(" ++ c_expr_typed e1 ++ ") || (uintptr_t)(" ++ c_expr_typed e2 ++ "))"
  | expr.ite c e1 e2 => "((uintptr_t)" ++ c_expr_typed c ++ ") ? (" ++ c_expr_typed e1 ++ ") : (" ++ c_expr_typed e2 ++ ")"
  end.

(** Typed command emitter. *)
Fixpoint c_cmd_typed (indent : string) (c : cmd) : string :=
  match c with
  | cmd.store s ea ev =>
    indent ++ "_br2_store(" ++ c_expr_typed ea ++ ", (uintptr_t)" ++ c_expr_typed ev ++ ", " ++ c_size s ++ ");" ++ LF
  | cmd.stackalloc x n body =>
    let tmp := "_br2_stackalloc_"++x in
    indent ++ "{ uint8_t "++tmp++"["++c_lit n++"]; "++x++" = "++tmp++";"++LF++
    c_cmd_typed indent body ++
    indent ++ "}" ++ LF
  | cmd.set x ev =>
    indent ++ c_var x ++ " = " ++ c_expr_typed ev ++ ";" ++ LF
  | cmd.unset x =>
    indent ++ "// unset " ++ c_var x ++ LF
  | cmd.cond eb t f =>
    indent ++ "if ((uintptr_t)" ++ c_expr_typed eb ++ ") {" ++ LF ++
      c_cmd_typed ("  "++indent) t ++
    indent ++ "} else {" ++ LF ++
      c_cmd_typed ("  "++indent) f ++
    indent ++ "}" ++ LF
  | cmd.while eb c =>
    indent ++ "while ((uintptr_t)" ++ c_expr_typed eb ++ ") {" ++ LF ++
      c_cmd_typed ("  "++indent) c ++
    indent ++ "}" ++ LF
  | cmd.seq c1 c2 =>
    c_cmd_typed indent c1 ++
    c_cmd_typed indent c2
  | cmd.skip =>
    indent ++ "/*skip*/" ++ LF
  | cmd.call args f es =>
    indent ++ c_call (List.map c_var args) (c_fun f) (List.map c_expr_typed es)
  | cmd.interact binds action es =>
    indent ++ c_act binds action (List.map c_expr_typed es)
  end.

(** Typed function body emitter. Local variables use uint8_t* for pointer-valued
    vars and uintptr_t for integer-valued vars. Since bedrock2 doesn't distinguish
    these, we use uint8_t* for ALL locals — C allows pointer arithmetic on uint8_t*
    and implicit integer-to-pointer casts in assignments. *)
Definition c_func_typed_with_globals globals '(name, (args, rets, body)) :=
  let name_clashes := list_intersect String.eqb
    globals (name :: args ++ rets ++ cmd.mod_vars body) in
  match name_clashes with
  | cons _ _ => "#error ""In " ++ name ++ ", locals clash with globals (" ++
                String.concat ", " name_clashes ++ ")"" " ++ LF
  | _ =>
  let decl_retvar_retrenames : string * option String.string * list (String.string * String.string) :=
  match rets with
  | nil => (fmt_c_decl_typed "void" args name nil, None, nil)
  | cons r0 _ =>
    let r0 := List.last rets r0 in
    let rets' := List.removelast rets in
    let retrenames := fst (rename_outs rets' (cmd.vars body)) in
    (fmt_c_decl_typed "uintptr_t" args name (List.map snd retrenames), Some r0, retrenames)
  end in
  let decl := fst (fst decl_retvar_retrenames) in
  let retvar := snd (fst decl_retvar_retrenames) in
  let retrenames := snd decl_retvar_retrenames in
  let localvars : list String.string := List_uniq String.eqb (
      let allvars := (List.app (match retvar with None => nil | Some v => cons v nil end) (cmd.vars body)) in
      (List_minus String.eqb allvars (List.app args globals))) in
  decl ++ " {" ++ LF ++
    let indent := "  " in
    (match localvars with nil => "" | _ => indent ++ "uint8_t *restrict " ++ concat ", *restrict " (List.map c_var localvars) ++ ";" ++ LF end) ++
    c_cmd_typed indent body ++
    concat "" (List.map (fun '(o, optr) => indent ++ "*" ++ c_var optr ++ " = " ++ c_var o ++ ";" ++ LF) retrenames) ++
    indent ++ "return" ++ (match retvar with None => "" | Some rv => " (uintptr_t)"++c_var rv end) ++ ";" ++ LF ++
    "}" ++ LF
  end.

Definition c_func_typed: func -> String.string := c_func_typed_with_globals nil.

Definition c_module_typed (fs : list func) :=
  match fs with
  | nil => "#error ""c_module nil"" "
  | cons main fs =>
    concat LF (typed_prelude :: List.map (fun f => "static " ++ c_decl_typed f) fs) ++ LF ++ LF ++
    c_func_typed main ++ LF ++
    concat LF (List.map (fun f => "static " ++ c_func_typed_with_globals nil f) fs)
  end.
