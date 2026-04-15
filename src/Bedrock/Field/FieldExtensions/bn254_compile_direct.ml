(* Direct compile_prog_to_asm driver for BN254 — AST-to-AST verified path.
 *
 * Parallel to compile_direct.ml (BLS12-381) and x25519_compile_direct.ml,
 * but uses the VERIFIED bridge [Bridge_simple_v2.to_jasmin_cmd] instead
 * of the deprecated OCaml-reimplemented [translate_cmd] (~200 lines
 * saved vs. compile_direct.ml).
 *
 * Pipeline:
 *   Bn254_full_jasmin_extracted.bn254_full_jasmin  (jasmin_func list)
 *   -> Obj.magic cast to Bridge_simple_v2.jasmin_cmd
 *   -> Bridge_simple_v2.to_jasmin_cmd               (EXTRACTED, Qed in Rocq)
 *   -> wrap_func / build_prog                       (this file, unverified plumbing)
 *   -> Conv.cuprog_of_prog                          (jasmin library)
 *   -> Compile.compile_prog_to_asm                  (jasminc full compiler)
 *   -> Pp_x86.print_prog                            (assembly output)
 *
 * RUNTIME BLOCKER (2026-04-15): bridge_simple_v2.ml has 8 unrealized
 * Coq axioms (5 Uint63 ops + int_to_ident + int_to_funname + type int)
 * that raise at runtime.  See BRIDGE_SIMPLE_V2_README.md for the
 * [Extract Constant] directives needed to regenerate a runtime-clean
 * bridge_simple_v2.ml.  Until then, this file compiles but cannot run.
 *
 * Register-pressure partitioning (the Montgomery-mul 1096-intermediate
 * workaround in compile_direct.ml lines 366-716) is not included here
 * because BN254's 4-limb Fp mul has far lower register pressure than
 * BLS12's 6-limb mul.  If jasminc's allocator spills too aggressively,
 * port partition_for_regalloc from compile_direct.ml verbatim. *)

open Jasmin
open Prog
open Wsize

(* ---------------- Architecture setup (mirrors compile_direct.ml) ---- *)

module X86_lowering_params : X86_arch_full.X86_input = struct
  let call_conv = X86_decl.x86_linux_call_conv
  let lowering_opt = { X86_lowering.use_lea = true; use_set0 = false }
end

module X86_core_arch = X86_arch_full.X86 (X86_lowering_params)
module X86_arch = Arch_full.Arch_from_Core_arch (X86_core_arch)

(* ---------------- Name / var interning ---------------------------- *)

let implode cs = String.init (List.length cs) (fun i -> List.nth cs i)

let var_tbl : (string, var) Hashtbl.t = Hashtbl.create 97
let fn_tbl : (string, CoreIdent.funname) Hashtbl.t = Hashtbl.create 97
let fn_counter = ref 0

let mk_var (name : string) : var =
  match Hashtbl.find_opt var_tbl name with
  | Some v -> v
  | None ->
    let v = V.mk name (Stack Direct) (Bty (U U64)) Location._dummy [] in
    Hashtbl.add var_tbl name v;
    v

let mk_funname (name : string) : CoreIdent.funname =
  match Hashtbl.find_opt fn_tbl name with
  | Some fn -> fn
  | None ->
    let fn = CoreIdent.F.mk name in
    Hashtbl.add fn_tbl name fn;
    fn

(* ---------------- Verified translation via Bridge_simple_v2 ------- *)

type x86_stmt = (int, unit, X86_arch.extended_op Sopn.asm_op_t) gstmt

(* The [atoI] / [asmop] parameters are opaque ([Obj.magic ()] works
   because the Coq-extracted function is parametric in them and the
   x86-64 instance is registered as a local typeclass instance at
   extraction time).  Same trick as ast2ast_main.ml. *)
let translate_to_jasmin (body : Bn254_full_jasmin_extracted.jasmin_cmd)
  : x86_stmt =
  let body' : Bridge_simple_v2.jasmin_cmd = Obj.magic body in
  Obj.magic (Bridge_simple_v2.to_jasmin_cmd
              (Obj.magic ()) (Obj.magic ()) body')

(* ---------------- Wrap into prog ---------------------------------- *)

let wrap_func (f : Bn254_full_jasmin_extracted.jasmin_func)
  : (unit, X86_arch.extended_op Sopn.asm_op_t) func =
  let name = implode f.jf_name in
  let body = translate_to_jasmin f.jf_body in
  {
    f_loc      = Location._dummy;
    f_annot    = FInfo.f_annot_empty;
    f_info     = ();
    f_cc       = FInfo.Export;
    f_name     = mk_funname name;
    f_tyin     = [];
    f_args     = [];
    f_body     = body;
    f_tyout    = [];
    f_ret_info = { FInfo.ret_annot = []; ret_loc = Location._dummy };
    f_ret      = [];
  }

let build_prog (funcs : Bn254_full_jasmin_extracted.jasmin_func list)
  : (unit, X86_arch.extended_op Sopn.asm_op_t) prog =
  ([], List.map wrap_func funcs)

(* ---------------- Call compile_prog_to_asm ------------------------ *)

(* See compile_direct.ml lines ~740-920 for the full boilerplate:
   - Conv.cuprog_of_prog
   - Conv.to_uprog x86_asmop
   - Compiler.compile_prog_to_asm
   - Pp_x86.print_prog
   Omitted here because the runtime is blocked by the Uint63 axioms
   (translate_to_jasmin will raise before we get to the prog wrap).
   Copy verbatim from compile_direct.ml lines 740-920 once
   bridge_simple_v2.ml is regenerated with Extract Constant directives. *)

let () =
  let funcs = Bn254_full_jasmin_extracted.bn254_full_jasmin in
  Printf.printf "[bn254-compile_direct] %d functions\n" (List.length funcs);
  (* Wrap each in a func record — this exercises the whole pipeline
     structurally at compile-time. Runtime will hit Uint63 axioms. *)
  let _prog = build_prog funcs in
  Printf.printf "[bn254-compile_direct] All functions wrapped in Jasmin prog\n";
  Printf.printf "[bn254-compile_direct] (compile_prog_to_asm call pending runtime fix)\n"
