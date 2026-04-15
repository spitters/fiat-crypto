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
 *   -> Compile.compile                              (jasminc full pipeline)
 *   -> Pp_x86.print_prog                            (assembly output)
 *
 * Usage:
 *   ./bn254_compile_direct <out.s>                   # all functions
 *   ./bn254_compile_direct <out.s> --func <name>     # one function
 *   ./bn254_compile_direct <out.s> --verbose         # per-pass tracing
 *
 * Register-pressure partitioning (compile_direct.ml lines 366-716) is not
 * included here; BN254's 4-limb Fp mul has lower register pressure than
 * BLS12's 6-limb mul.  If jasminc's allocator spills too aggressively, port
 * partition_for_regalloc from compile_direct.ml verbatim. *)

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
  let args = List.map (fun (n, _ty) -> mk_var (implode n)) f.jf_params in
  let tyin = List.map (fun _ -> Bty (U U64)) args in
  (* Add [nospill] annotation to match compile_direct.ml — protects Export
     functions from the CF.90 bug in jasminc that manifests when AutoSpill
     is applied to large functions. *)
  let nospill_annot = { FInfo.f_annot_empty with
    FInfo.f_user_annot =
      [(Location.mk_loc Location._dummy "nospill", None)] } in
  {
    f_loc      = Location._dummy;
    f_annot    = nospill_annot;
    f_info     = ();
    f_cc       = FInfo.Export;
    f_name     = mk_funname name;
    f_tyin     = tyin;
    f_args     = args;
    f_body     = body;
    f_tyout    = [];
    f_ret_info = { FInfo.ret_annot = []; ret_loc = Location._dummy };
    f_ret      = [];
  }

let build_prog (funcs : Bn254_full_jasmin_extracted.jasmin_func list)
  : (unit, X86_arch.extended_op Sopn.asm_op_t) prog =
  ([], List.map wrap_func funcs)

(* ---------------- CLI ---------------------------------------------- *)

let usage () =
  Printf.eprintf "usage: %s <output.s> [--func <name>] [--verbose]\n" Sys.argv.(0);
  Printf.eprintf "  --func <name>  compile only the named function (must be a leaf)\n";
  exit 2

let parse_args () =
  let args = Array.to_list Sys.argv in
  match args with
  | [_; out] -> (out, None, false)
  | [_; out; "--verbose"] -> (out, None, true)
  | [_; out; "--func"; fname] -> (out, Some fname, false)
  | [_; out; "--func"; fname; "--verbose"] -> (out, Some fname, true)
  | _ -> usage ()

(* ---------------- Pass-name helper for verbose tracing ------------ *)

let step_name (s : Compiler.compiler_step) =
  match s with
  | Typing -> "Typing" | ParamsExpansion -> "ParamsExpansion"
  | RemoveAssertion -> "RemoveAssertion" | InsertRenaming -> "InsertRenaming"
  | WintWord -> "WintWord" | ArrayCopy -> "ArrayCopy"
  | AddArrInit -> "AddArrInit" | LowerSpill -> "LowerSpill"
  | Inlining -> "Inlining" | RemoveUnusedFunction -> "RemoveUnusedFunction"
  | Unrolling -> "Unrolling" | Splitting -> "Splitting"
  | Renaming -> "Renaming" | RemovePhiNodes -> "RemovePhiNodes"
  | DeadCode_Renaming -> "DeadCode_Renaming" | RemoveArrInit -> "RemoveArrInit"
  | MakeRefArguments -> "MakeRefArguments"
  | RegArrayExpansion -> "RegArrayExpansion"
  | RemoveGlobal -> "RemoveGlobal"
  | LoadConstantsInCond -> "LoadConstantsInCond"
  | LowerInstruction -> "LowerInstruction"
  | PropagateInline -> "PropagateInline"
  | SLHLowering -> "SLHLowering" | LowerAddressing -> "LowerAddressing"
  | StackAllocation -> "StackAllocation" | RemoveReturn -> "RemoveReturn"
  | RegAllocation -> "RegAllocation"
  | DeadCode_RegAllocation -> "DeadCode_RegAllocation"
  | Linearization -> "Linearization" | StackZeroization -> "StackZeroization"
  | Tunneling -> "Tunneling" | Assembly -> "Assembly"

(* ---------------- Main ------------------------------------------- *)

let () =
  let outfile, func_filter, verbose = parse_args () in

  (* Step 1: Load + dedup *)
  let all_funcs = Bn254_full_jasmin_extracted.bn254_full_jasmin in
  let seen = Hashtbl.create 97 in
  let funcs = List.filter (fun (f : Bn254_full_jasmin_extracted.jasmin_func) ->
    let name = implode f.jf_name in
    if Hashtbl.mem seen name then false
    else (Hashtbl.add seen name (); true)
  ) all_funcs in
  Printf.eprintf "[bn254-compile_direct] loaded %d unique functions\n" (List.length funcs);

  (* Step 2: Optional --func filter *)
  let funcs_to_compile =
    match func_filter with
    | None -> funcs
    | Some fname ->
      let matches = List.filter (fun (f : Bn254_full_jasmin_extracted.jasmin_func) ->
        implode f.jf_name = fname
      ) funcs in
      match matches with
      | [] ->
        Printf.eprintf "[bn254-compile_direct] ERROR: function '%s' not found.\n" fname;
        Printf.eprintf "Available functions:\n";
        List.iter (fun (f : Bn254_full_jasmin_extracted.jasmin_func) ->
          Printf.eprintf "  %s\n" (implode f.jf_name)
        ) funcs;
        exit 1
      | _ ->
        Printf.eprintf "[bn254-compile_direct] filtering to function '%s'\n" fname;
        matches
  in

  (* Step 3: Pre-register funnames *)
  List.iter (fun (f : Bn254_full_jasmin_extracted.jasmin_func) ->
    ignore (mk_funname (implode f.jf_name))
  ) funcs_to_compile;

  (* Step 4: Translate + wrap *)
  let prog = build_prog funcs_to_compile in
  Printf.eprintf "[bn254-compile_direct] built prog with %d functions\n"
    (List.length (snd prog));

  (* Step 5: jasminc pipeline *)
  Printf.eprintf "[bn254-compile_direct] Conv.cuprog_of_prog ...\n%!";
  let cprog =
    try Conv.cuprog_of_prog prog
    with e ->
      Printf.eprintf "[bn254-compile_direct] Conv.cuprog_of_prog raised: %s\n"
        (Printexc.to_string e);
      Printexc.print_backtrace stderr;
      exit 1
  in
  Printf.eprintf "[bn254-compile_direct] Compile.compile ...\n%!";
  let visit_prog_after_pass ~debug:_ step _prog =
    if verbose then Printf.eprintf "  [pass] %s OK\n%!" (step_name step)
  in
  let result =
    try Compile.compile (module X86_arch) visit_prog_after_pass prog cprog
    with
    | Utils.HiError hierr ->
      Printf.eprintf "[bn254-compile_direct] Compile.compile raised HiError:\n";
      Format.eprintf "  %a\n" Utils.pp_hierror hierr;
      exit 1
    | e ->
      Printf.eprintf "[bn254-compile_direct] Compile.compile raised: %s\n"
        (Printexc.to_string e);
      Printexc.print_backtrace stderr;
      exit 1
  in
  match result with
  | Utils0.Ok asm_prog ->
    Printf.eprintf "[bn254-compile_direct] compilation succeeded!\n";
    let oc = open_out outfile in
    let fmt = Format.formatter_of_out_channel oc in
    Pp_x86.print_prog fmt (Obj.magic asm_prog);
    Format.pp_print_flush fmt ();
    close_out oc;
    Printf.eprintf "[bn254-compile_direct] wrote assembly to %s\n" outfile
  | Utils0.Error err ->
    let hierr = Conv.error_of_cerror
      (Printer.pp_err ~debug:true) err in
    Printf.eprintf "[bn254-compile_direct] compilation FAILED:\n";
    Format.eprintf "  %a\n" Utils.pp_hierror hierr;
    exit 1
