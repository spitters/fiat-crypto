(* AST-to-AST driver for BN254: bedrock2 → jasmin_cmd → Jasmin cmd
 *
 * Parallel to ast2ast_main.ml (BLS12). Combines two Coq extractions:
 *   1. Bn254_full_jasmin_extracted  — list of [jasmin_func] from
 *      ExtractBN254FullJasmin.vo (text-path driver; we reuse its
 *      [bn254_full_jasmin] list, not its pretty-printer).
 *   2. Bridge_simple_v2              — [to_jasmin_cmd] from
 *      JasminBridgeReal.v, extracted in isolation to avoid the
 *      universe conflict with fiat-crypto's coqutil imports.
 *
 * UNVERIFIED GLUE: only this file (~15 lines).
 * Types [jasmin_cmd]/[jasmin_expr]/[jasmin_type] are structurally
 * identical between the two extractions (same underlying Coq defs in
 * ToJasmin.v); [Obj.magic] casts between the two OCaml module
 * namespaces. Feeding the result to jasminc's verified
 * [compile_prog_to_asm] closes the chain.
 *)

let implode cs =
  String.init (List.length cs) (fun i -> List.nth cs i)

let () =
  let funcs = Bn254_full_jasmin_extracted.bn254_full_jasmin in
  Printf.printf "[bn254-ast2ast] %d functions\n" (List.length funcs);
  List.iter (fun (f : Bn254_full_jasmin_extracted.jasmin_func) ->
    let name = implode f.jf_name in
    (* Types match structurally — safe cast between module namespaces *)
    let body : Bridge_simple_v2.jasmin_cmd = Obj.magic f.jf_body in
    let jasmin_instrs = Bridge_simple_v2.to_jasmin_cmd
      (Obj.magic ()) (Obj.magic ()) body in
    Printf.printf "  %-30s -> %d Jasmin instrs\n" name (List.length jasmin_instrs)
  ) funcs;
  Printf.printf "[bn254-ast2ast] All functions translated via verified bridge.\n"
