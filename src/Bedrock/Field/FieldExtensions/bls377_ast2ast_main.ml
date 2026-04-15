(* AST-to-AST driver for BLS12-377: bedrock2 → jasmin_cmd → Jasmin cmd
 *
 * Parallel to ast2ast_main.ml (BLS12-381) and bn254_ast2ast_main.ml
 * (BN254).  Combines the two Coq extractions:
 *   1. Bls377_jasmin_extracted     — [bls377_all_jasmin : jasmin_func list]
 *      from ExtractBLS377Jasmin.vo (text-path driver, function-list
 *      surface reused).
 *   2. Bridge_simple_v2             — [to_jasmin_cmd] from
 *      JasminBridgeReal.v, extracted in isolation.
 *
 * UNVERIFIED GLUE: only this file (~15 lines).
 * Types [jasmin_cmd]/[jasmin_expr]/[jasmin_type] are structurally
 * identical between the two extractions (same Coq defs in ToJasmin.v);
 * [Obj.magic] casts between the two OCaml module namespaces.
 *)

let implode cs =
  String.init (List.length cs) (fun i -> List.nth cs i)

let () =
  let funcs = Bls377_jasmin_extracted.bls377_all_jasmin in
  Printf.printf "[bls377-ast2ast] %d functions\n" (List.length funcs);
  List.iter (fun (f : Bls377_jasmin_extracted.jasmin_func) ->
    let name = implode f.jf_name in
    let body : Bridge_simple_v2.jasmin_cmd = Obj.magic f.jf_body in
    let jasmin_instrs = Bridge_simple_v2.to_jasmin_cmd
      (Obj.magic ()) (Obj.magic ()) body in
    Printf.printf "  %-30s -> %d Jasmin instrs\n" name (List.length jasmin_instrs)
  ) funcs;
  Printf.printf "[bls377-ast2ast] All functions translated via verified bridge.\n"
