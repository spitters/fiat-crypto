let ocaml_string cs =
  String.init (List.length cs) (List.nth cs)

let () =
  let funcs = Bn254_opt_jasmin_extracted.bn254_opt_jasmin in
  let s = Bn254_opt_jasmin_extracted.pp_module funcs in
  print_string (ocaml_string s)
