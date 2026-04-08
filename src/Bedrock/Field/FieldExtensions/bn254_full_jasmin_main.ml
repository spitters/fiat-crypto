(** * BN254 full Jasmin emitter — base Fp + Fp2 + pairing pipeline + opt ops. *)

open Bn254_full_jasmin_extracted

let ocaml_string (cs : char list) : string =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let () =
  let outfile = if Array.length Sys.argv > 1 then Sys.argv.(1)
                else "/tmp/bn254_full.jazz" in
  let jfuncs = bn254_full_jasmin in
  let n = Stdlib.List.length jfuncs in
  Printf.eprintf "[bn254_full_jasmin] %d functions, field_size=4\n" n;
  let text = ocaml_string (pp_module jfuncs) in
  let oc = open_out outfile in
  output_string oc text; close_out oc;
  Printf.eprintf "[bn254_full_jasmin] wrote %d bytes to %s\n"
    (Stdlib.String.length text) outfile
