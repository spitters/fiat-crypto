(** * BLS12-381 Jasmin emitter.
 *
 * Loads the bedrock2 function list extracted from
 * [ExtractBLS12Jasmin.v], runs the verified flatten pass and the
 * [tr_func_sized] / [pp_module] translation, and writes the resulting
 * Jasmin source to a [.jazz] file.
 *
 * Usage:
 *   ocamlfind ocamlopt bls12_jasmin_extracted.ml bls12_jasmin_main.ml \
 *     -o bls12_jasmin_main
 *   ./bls12_jasmin_main bls12_pairing.jazz
 *)

open Bls12_jasmin_extracted

(* Coq's char list <-> OCaml string.  Use [Stdlib.List] explicitly so
   the local [List.ml] from Coq extraction does not shadow it. *)
let ocaml_string (cs : char list) : string =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let count_funcs (fs : 'a list) : int = Stdlib.List.length fs

let usage () =
  Printf.eprintf "usage: %s <output.jazz> [--flatten]\n" Sys.argv.(0);
  exit 2

let () =
  let outfile, do_flatten =
    match Array.to_list Sys.argv with
    | [_; out] -> (out, false)
    | [_; out; "--flatten"] -> (out, true)
    | _ -> usage ()
  in
  (* Use the Coq-side pre-translated jasmin_func lists.  Translating in
     Coq via [tr_func_sized] under [vm_compute] guarantees the
     [JTstack] limb counts are real literal integers in OCaml; the
     OCaml-side [Z.div]/[Z.add] under ExtrOcamlZInt still walk a
     binary positive representation and would otherwise yield zero. *)
  let jfuncs =
    if do_flatten then bls12_optimized_jasmin else bls12_all_jasmin
  in
  let n = count_funcs jfuncs in
  Printf.eprintf "[bls12_jasmin] loaded %d jasmin functions (flatten=%b)\n"
    n do_flatten;
  let _ = bls12_field_size in
  Printf.eprintf "[bls12_jasmin] field size = 6 limbs\n";
  let coq_text = pp_module jfuncs in
  let text = ocaml_string coq_text in
  let oc = open_out outfile in
  output_string oc text;
  close_out oc;
  Printf.eprintf "[bls12_jasmin] wrote %d bytes to %s\n"
    (Stdlib.String.length text) outfile
