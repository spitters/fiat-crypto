open To_jasmin_extracted

(* Helper: OCaml string -> Coq char list *)
let coq_string s =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i-1) (s.[i] :: acc)
  in aux (String.length s - 1) []

(* Helper: Coq char list -> OCaml string *)
let ocaml_string cs =
  String.init (List.length cs) (List.nth cs)

let var x = Coq_expr.Coq_var (coq_string x)
let lit n = Coq_expr.Coq_literal n
let add e1 e2 = Coq_expr.Coq_op (Coq_bopname.Coq_add, e1, e2)
let call fn args = Coq_cmd.Coq_call ([], coq_string fn, args)
let seq c1 c2 = Coq_cmd.Coq_seq (c1, c2)
let stackalloc x n body = Coq_cmd.Coq_stackalloc (coq_string x, n, body)

let seq_list cs skip =
  List.fold_right seq cs skip

let fp2_mul_body =
  seq_list [
    call "bls24_509_mul" [var "v0"; var "inx"; var "iny"];
    call "bls24_509_mul" [var "v1"; add (var "inx") (lit 64); add (var "iny") (lit 64)];
    call "bls24_509_add" [var "v2"; var "inx"; add (var "inx") (lit 64)];
    call "bls24_509_add" [add (var "out") (lit 64); var "iny"; add (var "iny") (lit 64)];
    call "bls24_509_mul" [add (var "out") (lit 64); add (var "out") (lit 64); var "v2"];
    call "bls24_509_sub" [add (var "out") (lit 64); add (var "out") (lit 64); var "v0"];
    call "bls24_509_sub" [add (var "out") (lit 64); add (var "out") (lit 64); var "v1"];
    call "bls24_Fp2_mul_by_nr" [var "v2"; var "v1"];
    call "bls24_509_add" [var "out"; var "v0"; var "v2"];
  ] Coq_cmd.Coq_skip

let fp2_mul_cmd =
  stackalloc "v0" 64
    (stackalloc "v1" 64
      (stackalloc "v2" 64
        fp2_mul_body))

let fp2_mul_func =
  (coq_string "bls24_Fp2_mul",
   ((List.map coq_string ["out"; "inx"; "iny"], []), fp2_mul_cmd))

let () =
  (* Original *)
  let jf = tr_func fp2_mul_func in
  Printf.printf "=== Original (nested stackallocs) ===\n";
  print_string (ocaml_string (pp_func jf));
  Printf.printf "\n";

  (* Flattened *)
  let ff = flatten_func fp2_mul_func in
  let jff = tr_func ff in
  Printf.printf "=== Flattened (single allocation) ===\n";
  print_string (ocaml_string (pp_func jff));
  Printf.printf "\n"
