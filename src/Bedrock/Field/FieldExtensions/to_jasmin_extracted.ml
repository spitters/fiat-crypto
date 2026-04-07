
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

type comparison =
| Eq
| Lt
| Gt

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type signed_int =
| Pos of uint
| Neg of uint

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil

module Little =
 struct
  (** val double : uint -> uint **)

  let rec double = function
  | Nil -> Nil
  | D0 d0 -> D0 (double d0)
  | D1 d0 -> D2 (double d0)
  | D2 d0 -> D4 (double d0)
  | D3 d0 -> D6 (double d0)
  | D4 d0 -> D8 (double d0)
  | D5 d0 -> D0 (succ_double d0)
  | D6 d0 -> D2 (succ_double d0)
  | D7 d0 -> D4 (succ_double d0)
  | D8 d0 -> D6 (succ_double d0)
  | D9 d0 -> D8 (succ_double d0)

  (** val succ_double : uint -> uint **)

  and succ_double = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 (double d0)
  | D1 d0 -> D3 (double d0)
  | D2 d0 -> D5 (double d0)
  | D3 d0 -> D7 (double d0)
  | D4 d0 -> D9 (double d0)
  | D5 d0 -> D1 (succ_double d0)
  | D6 d0 -> D3 (succ_double d0)
  | D7 d0 -> D5 (succ_double d0)
  | D8 d0 -> D7 (succ_double d0)
  | D9 d0 -> D9 (succ_double d0)
 end

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p) (succ p))
      (fun p -> (fun p->1+2*p) p)
      (fun _ -> (fun p->2*p) 1)
      x

  (** val add : int -> int -> int **)

  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun q -> (fun p->2*p) (add p q))
        (fun _ -> (fun p->1+2*p) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (succ q))
        (fun q -> (fun p->1+2*p) q)
        (fun _ -> (fun p->2*p) 1)
        y)
      x

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val mul : int -> int -> int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> add y ((fun p->2*p) (mul p y)))
      (fun p -> (fun p->2*p) (mul p y))
      (fun _ -> y)
      x

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : int -> int -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p
 end

module Coq_Pos =
 struct
  (** val to_little_uint : int -> uint **)

  let rec to_little_uint p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Little.succ_double (to_little_uint p0))
      (fun p0 -> Little.double (to_little_uint p0))
      (fun _ -> D1 Nil)
      p

  (** val to_uint : int -> uint **)

  let to_uint p =
    rev (to_little_uint p)
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: l0 -> fold_left f l0 (f a0 b)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        y)
      x

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul ((fun p->2*p) 1) r) 1 in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q), r')
      else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul ((fun p->2*p) 1) r in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q), r')
      else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun _ -> if leb ((fun p->2*p) 1) b then (0, 1) else (1, 0))
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q), 0))
           (fun _ -> ((opp (add q 1)), (add b r)))
           (fun _ -> ((opp (add q 1)), (add b r)))
           r))
        b)
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun _ ->
        let (q, r) = pos_div_eucl a' b in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q), 0))
           (fun _ -> ((opp (add q 1)), (sub b r)))
           (fun _ -> ((opp (add q 1)), (sub b r)))
           r))
        (fun b' -> let (q, r) = pos_div_eucl a' b' in (q, (opp r)))
        b)
      a

  (** val div : int -> int -> int **)

  let div a b =
    let (q, _) = div_eucl a b in q

  (** val to_int : int -> signed_int **)

  let to_int n =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> Pos (D0 Nil))
      (fun p -> Pos (Coq_Pos.to_uint p))
      (fun p -> Neg (Coq_Pos.to_uint p))
      n
 end

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val concat : char list -> char list list -> char list **)

let rec concat sep = function
| [] -> []
| x :: xs ->
  (match xs with
   | [] -> x
   | _ :: _ -> append x (append sep (concat sep xs)))

module Coq_op1 =
 struct
  type op1 =
  | Coq_not
  | Coq_opp
 end

module Coq_bopname =
 struct
  type bopname =
  | Coq_add
  | Coq_sub
  | Coq_mul
  | Coq_mulhuu
  | Coq_divu
  | Coq_remu
  | Coq_and
  | Coq_or
  | Coq_xor
  | Coq_sru
  | Coq_slu
  | Coq_srs
  | Coq_lts
  | Coq_ltu
  | Coq_eq
 end

module Coq_access_size =
 struct
  type access_size =
  | Coq_one
  | Coq_two
  | Coq_four
  | Coq_word
 end

module Coq_expr =
 struct
  type expr =
  | Coq_literal of int
  | Coq_var of char list
  | Coq_load of Coq_access_size.access_size * expr
  | Coq_inlinetable of Coq_access_size.access_size * char list * expr
  | Coq_op1 of Coq_op1.op1 * expr
  | Coq_op of Coq_bopname.bopname * expr * expr
  | Coq_ite of expr * expr * expr
 end

module Coq_cmd =
 struct
  type cmd =
  | Coq_skip
  | Coq_set of char list * Coq_expr.expr
  | Coq_unset of char list
  | Coq_store of Coq_access_size.access_size * Coq_expr.expr * Coq_expr.expr
  | Coq_stackalloc of char list * int * cmd
  | Coq_cond of Coq_expr.expr * cmd * cmd
  | Coq_seq of cmd * cmd
  | Coq_while of Coq_expr.expr * cmd
  | Coq_call of char list list * char list * Coq_expr.expr list
  | Coq_interact of char list list * char list * Coq_expr.expr list
 end

module NilEmpty =
 struct
  (** val string_of_uint : uint -> char list **)

  let rec string_of_uint = function
  | Nil -> []
  | D0 d0 -> '0'::(string_of_uint d0)
  | D1 d0 -> '1'::(string_of_uint d0)
  | D2 d0 -> '2'::(string_of_uint d0)
  | D3 d0 -> '3'::(string_of_uint d0)
  | D4 d0 -> '4'::(string_of_uint d0)
  | D5 d0 -> '5'::(string_of_uint d0)
  | D6 d0 -> '6'::(string_of_uint d0)
  | D7 d0 -> '7'::(string_of_uint d0)
  | D8 d0 -> '8'::(string_of_uint d0)
  | D9 d0 -> '9'::(string_of_uint d0)
 end

module NilZero =
 struct
  (** val string_of_uint : uint -> char list **)

  let string_of_uint d = match d with
  | Nil -> '0'::[]
  | _ -> NilEmpty.string_of_uint d

  (** val string_of_int : signed_int -> char list **)

  let string_of_int = function
  | Pos d0 -> string_of_uint d0
  | Neg d0 -> '-'::(string_of_uint d0)
 end

type jasmin_type =
| JTu64
| JTptr
| JTstack of int

type jasmin_expr =
| JEvar of char list
| JElit of int
| JEadd of jasmin_expr * jasmin_expr
| JEsub of jasmin_expr * jasmin_expr
| JEmul of jasmin_expr * jasmin_expr
| JEand of jasmin_expr * jasmin_expr
| JEor of jasmin_expr * jasmin_expr
| JExor of jasmin_expr * jasmin_expr
| JEshr of jasmin_expr * jasmin_expr
| JEshl of jasmin_expr * jasmin_expr
| JEload of jasmin_expr * int

type jasmin_cmd =
| JCskip
| JCseq of jasmin_cmd * jasmin_cmd
| JCset of char list * jasmin_expr
| JCstore of jasmin_expr * int * jasmin_expr
| JCcall of char list * jasmin_expr list
| JCif of jasmin_expr * jasmin_cmd * jasmin_cmd
| JCwhile of jasmin_expr * jasmin_cmd
| JCdecl of char list * jasmin_type * jasmin_cmd

type jasmin_func = { jf_name : char list;
                     jf_params : (char list * jasmin_type) list;
                     jf_locals : (char list * jasmin_type) list;
                     jf_body : jasmin_cmd }

(** val tr_expr : Coq_expr.expr -> jasmin_expr **)

let rec tr_expr = function
| Coq_expr.Coq_literal v -> JElit v
| Coq_expr.Coq_var x -> JEvar x
| Coq_expr.Coq_load (_, ea) -> JEload ((tr_expr ea), 0)
| Coq_expr.Coq_op (op, e1, e2) ->
  let e1' = tr_expr e1 in
  let e2' = tr_expr e2 in
  (match op with
   | Coq_bopname.Coq_add -> JEadd (e1', e2')
   | Coq_bopname.Coq_sub -> JEsub (e1', e2')
   | Coq_bopname.Coq_mul -> JEmul (e1', e2')
   | Coq_bopname.Coq_and -> JEand (e1', e2')
   | Coq_bopname.Coq_or -> JEor (e1', e2')
   | Coq_bopname.Coq_xor -> JExor (e1', e2')
   | Coq_bopname.Coq_sru -> JEshr (e1', e2')
   | Coq_bopname.Coq_slu -> JEshl (e1', e2')
   | _ -> JElit 0)
| _ -> JElit 0

(** val tr_cmd : Coq_cmd.cmd -> jasmin_cmd **)

let rec tr_cmd = function
| Coq_cmd.Coq_set (x, e) -> JCset (x, (tr_expr e))
| Coq_cmd.Coq_store (_, ea, ev) -> JCstore ((tr_expr ea), 0, (tr_expr ev))
| Coq_cmd.Coq_stackalloc (x, n, body) ->
  let nwords =
    Z.div (Z.add n ((fun p->1+2*p) ((fun p->1+2*p) 1))) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))
  in
  JCdecl (x, (JTstack nwords), (tr_cmd body))
| Coq_cmd.Coq_cond (e, ct, cf) -> JCif ((tr_expr e), (tr_cmd ct), (tr_cmd cf))
| Coq_cmd.Coq_seq (c1, c2) -> JCseq ((tr_cmd c1), (tr_cmd c2))
| Coq_cmd.Coq_while (e, body) -> JCwhile ((tr_expr e), (tr_cmd body))
| Coq_cmd.Coq_call (_, f, args) -> JCcall (f, (map tr_expr args))
| _ -> JCskip

(** val tr_func :
    (char list * ((char list list * char list list) * Coq_cmd.cmd)) ->
    jasmin_func **)

let tr_func = function
| (name, p) ->
  let (p0, body) = p in
  let (args, _) = p0 in
  { jf_name = name; jf_params = (map (fun a -> (a, JTptr)) args); jf_locals =
  []; jf_body = (tr_cmd body) }

(** val lF : char list **)

let lF =
  '\n'::[]

(** val pp_expr : jasmin_expr -> char list **)

let rec pp_expr = function
| JEvar x -> x
| JElit v ->
  if Z.ltb v 0
  then append ('('::('-'::(' '::[])))
         (append (NilZero.string_of_int (Z.to_int (Z.opp v))) (')'::[]))
  else NilZero.string_of_int (Z.to_int v)
| JEadd (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (' '::('+'::(' '::[]))) (append (pp_expr e2) (')'::[]))))
| JEsub (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (' '::('-'::(' '::[]))) (append (pp_expr e2) (')'::[]))))
| JEmul (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (' '::('*'::(' '::[]))) (append (pp_expr e2) (')'::[]))))
| JEand (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (' '::('&'::(' '::[]))) (append (pp_expr e2) (')'::[]))))
| JEor (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (' '::('|'::(' '::[]))) (append (pp_expr e2) (')'::[]))))
| JExor (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (' '::('^'::(' '::[]))) (append (pp_expr e2) (')'::[]))))
| JEshr (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (' '::('>'::('>'::(' '::[])))) (append (pp_expr e2) (')'::[]))))
| JEshl (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (' '::('<'::('<'::(' '::[])))) (append (pp_expr e2) (')'::[]))))
| JEload (base, off) ->
  let off_str = NilZero.string_of_int (Z.to_int off) in
  append ('('::('u'::('6'::('4'::(')'::('['::[]))))))
    (append (pp_expr base)
      (append (' '::('+'::(' '::[]))) (append off_str (']'::[]))))

(** val pp_type : jasmin_type -> char list **)

let pp_type = function
| JTu64 -> 'r'::('e'::('g'::(' '::('u'::('6'::('4'::[]))))))
| JTptr ->
  'r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('u'::('6'::('4'::('['::('1'::(']'::[])))))))))))))
| JTstack n ->
  append
    ('s'::('t'::('a'::('c'::('k'::(' '::('u'::('6'::('4'::('['::[]))))))))))
    (append (NilZero.string_of_int (Z.to_int n)) (']'::[]))

(** val pp_cmd : char list -> jasmin_cmd -> char list **)

let rec pp_cmd indent = function
| JCskip -> []
| JCseq (c1, c2) -> append (pp_cmd indent c1) (pp_cmd indent c2)
| JCset (x, e) ->
  append indent
    (append x
      (append (' '::('='::(' '::[])))
        (append (pp_expr e) (append (';'::[]) lF))))
| JCstore (base, off, v) ->
  let off_str = NilZero.string_of_int (Z.to_int off) in
  append indent
    (append ('('::('u'::('6'::('4'::(')'::('['::[]))))))
      (append (pp_expr base)
        (append (' '::('+'::(' '::[])))
          (append off_str
            (append (']'::(' '::('='::(' '::[]))))
              (append (pp_expr v) (append (';'::[]) lF)))))))
| JCcall (f, args) ->
  append indent
    (append f
      (append ('('::[])
        (append (concat (','::(' '::[])) (map pp_expr args))
          (append (')'::(';'::[])) lF))))
| JCif (e, ct, cf) ->
  append indent
    (append ('i'::('f'::(' '::('('::[]))))
      (append (pp_expr e)
        (append (' '::('!'::('='::(' '::('0'::(')'::(' '::('{'::[]))))))))
          (append lF
            (append (pp_cmd (append (' '::(' '::[])) indent) ct)
              (append indent
                (append
                  ('}'::(' '::('e'::('l'::('s'::('e'::(' '::('{'::[]))))))))
                  (append lF
                    (append (pp_cmd (append (' '::(' '::[])) indent) cf)
                      (append indent (append ('}'::[]) lF)))))))))))
| JCwhile (e, body) ->
  append indent
    (append ('w'::('h'::('i'::('l'::('e'::(' '::('('::[])))))))
      (append (pp_expr e)
        (append (' '::('!'::('='::(' '::('0'::(')'::(' '::('{'::[]))))))))
          (append lF
            (append (pp_cmd (append (' '::(' '::[])) indent) body)
              (append indent (append ('}'::[]) lF)))))))
| JCdecl (x, ty, body) ->
  append indent
    (append (pp_type ty)
      (append (' '::[])
        (append x (append (';'::[]) (append lF (pp_cmd indent body))))))

(** val pp_func : jasmin_func -> char list **)

let pp_func f =
  append
    ('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('n'::(' '::[]))))))))))
    (append f.jf_name
      (append ('('::[])
        (append
          (concat (','::(' '::[]))
            (map (fun pat ->
              let (name, ty) = pat in
              append (pp_type ty) (append (' '::[]) name)) f.jf_params))
          (append (')'::(' '::('{'::[])))
            (append lF
              (append (pp_cmd (' '::(' '::[])) f.jf_body)
                (append ('}'::[]) lF)))))))

(** val pp_module : jasmin_func list -> char list **)

let pp_module fs =
  concat (append lF lF) (map pp_func fs)

(** val to_jasmin :
    (char list * ((char list list * char list list) * Coq_cmd.cmd)) list ->
    char list **)

let to_jasmin fs =
  pp_module (map tr_func fs)

(** val collect_stackallocs :
    Coq_cmd.cmd -> (char list * int) list * Coq_cmd.cmd **)

let rec collect_stackallocs c = match c with
| Coq_cmd.Coq_stackalloc (x, n, body) ->
  let (rest, inner) = collect_stackallocs body in (((x, n) :: rest), inner)
| _ -> ([], c)

(** val total_size : (char list * int) list -> int **)

let total_size allocs =
  fold_left (fun acc pat -> let (_, n) = pat in Z.add acc n) allocs 0

(** val assign_offsets :
    char list -> (char list * int) list -> int -> Coq_cmd.cmd -> Coq_cmd.cmd **)

let rec assign_offsets frame_var allocs offset body =
  match allocs with
  | [] -> body
  | p :: rest ->
    let (x, n) = p in
    if Z.eqb offset 0
    then Coq_cmd.Coq_seq ((Coq_cmd.Coq_set (x, (Coq_expr.Coq_var
           frame_var))),
           (assign_offsets frame_var rest (Z.add offset n) body))
    else Coq_cmd.Coq_seq ((Coq_cmd.Coq_set (x, (Coq_expr.Coq_op
           (Coq_bopname.Coq_add, (Coq_expr.Coq_var frame_var),
           (Coq_expr.Coq_literal offset))))),
           (assign_offsets frame_var rest (Z.add offset n) body))

(** val frame_var_name : (char list * int) list -> char list **)

let frame_var_name allocs =
  append
    ('_'::('f'::('l'::('a'::('t'::('_'::('f'::('r'::('a'::('m'::('e'::('_'::[]))))))))))))
    (concat ('_'::[]) (map fst allocs))

(** val flatten_stackallocs : Coq_cmd.cmd -> Coq_cmd.cmd **)

let flatten_stackallocs c =
  let (allocs, body) = collect_stackallocs c in
  (match allocs with
   | [] -> c
   | _ :: l ->
     (match l with
      | [] -> c
      | _ :: _ ->
        let frame = frame_var_name allocs in
        let total = total_size allocs in
        Coq_cmd.Coq_stackalloc (frame, total,
        (assign_offsets frame allocs 0 body))))

(** val flatten_func :
    (char list * ((char list list * char list list) * Coq_cmd.cmd)) ->
    char list * ((char list list * char list list) * Coq_cmd.cmd) **)

let flatten_func = function
| (name, p) -> let (p0, body) = p in (name, (p0, (flatten_stackallocs body)))

(** val flatten_selected :
    char list list -> (char list * ((char list list * char list
    list) * Coq_cmd.cmd)) list -> (char list * ((char list list * char list
    list) * Coq_cmd.cmd)) list **)

let flatten_selected target_fns fs =
  map (fun f ->
    if existsb (eqb0 (fst f)) target_fns then flatten_func f else f) fs
