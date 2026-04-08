
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

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

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module Coq_Pos =
 struct
  (** val to_little_uint : positive -> uint **)

  let rec to_little_uint = function
  | XI p0 -> Little.succ_double (to_little_uint p0)
  | XO p0 -> Little.double (to_little_uint p0)
  | XH -> D1 Nil

  (** val to_uint : positive -> uint **)

  let to_uint p =
    rev (to_little_uint p)
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val rev0 : 'a1 list -> 'a1 list **)

let rec rev0 = function
| [] -> []
| x :: l' -> app (rev0 l') (x :: [])

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val to_int : z -> signed_int **)

  let to_int = function
  | Z0 -> Pos (D0 Nil)
  | Zpos p -> Pos (Coq_Pos.to_uint p)
  | Zneg p -> Neg (Coq_Pos.to_uint p)
 end

(** val eqb : char list -> char list -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb s1' s2' else false)

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
| JTptr of z
| JTstack of z

type jasmin_expr =
| JEvar of char list
| JElit of z
| JEadd of jasmin_expr * jasmin_expr
| JEsub of jasmin_expr * jasmin_expr
| JEmul of jasmin_expr * jasmin_expr
| JEmulhuu of jasmin_expr * jasmin_expr
| JEand of jasmin_expr * jasmin_expr
| JEor of jasmin_expr * jasmin_expr
| JExor of jasmin_expr * jasmin_expr
| JEshr of jasmin_expr * jasmin_expr
| JEshl of jasmin_expr * jasmin_expr
| JEltu of jasmin_expr * jasmin_expr
| JEeq of jasmin_expr * jasmin_expr
| JEload of jasmin_expr * z

type jasmin_cmd =
| JCskip
| JCseq of jasmin_cmd * jasmin_cmd
| JCset of char list * jasmin_expr
| JCstore of jasmin_expr * z * jasmin_expr
| JCcall of char list * jasmin_expr list
| JCif of jasmin_expr * jasmin_cmd * jasmin_cmd
| JCwhile of jasmin_expr * jasmin_cmd
| JCdecl of char list * jasmin_type * jasmin_cmd
| JCadd_flags of char list * char list * jasmin_expr * jasmin_expr
| JCadcx of char list * char list * jasmin_expr * jasmin_expr * char list
| JCmulx of char list * char list * jasmin_expr * jasmin_expr

type jasmin_func = { jf_name : char list;
                     jf_params : (char list * jasmin_type) list;
                     jf_locals : (char list * jasmin_type) list;
                     jf_body : jasmin_cmd }

(** val lF : char list **)

let lF =
  '\n'::[]

(** val pp_zlit_u64 : z -> char list **)

let pp_zlit_u64 v =
  let normalized =
    if Z.ltb v Z0
    then Z.add v
           (Z.pow (Zpos (XO XH)) (Zpos (XO (XO (XO (XO (XO (XO XH))))))))
    else v
  in
  NilZero.string_of_int (Z.to_int normalized)

(** val pp_expr : jasmin_expr -> char list **)

let rec pp_expr = function
| JEvar x -> x
| JElit v -> pp_zlit_u64 v
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
| JEmulhuu (e1, e2) ->
  append ('('::('M'::('U'::('L'::('H'::('U'::('U'::(' '::[]))))))))
    (append (pp_expr e1) (append (' '::[]) (append (pp_expr e2) (')'::[]))))
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
| JEltu (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (' '::('<'::('u'::(' '::[])))) (append (pp_expr e2) (')'::[]))))
| JEeq (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (' '::('='::('='::(' '::[])))) (append (pp_expr e2) (')'::[]))))
| JEload (base, off) ->
  let off_str = NilZero.string_of_int (Z.to_int off) in
  append ('['::[])
    (append (pp_expr base)
      (append (' '::('+'::(' '::[]))) (append off_str (']'::[]))))

(** val pp_type : jasmin_type -> char list **)

let pp_type = function
| JTstack n ->
  append
    ('s'::('t'::('a'::('c'::('k'::(' '::('u'::('6'::('4'::('['::[]))))))))))
    (append (NilZero.string_of_int (Z.to_int n)) (']'::[]))
| _ -> 'r'::('e'::('g'::(' '::('u'::('6'::('4'::[]))))))

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
    (append ('['::[])
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
| JCadd_flags (cf, result, a, b) ->
  append indent
    (append ('_'::(','::(' '::[])))
      (append cf
        (append
          (','::(' '::('_'::(','::(' '::('_'::(','::(' '::('_'::(','::(' '::[])))))))))))
          (append result
            (append
              (' '::('='::(' '::('#'::('A'::('D'::('D'::('('::[]))))))))
              (append (pp_expr a)
                (append (','::(' '::[]))
                  (append (pp_expr b) (append (')'::(';'::[])) lF)))))))))
| JCadcx (cf_out, result, a, b, cf_in) ->
  append indent
    (append cf_out
      (append (','::(' '::[]))
        (append result
          (append
            (' '::('='::(' '::('#'::('A'::('D'::('C'::('X'::('('::[])))))))))
            (append (pp_expr a)
              (append (','::(' '::[]))
                (append (pp_expr b)
                  (append (','::(' '::[]))
                    (append cf_in (append (')'::(';'::[])) lF))))))))))
| JCmulx (hi, lo, a, b) ->
  append indent
    (append ('('::[])
      (append hi
        (append (','::(' '::[]))
          (append lo
            (append
              (')'::(' '::('='::(' '::('#'::('M'::('U'::('L'::('X'::('('::[]))))))))))
              (append (pp_expr a)
                (append (','::(' '::[]))
                  (append (pp_expr b) (append (')'::(';'::[])) lF)))))))))

(** val string_in : char list -> char list list -> bool **)

let string_in x xs =
  existsb (eqb x) xs

(** val collect_set_vars : jasmin_cmd -> char list list **)

let rec collect_set_vars = function
| JCseq (c1, c2) -> app (collect_set_vars c1) (collect_set_vars c2)
| JCset (x, _) -> x :: []
| JCif (_, ct, cf) -> app (collect_set_vars ct) (collect_set_vars cf)
| JCwhile (_, body) -> collect_set_vars body
| JCdecl (x, _, body) ->
  filter (fun y -> negb (eqb x y)) (collect_set_vars body)
| JCadd_flags (cf, result, _, _) -> cf :: (result :: [])
| JCadcx (cf_out, result, _, _, _) -> cf_out :: (result :: [])
| JCmulx (hi, lo, _, _) -> hi :: (lo :: [])
| _ -> []

(** val dedup_strings : char list list -> char list list -> char list list **)

let rec dedup_strings acc = function
| [] -> rev0 acc
| x :: rest ->
  if string_in x acc
  then dedup_strings acc rest
  else dedup_strings (x :: acc) rest

(** val function_locals : jasmin_func -> char list list **)

let function_locals f =
  let param_names = map fst f.jf_params in
  let all_set = collect_set_vars f.jf_body in
  let filtered = filter (fun x -> negb (string_in x param_names)) all_set in
  dedup_strings [] filtered

(** val pp_locals_decls : char list -> char list list -> char list **)

let pp_locals_decls indent xs =
  concat []
    (map (fun x ->
      append indent
        (append ('r'::('e'::('g'::(' '::('u'::('6'::('4'::(' '::[]))))))))
          (append x (append (';'::[]) lF))))
      xs)

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
              (append (pp_locals_decls (' '::(' '::[])) (function_locals f))
                (append (pp_cmd (' '::(' '::[])) f.jf_body)
                  (append ('}'::[]) lF))))))))

(** val pp_module : jasmin_func list -> char list **)

let pp_module fs =
  concat (append lF lF) (map pp_func fs)

(** val bn254_opt_jasmin : jasmin_func list **)

let bn254_opt_jasmin =
  { jf_name =
    ('b'::('n'::('2'::('5'::('4'::('_'::('f'::('p'::('1'::('2'::('_'::('m'::('u'::('l'::('_'::('l'::('i'::('n'::('e'::[])))))))))))))))))));
    jf_params = ((('o'::('u'::('t'::[]))), (JTptr (Zpos (XO (XO
    XH))))) :: ((('f'::[]), (JTptr (Zpos (XO (XO
    XH))))) :: ((('l'::('0'::('0'::[]))), (JTptr (Zpos (XO (XO
    XH))))) :: ((('l'::('0'::('1'::[]))), (JTptr (Zpos (XO (XO
    XH))))) :: ((('l'::('1'::('0'::[]))), (JTptr (Zpos (XO (XO
    XH))))) :: []))))); jf_locals = []; jf_body = (JCdecl (('t'::('0'::[])),
    (JTstack (Zpos (XO (XO (XO XH))))), (JCdecl (('t'::('1'::[])), (JTstack
    (Zpos (XO (XO (XO XH))))), (JCdecl (('t'::('2'::[])), (JTstack (Zpos (XO
    (XO (XO XH))))), (JCdecl (('t'::('3'::[])), (JTstack (Zpos (XO (XO (XO
    XH))))), (JCdecl (('t'::('4'::[])), (JTstack (Zpos (XO (XO (XO XH))))),
    (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('0'::[]))) :: ((JEvar ('f'::[])) :: ((JEvar
    ('l'::('0'::('0'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('1'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO XH)))))))))) :: ((JEvar
    ('l'::('0'::('1'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO XH)))))))))) :: ((JEadd ((JEvar ('f'::[])), (JElit
    (Zpos (XO (XO (XO (XO (XO (XO (XO XH))))))))))) :: []))))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('l'::('0'::('1'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('u'::('b'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('1'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::('_'::('x'::('i'::[])))))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: [])))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('o'::('u'::('t'::[])))) :: ((JEvar ('t'::('0'::[]))) :: ((JEvar
    ('t'::('3'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('f'::[])) :: ((JEadd ((JEvar
    ('f'::[])), (JElit (Zpos (XO (XO (XO (XO (XO (XO XH)))))))))) :: []))))),
    (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEvar ('l'::('0'::('0'::[])))) :: ((JEvar
    ('l'::('0'::('1'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('4'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('u'::('b'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('0'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('u'::('b'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('1'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XO (XO XH)))))))))))) :: ((JEvar
    ('l'::('1'::('0'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::('_'::('x'::('i'::[])))))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEvar ('t'::('4'::[]))) :: [])))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEadd ((JEvar ('o'::('u'::('t'::[])))), (JElit (Zpos (XO (XO (XO (XO
    (XO (XO XH)))))))))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('4'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('f'::[])) :: ((JEadd ((JEvar
    ('f'::[])), (JElit (Zpos (XO (XO (XO (XO (XO (XO (XO
    XH))))))))))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('l'::('0'::('0'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('u'::('b'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('0'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('1'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XI (XO XH)))))))))))) :: ((JEvar
    ('l'::('1'::('0'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::('_'::('x'::('i'::[])))))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEvar ('t'::('4'::[]))) :: [])))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEadd ((JEvar ('o'::('u'::('t'::[])))), (JElit (Zpos (XO (XO (XO (XO
    (XO (XO (XO XH))))))))))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('4'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('0'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XI XH))))))))))) :: ((JEvar
    ('l'::('0'::('0'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XI (XO XH)))))))))))) :: ((JEvar
    ('l'::('1'::('0'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::('_'::('x'::('i'::[])))))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: [])))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('0'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XO XH))))))))))) :: ((JEvar
    ('l'::('1'::('0'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::('_'::('x'::('i'::[])))))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEvar ('t'::('4'::[]))) :: [])))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEadd ((JEvar ('o'::('u'::('t'::[])))), (JElit (Zpos (XO (XO (XO (XO
    (XO (XO (XI XH))))))))))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('4'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XI XH))))))))))) :: ((JEvar
    ('l'::('0'::('1'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XO (XO XH)))))))))))) :: ((JEvar
    ('l'::('0'::('0'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('4'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEvar ('f'::[])) :: ((JEvar
    ('l'::('1'::('0'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEadd ((JEvar ('o'::('u'::('t'::[])))), (JElit (Zpos (XO (XO (XO (XO
    (XO (XO (XO (XO XH)))))))))))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('4'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XO (XO XH)))))))))))) :: ((JEvar
    ('l'::('0'::('1'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XI (XO XH)))))))))))) :: ((JEvar
    ('l'::('0'::('0'::[])))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::('3'::[]))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('4'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::[]))))))))))))),
    ((JEvar ('t'::('4'::[]))) :: ((JEadd ((JEvar ('f'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO XH)))))))))) :: ((JEvar
    ('l'::('1'::('0'::[])))) :: []))))), (JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEadd ((JEvar ('o'::('u'::('t'::[])))), (JElit (Zpos (XO (XO (XO (XO
    (XO (XO (XI (XO XH)))))))))))) :: ((JEvar ('t'::('3'::[]))) :: ((JEvar
    ('t'::('4'::[]))) :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) } :: ({ jf_name =
    ('b'::('n'::('2'::('5'::('4'::('_'::('f'::('p'::('1'::('2'::('_'::('c'::('y'::('c'::('_'::('s'::('q'::('r'::[]))))))))))))))))));
    jf_params = ((('o'::('u'::('t'::[]))), (JTptr (Zpos (XO (XO
    XH))))) :: ((('x'::[]), (JTptr (Zpos (XO (XO XH))))) :: [])); jf_locals =
    []; jf_body = (JCdecl (('A'::('0'::[])), (JTstack (Zpos (XO (XO (XO
    XH))))), (JCdecl (('A'::('1'::[])), (JTstack (Zpos (XO (XO (XO XH))))),
    (JCdecl (('A'::('2'::[])), (JTstack (Zpos (XO (XO (XO XH))))), (JCdecl
    (('B'::('0'::[])), (JTstack (Zpos (XO (XO (XO XH))))), (JCdecl
    (('B'::('1'::[])), (JTstack (Zpos (XO (XO (XO XH))))), (JCdecl
    (('B'::('2'::[])), (JTstack (Zpos (XO (XO (XO XH))))), (JCdecl
    (('t'::[]), (JTstack (Zpos (XO (XO (XO XH))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('q'::('u'::('a'::('r'::('e'::[])))))))))))))))),
    ((JEvar ('A'::('0'::[]))) :: ((JEvar ('x'::[])) :: [])))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('q'::('u'::('a'::('r'::('e'::[])))))))))))))))),
    ((JEvar ('A'::('1'::[]))) :: ((JEadd ((JEvar ('x'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO XH)))))))))) :: [])))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('q'::('u'::('a'::('r'::('e'::[])))))))))))))))),
    ((JEvar ('A'::('2'::[]))) :: ((JEadd ((JEvar ('x'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XO XH))))))))))) :: [])))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('q'::('u'::('a'::('r'::('e'::[])))))))))))))))),
    ((JEvar ('B'::('0'::[]))) :: ((JEadd ((JEvar ('x'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XI XH))))))))))) :: [])))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('q'::('u'::('a'::('r'::('e'::[])))))))))))))))),
    ((JEvar ('B'::('1'::[]))) :: ((JEadd ((JEvar ('x'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XO (XO XH)))))))))))) :: [])))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('q'::('u'::('a'::('r'::('e'::[])))))))))))))))),
    ((JEvar ('B'::('2'::[]))) :: ((JEadd ((JEvar ('x'::[])), (JElit (Zpos (XO
    (XO (XO (XO (XO (XO (XI (XO XH)))))))))))) :: [])))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('A'::('0'::[]))) :: ((JEvar
    ('A'::('0'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEvar
    ('A'::('0'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('u'::('b'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEvar
    ('x'::[])) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('u'::('b'::[]))))))))))))),
    ((JEvar ('o'::('u'::('t'::[])))) :: ((JEvar ('t'::[])) :: ((JEvar
    ('x'::[])) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::('_'::('x'::('i'::[])))))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('B'::('2'::[]))) :: [])))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEvar
    ('t'::[])) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEvar
    ('B'::('2'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('m'::('u'::('l'::('_'::('x'::('i'::[])))))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: [])))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEadd ((JEvar ('x'::[])),
    (JElit (Zpos (XO (XO (XO (XO (XO (XO XH)))))))))) :: []))))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEadd ((JEvar ('o'::('u'::('t'::[])))), (JElit (Zpos (XO (XO (XO (XO
    (XO (XO XH)))))))))) :: ((JEvar ('t'::[])) :: ((JEadd ((JEvar ('x'::[])),
    (JElit (Zpos (XO (XO (XO (XO (XO (XO XH)))))))))) :: []))))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('A'::('1'::[]))) :: ((JEvar
    ('A'::('1'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEvar
    ('A'::('1'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('u'::('b'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEadd ((JEvar ('x'::[])),
    (JElit (Zpos (XO (XO (XO (XO (XO (XO (XO XH))))))))))) :: []))))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('u'::('b'::[]))))))))))))),
    ((JEadd ((JEvar ('o'::('u'::('t'::[])))), (JElit (Zpos (XO (XO (XO (XO
    (XO (XO (XO XH))))))))))) :: ((JEvar ('t'::[])) :: ((JEadd ((JEvar
    ('x'::[])), (JElit (Zpos (XO (XO (XO (XO (XO (XO (XO
    XH))))))))))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('B'::('0'::[]))) :: ((JEvar
    ('B'::('0'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEvar
    ('B'::('0'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEadd ((JEvar ('x'::[])),
    (JElit (Zpos (XO (XO (XO (XO (XO (XO (XI XH))))))))))) :: []))))), (JCseq
    ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEadd ((JEvar ('o'::('u'::('t'::[])))), (JElit (Zpos (XO (XO (XO (XO
    (XO (XO (XI XH))))))))))) :: ((JEvar ('t'::[])) :: ((JEadd ((JEvar
    ('x'::[])), (JElit (Zpos (XO (XO (XO (XO (XO (XO (XI
    XH))))))))))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('A'::('2'::[]))) :: ((JEvar
    ('A'::('2'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEvar
    ('A'::('2'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('u'::('b'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEadd ((JEvar ('x'::[])),
    (JElit (Zpos (XO (XO (XO (XO (XO (XO (XO (XO XH)))))))))))) :: []))))),
    (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('s'::('u'::('b'::[]))))))))))))),
    ((JEadd ((JEvar ('o'::('u'::('t'::[])))), (JElit (Zpos (XO (XO (XO (XO
    (XO (XO (XO (XO XH)))))))))))) :: ((JEvar ('t'::[])) :: ((JEadd ((JEvar
    ('x'::[])), (JElit (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
    XH)))))))))))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('B'::('1'::[]))) :: ((JEvar
    ('B'::('1'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEvar
    ('B'::('1'::[]))) :: []))))), (JCseq ((JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEvar ('t'::[])) :: ((JEvar ('t'::[])) :: ((JEadd ((JEvar ('x'::[])),
    (JElit (Zpos (XO (XO (XO (XO (XO (XO (XI (XO XH)))))))))))) :: []))))),
    (JCcall
    (('b'::('n'::('2'::('5'::('4'::('_'::('F'::('p'::('2'::('_'::('a'::('d'::('d'::[]))))))))))))),
    ((JEadd ((JEvar ('o'::('u'::('t'::[])))), (JElit (Zpos (XO (XO (XO (XO
    (XO (XO (XI (XO XH)))))))))))) :: ((JEvar ('t'::[])) :: ((JEadd ((JEvar
    ('x'::[])), (JElit (Zpos (XO (XO (XO (XO (XO (XO (XI (XO
    XH)))))))))))) :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) } :: [])
