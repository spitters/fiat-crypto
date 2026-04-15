
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type reflect =
| ReflectT
| ReflectF

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

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

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val max : nat -> nat -> nat **)

let rec max n0 m =
  match n0 with
  | O -> m
  | S n' -> (match m with
             | O -> n0
             | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n0 m =
  match n0 with
  | O -> O
  | S n' -> (match m with
             | O -> O
             | S m' -> S (min n' m'))

type 't reverseCoercionSource = 't

type 't reverseCoercionTarget = 't

(** val reverse_coercion :
    'a1 -> 'a2 reverseCoercionSource -> 'a1 reverseCoercionTarget **)

let reverse_coercion x' _ =
  x'

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module type DecidableType =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type DecidableTypeOrig =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

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

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos =
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

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

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

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> false)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> false)
    | XH -> (match x0 with
             | XH -> true
             | _ -> false)
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.add p q))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Coq_Pos.mul p q))

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Pos.to_nat p
 end

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b :: l' ->
  N.add (if b then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> nat **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: l0 -> f b (fold_right f a0 l0)

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

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

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

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Pos.of_succ_nat n1)

  (** val eq_dec : z -> z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos p0 -> Coq_Pos.eq_dec p p0
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg p0 -> Coq_Pos.eq_dec p p0
                 | _ -> false)
 end

(* PATCH (2026-04-15): Uint63 axioms realized via jasmin.uint63-native,
   which implements [type t = int].  See BRIDGE_SIMPLE_V2_README.md for
   the equivalent Extract Constant directives that would produce these
   inline at re-extraction time.  The Uint63 [.mli] seals [t], so we go
   through Obj.magic for the bit ops that aren't in the exposed API. *)
type int = Uint63.t

(** val lsl0 : int -> int -> int **)

let lsl0 : int -> int -> int = Obj.magic (Stdlib.(lsl) : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t)

(** val lor0 : int -> int -> int **)

let lor0 : int -> int -> int = Obj.magic (Stdlib.(lor) : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t)

(** val sub0 : int -> int -> int **)

let sub0 : int -> int -> int = Obj.magic (Stdlib.(-) : Stdlib.Int.t -> Stdlib.Int.t -> Stdlib.Int.t)

(** val eqb0 : int -> int -> bool **)

let eqb0 : int -> int -> bool = Uint63.equal

(** val compares : int -> int -> comparison **)

let compares (a : int) (b : int) : comparison =
  let c = Uint63.compares a b in
  if c = 0 then Eq else if c < 0 then Lt else Gt

(** val iffP : bool -> reflect -> reflect **)

let iffP _ pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

(** val equivP : bool -> reflect -> reflect **)

let equivP =
  iffP

type alt_spec =
| AltTrue
| AltFalse

(** val altP : bool -> reflect -> alt_spec **)

let altP _ pb =
  let _evar_0_ = fun _ _ -> AltTrue in
  let _evar_0_0 = fun _ _ -> AltFalse in
  (match pb with
   | ReflectT -> _evar_0_ __ __
   | ReflectF -> _evar_0_0 __ __)

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

(** val boolP : bool -> alt_spec **)

let boolP b1 =
  altP b1 (idP b1)

(** val andP : bool -> bool -> reflect **)

let andP b1 b2 =
  if b1 then if b2 then ReflectT else ReflectF else ReflectF

type 't pred = 't -> bool

type 't predType =
  __ -> 't pred
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

type 't rel = 't -> 't pred

type 't mem_pred = 't pred
  (* singleton inductive, whose constructor was Mem *)

(** val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort **)

let pred_of_mem mp =
  Obj.magic mp

(** val in_mem : 'a1 -> 'a1 mem_pred -> bool **)

let in_mem x mp =
  Obj.magic pred_of_mem mp x

(** val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred **)

let mem pT =
  pT

(** val size : nat **)

let size =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val of_pos_rec : nat -> positive -> int **)

let rec of_pos_rec n0 p =
  match n0 with
  | O -> (Uint63.of_int (0))
  | S n1 ->
    (match p with
     | XI p0 ->
       lor0 (lsl0 (of_pos_rec n1 p0) (Uint63.of_int (1))) (Uint63.of_int (1))
     | XO p0 -> lsl0 (of_pos_rec n1 p0) (Uint63.of_int (1))
     | XH -> (Uint63.of_int (1)))

(** val of_pos : positive -> int **)

let of_pos =
  of_pos_rec size

(** val of_Z : z -> int **)

let of_Z = function
| Z0 -> (Uint63.of_int (0))
| Zpos p -> of_pos p
| Zneg p -> sub0 (Uint63.of_int (0)) (of_pos p)

(** val iffP2 : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> reflect **)

let iffP2 f x1 x2 =
  iffP (f x1 x2) (idP (f x1 x2))

(** val pos_eq_dec : positive -> positive -> bool **)

let rec pos_eq_dec p x0 =
  match p with
  | XI p0 -> (match x0 with
              | XI p1 -> pos_eq_dec p0 p1
              | _ -> false)
  | XO p0 -> (match x0 with
              | XO p1 -> pos_eq_dec p0 p1
              | _ -> false)
  | XH -> (match x0 with
           | XH -> true
           | _ -> false)

(** val eqb_body :
    ('a1 -> positive) -> ('a1 -> 'a3) -> (positive -> 'a2 -> 'a3 -> bool) ->
    positive -> 'a2 -> 'a1 -> bool **)

let eqb_body tagB fieldsB eqb_fields t1 f1 x2 =
  let t2 = tagB x2 in
  if pos_eq_dec t2 t1
  then let f2 = fieldsB x2 in eqb_fields t1 f1 f2
  else false

type 't eq_axiom = 't -> 't -> reflect

module Coq_hasDecEq =
 struct
  type 't axioms_ = { eq_op : 't rel; eqP : 't eq_axiom }

  (** val eq_op : 'a1 axioms_ -> 'a1 rel **)

  let eq_op record =
    record.eq_op

  (** val eqP : 'a1 axioms_ -> 'a1 eq_axiom **)

  let eqP record =
    record.eqP
 end

module Equality =
 struct
  type 't axioms_ =
    't Coq_hasDecEq.axioms_
    (* singleton inductive, whose constructor was Class *)

  (** val eqtype_hasDecEq_mixin : 'a1 axioms_ -> 'a1 Coq_hasDecEq.axioms_ **)

  let eqtype_hasDecEq_mixin record =
    record

  type coq_type =
    __ axioms_
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort axioms_ **)

  let coq_class record =
    record
 end

(** val eq_op0 : Equality.coq_type -> Equality.sort rel **)

let eq_op0 s =
  s.Coq_hasDecEq.eq_op

(** val eqP0 : Equality.coq_type -> Equality.sort eq_axiom **)

let eqP0 s =
  s.Coq_hasDecEq.eqP

(** val pair_eq :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    rel **)

let pair_eq t1 t2 u v =
  (&&) (eq_op0 t1 (fst u) (fst v)) (eq_op0 t2 (snd u) (snd v))

(** val pair_eqP :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    eq_axiom **)

let pair_eqP t1 t2 __top_assumption_ =
  let _evar_0_ = fun x1 x2 __top_assumption_0 ->
    let _evar_0_ = fun y1 y2 ->
      iffP
        ((&&) (eq_op0 t1 (fst (x1, x2)) (fst (y1, y2)))
          (eq_op0 t2 (snd (x1, x2)) (snd (y1, y2))))
        (andP (eq_op0 t1 (fst (x1, x2)) (fst (y1, y2)))
          (eq_op0 t2 (snd (x1, x2)) (snd (y1, y2))))
    in
    let (a, b) = __top_assumption_0 in _evar_0_ a b
  in
  let (a, b) = __top_assumption_ in _evar_0_ a b

(** val hB_unnamed_factory_38 :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    Coq_hasDecEq.axioms_ **)

let hB_unnamed_factory_38 t1 t2 =
  { Coq_hasDecEq.eq_op = (pair_eq t1 t2); Coq_hasDecEq.eqP =
    (pair_eqP t1 t2) }

(** val datatypes_prod__canonical__eqtype_Equality :
    Equality.coq_type -> Equality.coq_type -> Equality.coq_type **)

let datatypes_prod__canonical__eqtype_Equality t1 t2 =
  Obj.magic hB_unnamed_factory_38 t1 t2

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x :: s1' -> x :: (cat s1' s2)

(** val mem_seq :
    Equality.coq_type -> Equality.sort list -> Equality.sort -> bool **)

let rec mem_seq t0 = function
| [] -> (fun _ -> false)
| y :: s' -> let p = mem_seq t0 s' in (fun x -> (||) (eq_op0 t0 x y) (p x))

type seq_eqclass = Equality.sort list

(** val pred_of_seq :
    Equality.coq_type -> seq_eqclass -> Equality.sort pred_sort **)

let pred_of_seq t0 s =
  Obj.magic mem_seq t0 s

(** val seq_predType : Equality.coq_type -> Equality.sort predType **)

let seq_predType t0 =
  Obj.magic pred_of_seq t0

type 't eqTypeC = { beq : ('t -> 't -> bool); ceqP : 't eq_axiom }

type ('e, 'a) result =
| Ok of 'a
| Error of 'e

type assertion_label = char list

type error =
| ErrOob
| ErrAddrUndef
| ErrAddrInvalid
| ErrStack
| ErrType
| ErrArith
| ErrSemUndef
| ErrAssert of assertion_label

type 't exec = (error, 't) result

(** val positive_tag : positive -> positive **)

let positive_tag = function
| XI _ -> XH
| XO _ -> XO XH
| XH -> XI XH

type box_positive_xH =
| Box_positive_xH

type positive_fields_t = __

(** val positive_fields : positive -> positive_fields_t **)

let positive_fields = function
| XI h -> Obj.magic h
| XO h -> Obj.magic h
| XH -> Obj.magic Box_positive_xH

(** val positive_eqb_fields :
    (positive -> positive -> bool) -> positive -> positive_fields_t ->
    positive_fields_t -> bool **)

let positive_eqb_fields rec0 x a b =
  match x with
  | XI _ -> true
  | _ -> (&&) (rec0 (Obj.magic a) (Obj.magic b)) true

(** val positive_eqb : positive -> positive -> bool **)

let rec positive_eqb x1 x2 =
  match x1 with
  | XI h ->
    eqb_body positive_tag positive_fields
      (Obj.magic positive_eqb_fields positive_eqb) (positive_tag (XI h)) h x2
  | XO h ->
    eqb_body positive_tag positive_fields
      (Obj.magic positive_eqb_fields positive_eqb) (positive_tag (XO h)) h x2
  | XH ->
    eqb_body positive_tag positive_fields
      (Obj.magic positive_eqb_fields positive_eqb) (positive_tag XH)
      Box_positive_xH x2

type 'tr lprod = __

type ltuple = __

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module type Coq_DecidableType =
 DecidableTypeOrig

module WFacts_fun =
 functor (E:Coq_DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 struct
  (** val eqb : E.t -> E.t -> bool **)

  let eqb x y =
    if E.eq_dec x y then true else false

  (** val coq_In_dec : 'a1 M.t -> M.key -> bool **)

  let coq_In_dec m x =
    let b = M.mem x m in if b then true else false
 end

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p :: l ->
    let (k', _) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p :: s' ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | [] -> (k, x) :: []
  | p :: l ->
    let (k', y) = p in
    (match X.compare k k' with
     | LT -> (k, x) :: s
     | EQ -> (k, x) :: l
     | GT -> (k', y) :: (add k x l))

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p :: l ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k', x) :: (remove k l))

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p :: m' -> let (k, e) = p in fold f m' (f k e acc)

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp0 m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _ :: _ -> false)
    | p :: l ->
      let (x, e) = p in
      (match m' with
       | [] -> false
       | p0 :: l' ->
         let (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> (&&) (cmp0 e e') (equal cmp0 l l')
          | _ -> false))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f k e)) :: (mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> (k, e) :: l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p :: l -> let (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p :: l' ->
    let (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p :: l ->
    let (k, e) = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> (None, (Some e')))
  | p :: l ->
    let (k, e) = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> ((Some e0), None)) m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> (k, ((Some e), None)) :: (combine l m')
       | EQ -> (k, ((Some e), (Some e'))) :: (combine l l')
       | GT -> (k', (None, (Some e'))) :: (combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module type Int =
 sig
  type t

  val i2z : t -> z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = z

  (** val _0 : z **)

  let _0 =
    Z0

  (** val _1 : z **)

  let _1 =
    Zpos XH

  (** val _2 : z **)

  let _2 =
    Zpos (XO XH)

  (** val _3 : z **)

  let _3 =
    Zpos (XI XH)

  (** val add : z -> z -> z **)

  let add =
    Z.add

  (** val opp : z -> z **)

  let opp =
    Z.opp

  (** val sub : z -> z -> z **)

  let sub =
    Z.sub

  (** val mul : z -> z -> z **)

  let mul =
    Z.mul

  (** val max : z -> z -> z **)

  let max =
    Z.max

  (** val eqb : z -> z -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : z -> z -> bool **)

  let ltb =
    Z.ltb

  (** val leb : z -> z -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : z -> z -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : z -> z -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : z -> z -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> z **)

  let i2z n0 =
    n0
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rect f f0 t1) k y t2 (tree_rect f f0 t2) t3

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rec f f0 t1) k y t2 (tree_rec f f0 t2) t3

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, _, _, r, _) -> S (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x d r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d r)
            else (match lr with
                  | Leaf -> assert_false l x d r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x d r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> (r, (x, d))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p) = remove_min l2 x2 d2 r2 in
         let (x, d) = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x d r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t0 =
    t0.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t0 =
    t0.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) -> elements_aux ((x, d) :: (elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp0 x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp0 d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp0 m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp0 l1 (equal_more cmp0 x1 d1 (equal_cont cmp0 r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp0 m1 m2 =
    equal_cont cmp0 m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x, e0, t0, r) -> (x, e0) :: (app (elements t0) (flatten_e r))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty =
    Raw.is_empty

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add =
    Raw.add

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove =
    Raw.remove

  (** val mem : key -> 'a1 t -> bool **)

  let mem =
    Raw.mem

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find =
    Raw.find

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map =
    Raw.map

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi =
    Raw.mapi

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 =
    Raw.map2

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements =
    Raw.elements

  (** val cardinal : 'a1 t -> nat **)

  let cardinal =
    Raw.cardinal

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold =
    Raw.fold

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal =
    Raw.equal
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

module type WSets =
 sig
  module E :
   DecidableType

  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end

module WFactsOn =
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end) ->
 struct
  (** val eqb : E.t -> E.t -> bool **)

  let eqb x y =
    if E.eq_dec x y then true else false
 end

module WDecideOn =
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end) ->
 struct
  module F = WFactsOn(E)(M)

  module MSetLogicalFacts =
   struct
   end

  module MSetDecideAuxiliary =
   struct
   end

  module MSetDecideTestCases =
   struct
   end
 end

module WDecide =
 functor (M:WSets) ->
 WDecideOn(M.E)(M)

module WPropertiesOn =
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end) ->
 struct
  module Dec = WDecideOn(E)(M)

  module FM = Dec.F

  (** val coq_In_dec : M.elt -> M.t -> bool **)

  let coq_In_dec x s =
    if M.mem x s then true else false

  (** val of_list : M.elt list -> M.t **)

  let of_list l =
    fold_right M.add M.empty l

  (** val to_list : M.t -> M.elt list **)

  let to_list =
    M.elements

  (** val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
      'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2 **)

  let fold_rec f i s pempty pstep =
    let l = rev (M.elements s) in
    let pstep' = fun x a s' s'' x0 -> pstep x a s' s'' __ __ __ x0 in
    let rec f0 l0 pstep'0 s0 =
      match l0 with
      | [] -> pempty s0 __
      | y :: l1 ->
        pstep'0 y (fold_right f i l1) (of_list l1) s0 __ __ __
          (f0 l1 (fun x a s' s'' _ _ _ x0 -> pstep'0 x a s' s'' __ __ __ x0)
            (of_list l1))
    in f0 l (fun x a s' s'' _ _ _ x0 -> pstep' x a s' s'' x0) s

  (** val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2 **)

  let fold_rec_bis f i s pmorphism pempty pstep =
    fold_rec f i s (fun s' _ -> pmorphism M.empty s' i __ pempty)
      (fun x a s' s'' _ _ _ x0 ->
      pmorphism (M.add x s') s'' (f x a) __ (pstep x a s' __ __ x0))

  (** val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2 **)

  let fold_rec_nodep f i s x x0 =
    fold_rec_bis f i s (fun _ _ _ _ x1 -> x1) x (fun x1 a _ _ _ x2 ->
      x0 x1 a __ x2)

  (** val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2 **)

  let fold_rec_weak f i x x0 x1 s =
    fold_rec_bis f i s x x0 (fun x2 a s' _ _ x3 -> x1 x2 a s' __ x3)

  (** val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
      'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 **)

  let fold_rel f g i j s rempty rstep =
    let l = rev (M.elements s) in
    let rstep' = fun x a b x0 -> rstep x a b __ x0 in
    let rec f0 l0 rstep'0 =
      match l0 with
      | [] -> rempty
      | y :: l1 ->
        rstep'0 y (fold_right f i l1) (fold_right g j l1) __
          (f0 l1 (fun x a0 b _ x0 -> rstep'0 x a0 b __ x0))
    in f0 l (fun x a b _ x0 -> rstep' x a b x0)

  (** val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
      -> M.t -> 'a1 **)

  let set_induction x x0 s =
    fold_rec (fun _ _ -> ()) () s x (fun x1 _ s' s'' _ _ _ x2 ->
      x0 s' s'' x2 x1 __ __)

  (** val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
      -> 'a1) -> M.t -> 'a1 **)

  let set_induction_bis x x0 x1 s =
    fold_rec_bis (fun _ _ -> ()) () s (fun s0 s' _ _ x2 -> x s0 s' __ x2) x0
      (fun x2 _ s' _ _ x3 -> x1 x2 s' __ x3)

  (** val cardinal_inv_2 : M.t -> nat -> M.elt **)

  let cardinal_inv_2 s _ =
    let l = M.elements s in
    (match l with
     | [] -> assert false (* absurd case *)
     | e :: _ -> e)

  (** val cardinal_inv_2b : M.t -> M.elt **)

  let cardinal_inv_2b s =
    let n0 = M.cardinal s in
    let x = fun x -> cardinal_inv_2 s x in
    (match n0 with
     | O -> assert false (* absurd case *)
     | S n1 -> x n1)
 end

module WEqPropertiesOn =
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end) ->
 struct
  module MP = WPropertiesOn(E)(M)

  (** val choose_mem_3 : M.t -> M.elt **)

  let choose_mem_3 s =
    let o = M.choose s in
    (match o with
     | Some e -> e
     | None -> assert false (* absurd case *))

  (** val set_rec :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> (M.t -> M.elt -> __ -> 'a1 -> 'a1)
      -> 'a1 -> M.t -> 'a1 **)

  let set_rec x x0 x1 s =
    MP.set_induction (fun s0 _ -> x M.empty s0 __ x1) (fun s0 s' x2 x3 _ _ ->
      x (M.add x3 s0) s' __ (x0 s0 x3 __ x2)) s

  (** val for_all_mem_4 : (M.elt -> bool) -> M.t -> M.elt **)

  let for_all_mem_4 f s =
    choose_mem_3 (M.filter (fun x -> negb (f x)) s)

  (** val exists_mem_4 : (M.elt -> bool) -> M.t -> M.elt **)

  let exists_mem_4 f s =
    for_all_mem_4 (fun x -> negb (f x)) s

  (** val sum : (M.elt -> nat) -> M.t -> nat **)

  let sum f s =
    M.fold (fun x -> add (f x)) s O
 end

module WEqProperties =
 functor (M:WSets) ->
 WEqPropertiesOn(M.E)(M)

module EqProperties = WEqProperties

module type CmpType =
 sig
  val t : Equality.coq_type

  val cmp : Equality.sort -> Equality.sort -> comparison
 end

module MkOrdT =
 functor (T:CmpType) ->
 struct
  type t = Equality.sort

  (** val compare :
      Equality.sort -> Equality.sort -> Equality.sort compare0 **)

  let compare x y =
    let c = T.cmp x y in (match c with
                          | Eq -> EQ
                          | Lt -> LT
                          | Gt -> GT)

  (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

  let eq_dec x y =
    let _evar_0_ = true in
    let _evar_0_0 = false in
    let _evar_0_1 = false in
    (match T.cmp x y with
     | Eq -> _evar_0_
     | Lt -> _evar_0_0
     | Gt -> _evar_0_1)
 end

module type MAP =
 sig
  module K :
   CmpType

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val get : 'a1 t -> Equality.sort -> 'a1 option

  val set : 'a1 t -> Equality.sort -> 'a1 -> 'a1 t

  val remove : 'a1 t -> Equality.sort -> 'a1 t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (Equality.sort -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2
    t -> 'a3 t

  val filter_map : (Equality.sort -> 'a1 -> 'a2 option) -> 'a1 t -> 'a2 t

  val incl_def :
    (Equality.sort -> 'a1 -> bool) -> (Equality.sort -> 'a1 -> 'a2 -> bool)
    -> 'a1 t -> 'a2 t -> bool

  val incl : (Equality.sort -> 'a1 -> 'a2 -> bool) -> 'a1 t -> 'a2 t -> bool

  val all : (Equality.sort -> 'a1 -> bool) -> 'a1 t -> bool

  val has : (Equality.sort -> 'a1 -> bool) -> 'a1 t -> bool

  val elements : 'a1 t -> (Equality.sort * 'a1) list

  val fold : (Equality.sort -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val in_codom : Equality.coq_type -> Equality.sort -> Equality.sort t -> bool

  val is_emptyP : 'a1 t -> reflect

  val elementsP :
    Equality.coq_type -> (Equality.sort * Equality.sort) -> Equality.sort t
    -> reflect
 end

module Mmake =
 functor (K':CmpType) ->
 struct
  module K = K'

  module Ordered = MkOrdT(K)

  module Map = Make(Ordered)

  module Facts = WFacts_fun(Ordered)(Map)

  type 't t = 't Map.t

  (** val empty : 'a1 t **)

  let empty =
    Map.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty =
    Map.is_empty

  (** val get : 'a1 t -> Equality.sort -> 'a1 option **)

  let get m k =
    Map.find k m

  (** val set : 'a1 t -> Equality.sort -> 'a1 -> 'a1 Map.t **)

  let set m k v =
    Map.add k v m

  (** val remove : 'a1 t -> Equality.sort -> 'a1 Map.t **)

  let remove m k =
    Map.remove k m

  (** val map : ('a1 -> 'a2) -> 'a1 Map.t -> 'a2 Map.t **)

  let map =
    Map.map

  (** val mapi : (Map.key -> 'a1 -> 'a2) -> 'a1 Map.t -> 'a2 Map.t **)

  let mapi =
    Map.mapi

  (** val raw_map2 :
      (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1
      Map.Raw.tree -> 'a2 Map.Raw.tree -> 'a3 Map.Raw.tree **)

  let raw_map2 f m1 m2 =
    Map.Raw.map2_opt (fun k d o -> f k (Some d) o)
      (Map.Raw.map_option (fun k d -> f k (Some d) None))
      (Map.Raw.map_option (fun k d' -> f k None (Some d'))) m1 m2

  (** val elements : 'a1 Map.t -> (Map.key * 'a1) list **)

  let elements =
    Map.elements

  (** val fold : (Map.key -> 'a1 -> 'a2 -> 'a2) -> 'a1 Map.t -> 'a2 -> 'a2 **)

  let fold =
    Map.fold

  (** val all_t :
      (Equality.sort -> 'a1 -> bool) -> 'a1 Map.Raw.tree -> bool **)

  let rec all_t f = function
  | Map.Raw.Leaf -> true
  | Map.Raw.Node (t1, k, x, t2, _) ->
    (&&) ((&&) (f k x) (all_t f t1)) (all_t f t2)

  (** val has_t :
      (Equality.sort -> 'a1 -> bool) -> 'a1 Map.Raw.tree -> bool **)

  let rec has_t f = function
  | Map.Raw.Leaf -> false
  | Map.Raw.Node (t1, k, x, t2, _) ->
    (||) ((||) (f k x) (has_t f t1)) (has_t f t2)

  (** val incl_t :
      (Equality.sort -> 'a1 -> bool) -> (Equality.sort -> 'a1 -> 'a2 -> bool)
      -> 'a1 Map.Raw.tree -> 'a2 Map.Raw.tree -> bool **)

  let rec incl_t f f2 t1 t2 =
    match t1 with
    | Map.Raw.Leaf -> true
    | Map.Raw.Node (t11, k, x1, t12, _) ->
      let { Map.Raw.t_left = t21; Map.Raw.t_opt = ox2; Map.Raw.t_right =
        t22 } = Map.Raw.split k t2
      in
      (&&) (match ox2 with
            | Some x2 -> f2 k x1 x2
            | None -> f k x1)
        ((&&) (incl_t f f2 t11 t21) (incl_t f f2 t12 t22))

  (** val all : (Equality.sort -> 'a1 -> bool) -> 'a1 t -> bool **)

  let all f m =
    all_t f (Map.this m)

  (** val has : (Equality.sort -> 'a1 -> bool) -> 'a1 t -> bool **)

  let has f m =
    has_t f (Map.this m)

  (** val incl_def :
      (Equality.sort -> 'a1 -> bool) -> (Equality.sort -> 'a1 -> 'a2 -> bool)
      -> 'a1 Map.bst -> 'a2 Map.bst -> bool **)

  let incl_def f f2 m1 m2 =
    incl_t f f2 (Map.this m1) (Map.this m2)

  (** val incl :
      (Equality.sort -> 'a1 -> 'a2 -> bool) -> 'a1 Map.bst -> 'a2 Map.bst ->
      bool **)

  let incl f2 =
    incl_def (fun _ _ -> false) f2

  (** val in_codom :
      Equality.coq_type -> Equality.sort -> Equality.sort t -> bool **)

  let in_codom t0 v m =
    has (fun _ v' -> eq_op0 t0 v v') m

  (** val map2 :
      (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1 t ->
      'a2 t -> 'a3 t **)

  let map2 f m1 m2 =
    raw_map2 f (Map.this m1) (Map.this m2)

  (** val filter_map :
      (Equality.sort -> 'a1 -> 'a2 option) -> 'a1 t -> 'a2 t **)

  let filter_map f m =
    Map.Raw.map_option f (Map.this m)

  (** val is_emptyP : 'a1 t -> reflect **)

  let is_emptyP m =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if Map.Raw.is_empty (Map.this m) then _evar_0_ __ else _evar_0_0 __

  (** val elementsP :
      Equality.coq_type -> (Equality.sort * Equality.sort) -> Equality.sort t
      -> reflect **)

  let elementsP t0 kv m =
    let _evar_0_ = fun _ _ -> ReflectT in
    let _evar_0_0 = fun _ _ -> ReflectF in
    (match boolP
             (in_mem (Obj.magic kv)
               (mem
                 (seq_predType
                   (datatypes_prod__canonical__eqtype_Equality K.t t0))
                 (Obj.magic Map.elements m))) with
     | AltTrue -> _evar_0_ __ __
     | AltFalse -> _evar_0_0 __ __)
 end

module MkMOrdT =
 functor (T:CmpType) ->
 struct
  type t = Equality.sort

  (** val compare : t -> t -> comparison **)

  let compare =
    T.cmp

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    let _evar_0_ = fun _ -> true in
    let _evar_0_0 = fun _ -> false in
    (match eqP0 T.t x y with
     | ReflectT -> _evar_0_ __
     | ReflectF -> _evar_0_0 __)
 end

module Smake =
 functor (T:CmpType) ->
 struct
  module Ordered = MkMOrdT(T)

  module Raw =
   struct
    type elt = Equality.sort

    type tree =
    | Leaf
    | Node of Z_as_Int.t * tree * Equality.sort * tree

    (** val empty : tree **)

    let empty =
      Leaf

    (** val is_empty : tree -> bool **)

    let is_empty = function
    | Leaf -> true
    | Node (_, _, _, _) -> false

    (** val mem : Equality.sort -> tree -> bool **)

    let rec mem x = function
    | Leaf -> false
    | Node (_, l, k, r) ->
      (match T.cmp x k with
       | Eq -> true
       | Lt -> mem x l
       | Gt -> mem x r)

    (** val min_elt : tree -> elt option **)

    let rec min_elt = function
    | Leaf -> None
    | Node (_, l, x, _) ->
      (match l with
       | Leaf -> Some x
       | Node (_, _, _, _) -> min_elt l)

    (** val max_elt : tree -> elt option **)

    let rec max_elt = function
    | Leaf -> None
    | Node (_, _, x, r) ->
      (match r with
       | Leaf -> Some x
       | Node (_, _, _, _) -> max_elt r)

    (** val choose : tree -> elt option **)

    let choose =
      min_elt

    (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)

    let rec fold f t0 base =
      match t0 with
      | Leaf -> base
      | Node (_, l, x, r) -> fold f r (f x (fold f l base))

    (** val elements_aux :
        Equality.sort list -> tree -> Equality.sort list **)

    let rec elements_aux acc = function
    | Leaf -> acc
    | Node (_, l, x, r) -> elements_aux (x :: (elements_aux acc r)) l

    (** val elements : tree -> Equality.sort list **)

    let elements =
      elements_aux []

    (** val rev_elements_aux :
        Equality.sort list -> tree -> Equality.sort list **)

    let rec rev_elements_aux acc = function
    | Leaf -> acc
    | Node (_, l, x, r) -> rev_elements_aux (x :: (rev_elements_aux acc l)) r

    (** val rev_elements : tree -> Equality.sort list **)

    let rev_elements =
      rev_elements_aux []

    (** val cardinal : tree -> nat **)

    let rec cardinal = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (add (cardinal l) (cardinal r))

    (** val maxdepth : tree -> nat **)

    let rec maxdepth = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (max (maxdepth l) (maxdepth r))

    (** val mindepth : tree -> nat **)

    let rec mindepth = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (min (mindepth l) (mindepth r))

    (** val for_all : (elt -> bool) -> tree -> bool **)

    let rec for_all f = function
    | Leaf -> true
    | Node (_, l, x, r) ->
      if if f x then for_all f l else false then for_all f r else false

    (** val exists_ : (elt -> bool) -> tree -> bool **)

    let rec exists_ f = function
    | Leaf -> false
    | Node (_, l, x, r) ->
      if if f x then true else exists_ f l then true else exists_ f r

    type enumeration =
    | End
    | More of elt * tree * enumeration

    (** val cons : tree -> enumeration -> enumeration **)

    let rec cons s e =
      match s with
      | Leaf -> e
      | Node (_, l, x, r) -> cons l (More (x, r, e))

    (** val compare_more :
        Equality.sort -> (enumeration -> comparison) -> enumeration ->
        comparison **)

    let compare_more x1 cont = function
    | End -> Gt
    | More (x2, r2, e3) ->
      (match T.cmp x1 x2 with
       | Eq -> cont (cons r2 e3)
       | x -> x)

    (** val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison **)

    let rec compare_cont s1 cont e2 =
      match s1 with
      | Leaf -> cont e2
      | Node (_, l1, x1, r1) ->
        compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2

    (** val compare_end : enumeration -> comparison **)

    let compare_end = function
    | End -> Eq
    | More (_, _, _) -> Lt

    (** val compare : tree -> tree -> comparison **)

    let compare s1 s2 =
      compare_cont s1 compare_end (cons s2 End)

    (** val equal : tree -> tree -> bool **)

    let equal s1 s2 =
      match compare s1 s2 with
      | Eq -> true
      | _ -> false

    (** val subsetl : (tree -> bool) -> Equality.sort -> tree -> bool **)

    let rec subsetl subset_l1 x1 s2 = match s2 with
    | Leaf -> false
    | Node (_, l2, x2, r2) ->
      (match T.cmp x1 x2 with
       | Eq -> subset_l1 l2
       | Lt -> subsetl subset_l1 x1 l2
       | Gt -> if mem x1 r2 then subset_l1 s2 else false)

    (** val subsetr : (tree -> bool) -> Equality.sort -> tree -> bool **)

    let rec subsetr subset_r1 x1 s2 = match s2 with
    | Leaf -> false
    | Node (_, l2, x2, r2) ->
      (match T.cmp x1 x2 with
       | Eq -> subset_r1 r2
       | Lt -> if mem x1 l2 then subset_r1 s2 else false
       | Gt -> subsetr subset_r1 x1 r2)

    (** val subset : tree -> tree -> bool **)

    let rec subset s1 s2 =
      match s1 with
      | Leaf -> true
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> false
         | Node (_, l2, x2, r2) ->
           (match T.cmp x1 x2 with
            | Eq -> if subset l1 l2 then subset r1 r2 else false
            | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
            | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))

    type t = tree

    (** val height : t -> Z_as_Int.t **)

    let height = function
    | Leaf -> Z_as_Int._0
    | Node (h, _, _, _) -> h

    (** val singleton : Equality.sort -> tree **)

    let singleton x =
      Node (Z_as_Int._1, Leaf, x, Leaf)

    (** val create : t -> Equality.sort -> t -> tree **)

    let create l x r =
      Node ((Z_as_Int.add (Z_as_Int.max (height l) (height r)) Z_as_Int._1),
        l, x, r)

    (** val assert_false : t -> Equality.sort -> t -> tree **)

    let assert_false =
      create

    (** val bal : t -> Equality.sort -> t -> tree **)

    let bal l x r =
      let hl = height l in
      let hr = height r in
      if Z_as_Int.ltb (Z_as_Int.add hr Z_as_Int._2) hl
      then (match l with
            | Leaf -> assert_false l x r
            | Node (_, ll, lx, lr) ->
              if Z_as_Int.leb (height lr) (height ll)
              then create ll lx (create lr x r)
              else (match lr with
                    | Leaf -> assert_false l x r
                    | Node (_, lrl, lrx, lrr) ->
                      create (create ll lx lrl) lrx (create lrr x r)))
      else if Z_as_Int.ltb (Z_as_Int.add hl Z_as_Int._2) hr
           then (match r with
                 | Leaf -> assert_false l x r
                 | Node (_, rl, rx, rr) ->
                   if Z_as_Int.leb (height rl) (height rr)
                   then create (create l x rl) rx rr
                   else (match rl with
                         | Leaf -> assert_false l x r
                         | Node (_, rll, rlx, rlr) ->
                           create (create l x rll) rlx (create rlr rx rr)))
           else create l x r

    (** val add : Equality.sort -> tree -> tree **)

    let rec add x = function
    | Leaf -> Node (Z_as_Int._1, Leaf, x, Leaf)
    | Node (h, l, y, r) ->
      (match T.cmp x y with
       | Eq -> Node (h, l, y, r)
       | Lt -> bal (add x l) y r
       | Gt -> bal l y (add x r))

    (** val join : tree -> elt -> t -> t **)

    let rec join l = match l with
    | Leaf -> add
    | Node (lh, ll, lx, lr) ->
      (fun x ->
        let rec join_aux r = match r with
        | Leaf -> add x l
        | Node (rh, rl, rx, rr) ->
          if Z_as_Int.ltb (Z_as_Int.add rh Z_as_Int._2) lh
          then bal ll lx (join lr x r)
          else if Z_as_Int.ltb (Z_as_Int.add lh Z_as_Int._2) rh
               then bal (join_aux rl) rx rr
               else create l x r
        in join_aux)

    (** val remove_min : tree -> elt -> t -> t * elt **)

    let rec remove_min l x r =
      match l with
      | Leaf -> (r, x)
      | Node (_, ll, lx, lr) ->
        let (l', m) = remove_min ll lx lr in ((bal l' x r), m)

    (** val merge : tree -> tree -> tree **)

    let merge s1 s2 =
      match s1 with
      | Leaf -> s2
      | Node (_, _, _, _) ->
        (match s2 with
         | Leaf -> s1
         | Node (_, l2, x2, r2) ->
           let (s2', m) = remove_min l2 x2 r2 in bal s1 m s2')

    (** val remove : Equality.sort -> tree -> tree **)

    let rec remove x = function
    | Leaf -> Leaf
    | Node (_, l, y, r) ->
      (match T.cmp x y with
       | Eq -> merge l r
       | Lt -> bal (remove x l) y r
       | Gt -> bal l y (remove x r))

    (** val concat : tree -> tree -> tree **)

    let concat s1 s2 =
      match s1 with
      | Leaf -> s2
      | Node (_, _, _, _) ->
        (match s2 with
         | Leaf -> s1
         | Node (_, l2, x2, r2) ->
           let (s2', m) = remove_min l2 x2 r2 in join s1 m s2')

    type triple = { t_left : t; t_in : bool; t_right : t }

    (** val t_left : triple -> t **)

    let t_left t0 =
      t0.t_left

    (** val t_in : triple -> bool **)

    let t_in t0 =
      t0.t_in

    (** val t_right : triple -> t **)

    let t_right t0 =
      t0.t_right

    (** val split : Equality.sort -> tree -> triple **)

    let rec split x = function
    | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
    | Node (_, l, y, r) ->
      (match T.cmp x y with
       | Eq -> { t_left = l; t_in = true; t_right = r }
       | Lt ->
         let { t_left = ll; t_in = b; t_right = rl } = split x l in
         { t_left = ll; t_in = b; t_right = (join rl y r) }
       | Gt ->
         let { t_left = rl; t_in = b; t_right = rr } = split x r in
         { t_left = (join l y rl); t_in = b; t_right = rr })

    (** val inter : tree -> tree -> tree **)

    let rec inter s1 s2 =
      match s1 with
      | Leaf -> Leaf
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> Leaf
         | Node (_, _, _, _) ->
           let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
           if pres
           then join (inter l1 l2') x1 (inter r1 r2')
           else concat (inter l1 l2') (inter r1 r2'))

    (** val diff : tree -> tree -> tree **)

    let rec diff s1 s2 =
      match s1 with
      | Leaf -> Leaf
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> s1
         | Node (_, _, _, _) ->
           let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
           if pres
           then concat (diff l1 l2') (diff r1 r2')
           else join (diff l1 l2') x1 (diff r1 r2'))

    (** val union : tree -> tree -> tree **)

    let rec union s1 s2 =
      match s1 with
      | Leaf -> s2
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> s1
         | Node (_, _, _, _) ->
           let { t_left = l2'; t_in = _; t_right = r2' } = split x1 s2 in
           join (union l1 l2') x1 (union r1 r2'))

    (** val filter : (elt -> bool) -> tree -> tree **)

    let rec filter f = function
    | Leaf -> Leaf
    | Node (_, l, x, r) ->
      let l' = filter f l in
      let r' = filter f r in if f x then join l' x r' else concat l' r'

    (** val partition : (elt -> bool) -> t -> t * t **)

    let rec partition f = function
    | Leaf -> (Leaf, Leaf)
    | Node (_, l, x, r) ->
      let (l1, l2) = partition f l in
      let (r1, r2) = partition f r in
      if f x
      then ((join l1 x r1), (concat l2 r2))
      else ((concat l1 r1), (join l2 x r2))

    (** val ltb_tree : Equality.sort -> tree -> bool **)

    let rec ltb_tree x = function
    | Leaf -> true
    | Node (_, l, y, r) ->
      (match T.cmp x y with
       | Gt -> (&&) (ltb_tree x l) (ltb_tree x r)
       | _ -> false)

    (** val gtb_tree : Equality.sort -> tree -> bool **)

    let rec gtb_tree x = function
    | Leaf -> true
    | Node (_, l, y, r) ->
      (match T.cmp x y with
       | Lt -> (&&) (gtb_tree x l) (gtb_tree x r)
       | _ -> false)

    (** val isok : tree -> bool **)

    let rec isok = function
    | Leaf -> true
    | Node (_, l, x, r) ->
      (&&) ((&&) ((&&) (isok l) (isok r)) (ltb_tree x l)) (gtb_tree x r)

    module MX =
     struct
      module OrderTac =
       struct
        module OTF =
         struct
          type t = Equality.sort

          (** val compare : Equality.sort -> Equality.sort -> comparison **)

          let compare =
            T.cmp

          (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

          let eq_dec =
            Ordered.eq_dec
         end

        module TO =
         struct
          type t = Equality.sort

          (** val compare : Equality.sort -> Equality.sort -> comparison **)

          let compare =
            T.cmp

          (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

          let eq_dec =
            OTF.eq_dec
         end
       end

      (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

      let eq_dec =
        Ordered.eq_dec

      (** val lt_dec : Equality.sort -> Equality.sort -> bool **)

      let lt_dec x y =
        let c = compSpec2Type x y (T.cmp x y) in
        (match c with
         | CompLtT -> true
         | _ -> false)

      (** val eqb : Equality.sort -> Equality.sort -> bool **)

      let eqb x y =
        if eq_dec x y then true else false
     end

    module L =
     struct
      module MO =
       struct
        module OrderTac =
         struct
          module OTF =
           struct
            type t = Equality.sort

            (** val compare : Equality.sort -> Equality.sort -> comparison **)

            let compare =
              T.cmp

            (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

            let eq_dec =
              Ordered.eq_dec
           end

          module TO =
           struct
            type t = Equality.sort

            (** val compare : Equality.sort -> Equality.sort -> comparison **)

            let compare =
              T.cmp

            (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

            let eq_dec =
              OTF.eq_dec
           end
         end

        (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

        let eq_dec =
          Ordered.eq_dec

        (** val lt_dec : Equality.sort -> Equality.sort -> bool **)

        let lt_dec x y =
          let c = compSpec2Type x y (T.cmp x y) in
          (match c with
           | CompLtT -> true
           | _ -> false)

        (** val eqb : Equality.sort -> Equality.sort -> bool **)

        let eqb x y =
          if eq_dec x y then true else false
       end
     end

    (** val flatten_e : enumeration -> elt list **)

    let rec flatten_e = function
    | End -> []
    | More (x, t0, r) -> x :: (app (elements t0) (flatten_e r))
   end

  module E =
   struct
    type t = Equality.sort

    (** val compare : Equality.sort -> Equality.sort -> comparison **)

    let compare =
      T.cmp

    (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

    let eq_dec =
      Ordered.eq_dec
   end

  type elt = Equality.sort

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem =
    Raw.mem

  (** val add : elt -> t -> t **)

  let add =
    Raw.add

  (** val remove : elt -> t -> t **)

  let remove =
    Raw.remove

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union =
    Raw.union

  (** val inter : t -> t -> t **)

  let inter =
    Raw.inter

  (** val diff : t -> t -> t **)

  let diff =
    Raw.diff

  (** val equal : t -> t -> bool **)

  let equal =
    Raw.equal

  (** val subset : t -> t -> bool **)

  let subset =
    Raw.subset

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty =
    Raw.is_empty

  (** val elements : t -> elt list **)

  let elements =
    Raw.elements

  (** val choose : t -> elt option **)

  let choose =
    Raw.choose

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold =
    Raw.fold

  (** val cardinal : t -> nat **)

  let cardinal =
    Raw.cardinal

  (** val filter : (elt -> bool) -> t -> t **)

  let filter =
    Raw.filter

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all =
    Raw.for_all

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ =
    Raw.exists_

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p = Raw.partition f s in ((fst p), (snd p))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false

  (** val compare : t -> t -> comparison **)

  let compare =
    Raw.compare

  (** val min_elt : t -> elt option **)

  let min_elt =
    Raw.min_elt

  (** val max_elt : t -> elt option **)

  let max_elt =
    Raw.max_elt
 end

type wsize =
| U8
| U16
| U32
| U64
| U128
| U256

(** val wsize_tag : wsize -> positive **)

let wsize_tag = function
| U8 -> XH
| U16 -> XO XH
| U32 -> XI XH
| U64 -> XO (XO XH)
| U128 -> XI (XO XH)
| U256 -> XO (XI XH)

type box_wsize_U8 =
| Box_wsize_U8

type wsize_fields_t = __

(** val wsize_fields : wsize -> wsize_fields_t **)

let wsize_fields _ =
  Obj.magic Box_wsize_U8

(** val wsize_eqb_fields :
    (wsize -> wsize -> bool) -> positive -> wsize_fields_t -> wsize_fields_t
    -> bool **)

let wsize_eqb_fields _ _ _ _ =
  true

(** val wsize_eqb : wsize -> wsize -> bool **)

let wsize_eqb x1 x2 =
  eqb_body wsize_tag wsize_fields
    (Obj.magic wsize_eqb_fields (fun _ _ -> true)) (wsize_tag x1)
    Box_wsize_U8 x2

type velem =
| VE8
| VE16
| VE32
| VE64

type pelem =
| PE1
| PE2
| PE4
| PE8
| PE16
| PE32
| PE64
| PE128

type signedness =
| Signed
| Unsigned

(** val wsize_cmp : wsize -> wsize -> comparison **)

let wsize_cmp s s' =
  match s with
  | U8 -> (match s' with
           | U8 -> Eq
           | _ -> Lt)
  | U16 -> (match s' with
            | U8 -> Gt
            | U16 -> Eq
            | _ -> Lt)
  | U32 -> (match s' with
            | U8 -> Gt
            | U16 -> Gt
            | U32 -> Eq
            | _ -> Lt)
  | U64 -> (match s' with
            | U64 -> Eq
            | U128 -> Lt
            | U256 -> Lt
            | _ -> Gt)
  | U128 -> (match s' with
             | U128 -> Eq
             | U256 -> Lt
             | _ -> Gt)
  | U256 -> (match s' with
             | U256 -> Eq
             | _ -> Gt)

type reg_kind =
| Normal
| Extra

type writable =
| Constant
| Writable

type reference =
| Direct
| Pointer of writable

type v_kind =
| Const
| Stack of reference
| Reg of (reg_kind * reference)
| Inline
| Global

type safe_cond =
| NotZero of wsize * nat
| X86Division of wsize * signedness
| InRangeMod32 of wsize * z * z * nat
| ULt of wsize * nat * z
| UGe of wsize * z * nat
| UaddLe of wsize * nat * nat * z
| AllInit of wsize * positive * nat
| ScFalse

type atype =
| Abool
| Aint
| Aarr of wsize * positive
| Aword of wsize

(** val atype_tag : atype -> positive **)

let atype_tag = function
| Abool -> XH
| Aint -> XO XH
| Aarr (_, _) -> XI XH
| Aword _ -> XO (XO XH)

type box_atype_abool =
| Box_atype_abool

type box_atype_aarr = { box_atype_aarr_0 : wsize; box_atype_aarr_1 : positive }

type atype_fields_t = __

(** val atype_fields : atype -> atype_fields_t **)

let atype_fields = function
| Aarr (h, h0) -> Obj.magic { box_atype_aarr_0 = h; box_atype_aarr_1 = h0 }
| Aword h -> Obj.magic h
| _ -> Obj.magic Box_atype_abool

(** val atype_eqb_fields :
    (atype -> atype -> bool) -> positive -> atype_fields_t -> atype_fields_t
    -> bool **)

let atype_eqb_fields _ x a b =
  match x with
  | XI _ ->
    let { box_atype_aarr_0 = box_atype_aarr_2; box_atype_aarr_1 =
      box_atype_aarr_3 } = Obj.magic a
    in
    let { box_atype_aarr_0 = box_atype_aarr_4; box_atype_aarr_1 =
      box_atype_aarr_5 } = Obj.magic b
    in
    (&&) (wsize_eqb box_atype_aarr_2 box_atype_aarr_4)
      ((&&) (positive_eqb box_atype_aarr_3 box_atype_aarr_5) true)
  | XO x0 ->
    (match x0 with
     | XO _ -> (&&) (wsize_eqb (Obj.magic a) (Obj.magic b)) true
     | _ -> true)
  | XH -> true

(** val atype_eqb : atype -> atype -> bool **)

let atype_eqb x1 x2 =
  match x1 with
  | Aarr (h, h0) ->
    eqb_body atype_tag atype_fields
      (Obj.magic atype_eqb_fields (fun _ _ -> true))
      (atype_tag (Aarr (h, h0))) { box_atype_aarr_0 = h; box_atype_aarr_1 =
      h0 } x2
  | Aword h ->
    eqb_body atype_tag atype_fields
      (Obj.magic atype_eqb_fields (fun _ _ -> true)) (atype_tag (Aword h)) h
      x2
  | x ->
    eqb_body atype_tag atype_fields
      (Obj.magic atype_eqb_fields (fun _ _ -> true)) (atype_tag x)
      Box_atype_abool x2

(** val atype_eqb_OK : atype -> atype -> reflect **)

let atype_eqb_OK =
  iffP2 atype_eqb

(** val hB_unnamed_factory_3 : atype Coq_hasDecEq.axioms_ **)

let hB_unnamed_factory_3 =
  { Coq_hasDecEq.eq_op = atype_eqb; Coq_hasDecEq.eqP = atype_eqb_OK }

(** val type_atype__canonical__eqtype_Equality : Equality.coq_type **)

let type_atype__canonical__eqtype_Equality =
  Obj.magic hB_unnamed_factory_3

(** val atype_cmp : atype -> atype -> comparison **)

let atype_cmp t0 t' =
  match t0 with
  | Abool -> (match t' with
              | Abool -> Eq
              | _ -> Lt)
  | Aint -> (match t' with
             | Abool -> Gt
             | Aint -> Eq
             | _ -> Lt)
  | Aarr (ws, n0) ->
    (match t' with
     | Aarr (ws', n') ->
       (match wsize_cmp ws ws' with
        | Eq -> Coq_Pos.compare n0 n'
        | x -> x)
     | _ -> Gt)
  | Aword w ->
    (match t' with
     | Aarr (_, _) -> Lt
     | Aword w' -> wsize_cmp w w'
     | _ -> Gt)

module type TaggedCore =
 sig
  type t

  val tag : t -> int
 end

module Tagged =
 functor (C:TaggedCore) ->
 struct
  type t = C.t

  (** val tag : t -> int **)

  let tag =
    C.tag

  (** val t_eqb : t -> t -> bool **)

  let t_eqb x y =
    eqb0 (tag x) (tag y)

  (** val t_eq_axiom : t eq_axiom **)

  let t_eq_axiom x y =
    equivP (t_eqb x y) (iff_reflect (t_eqb x y))

  (** val coq_HB_unnamed_factory_1 : t Coq_hasDecEq.axioms_ **)

  let coq_HB_unnamed_factory_1 =
    { Coq_hasDecEq.eq_op = t_eqb; Coq_hasDecEq.eqP = t_eq_axiom }

  (** val coq_Tagged_t__canonical__eqtype_Equality : Equality.coq_type **)

  let coq_Tagged_t__canonical__eqtype_Equality =
    Obj.magic coq_HB_unnamed_factory_1

  (** val t_eqType : Equality.coq_type **)

  let t_eqType =
    reverse_coercion coq_Tagged_t__canonical__eqtype_Equality __

  (** val cmp : t -> t -> comparison **)

  let cmp x y =
    compares (tag x) (tag y)

  module CmpT =
   struct
    (** val t : Equality.coq_type **)

    let t =
      reverse_coercion coq_Tagged_t__canonical__eqtype_Equality __

    (** val cmp : Equality.sort -> Equality.sort -> comparison **)

    let cmp =
      Obj.magic cmp
   end

  module Mt = Mmake(CmpT)

  module St = Smake(CmpT)

  module StP = EqProperties(St)

  module StD = WDecide(St)
 end

module type CORE_IDENT =
 sig
  type t

  val tag : t -> int

  val id_name : t -> char list

  val id_kind : t -> v_kind

  val spill_to_mmx : t -> bool
 end

module Cident =
 struct
  type t = int

  (** val tag : t -> int **)

  let tag x =
    x

  (** val tagI : __ **)

  let tagI =
    __

  (** val id_name : t -> char list **)

  let id_name _ =
    []

  (** val id_kind : t -> v_kind **)

  let id_kind _ =
    Const

  (** val spill_to_mmx : t -> bool **)

  let spill_to_mmx _ =
    false
 end

module Tident = Tagged(Cident)

(** val ident_eqType : Equality.coq_type **)

let ident_eqType = Obj.magic (fun () ->
  { Coq_hasDecEq.eq_op = (fun x y ->
    eqb0 (Cident.tag (Obj.magic x)) (Cident.tag (Obj.magic y)));
    Coq_hasDecEq.eqP = (Obj.magic Tident.t_eq_axiom) }) ()

module WrapIdent =
 struct
  type t = Cident.t
 end

module type IDENT =
 sig
  type ident = WrapIdent.t

  module Mid :
   MAP
 end

module Ident =
 struct
  type ident = WrapIdent.t

  (** val id_name : ident -> char list **)

  let id_name =
    Cident.id_name

  (** val id_kind : ident -> v_kind **)

  let id_kind =
    Cident.id_kind

  module Mid = Tident.Mt

  (** val spill_to_mmx : ident -> bool **)

  let spill_to_mmx =
    Cident.spill_to_mmx
 end

module FunName =
 struct
  type t = int

  (** val tag : t -> int **)

  let tag x =
    x

  (** val tagI : __ **)

  let tagI =
    __
 end

type funname = FunName.t

module MvMake =
 functor (I:IDENT) ->
 struct
  type var = { vtype : atype; vname : I.ident }

  (** val vtype : var -> atype **)

  let vtype v =
    v.vtype

  (** val vname : var -> I.ident **)

  let vname v =
    v.vname

  (** val var_beq : var -> var -> bool **)

  let var_beq v1 v2 =
    let { vtype = t1; vname = n1 } = v1 in
    let { vtype = t2; vname = n2 } = v2 in
    (&&)
      (eq_op0 type_atype__canonical__eqtype_Equality (Obj.magic t1)
        (Obj.magic t2))
      (eq_op0 ident_eqType (Obj.magic n1) (Obj.magic n2))

  (** val var_eqP : var eq_axiom **)

  let var_eqP __top_assumption_ =
    let _evar_0_ = fun t1 n1 __top_assumption_0 ->
      let _evar_0_ = fun t2 n2 ->
        iffP (var_beq { vtype = t1; vname = n1 } { vtype = t2; vname = n2 })
          (idP
            (var_beq { vtype = t1; vname = n1 } { vtype = t2; vname = n2 }))
      in
      let { vtype = vtype0; vname = vname0 } = __top_assumption_0 in
      _evar_0_ vtype0 vname0
    in
    let { vtype = vtype0; vname = vname0 } = __top_assumption_ in
    _evar_0_ vtype0 vname0

  (** val coq_HB_unnamed_factory_1 : var Coq_hasDecEq.axioms_ **)

  let coq_HB_unnamed_factory_1 =
    { Coq_hasDecEq.eq_op = var_beq; Coq_hasDecEq.eqP = var_eqP }

  (** val coq_MvMake_var__canonical__eqtype_Equality : Equality.coq_type **)

  let coq_MvMake_var__canonical__eqtype_Equality =
    Obj.magic coq_HB_unnamed_factory_1

  (** val var_cmp : var -> var -> comparison **)

  let var_cmp x y =
    match atype_cmp x.vtype y.vtype with
    | Eq -> I.Mid.K.cmp (Obj.magic x.vname) (Obj.magic y.vname)
    | x0 -> x0
 end

module Var = MvMake(Ident)

type aligned =
| Unaligned
| Aligned

type arr_access =
| AAdirect
| AAscale

type 'tr sem_prod = 'tr lprod

type sem_tuple = ltuple

type slh_op =
| SLHinit
| SLHupdate
| SLHmove
| SLHprotect of wsize
| SLHprotect_ptr of wsize * positive
| SLHprotect_ptr_fail of wsize * positive

type spill_op =
| Spill
| Unspill

type pseudo_operator =
| Ospill of spill_op * atype list
| Ocopy of wsize * positive
| Odeclassify of atype
| Odeclassify_mem of positive
| Onop
| Omulu of wsize
| Oaddcarry of wsize
| Osubcarry of wsize
| Oswap of atype

type arg_constrained_register =
| ACR_any
| ACR_exact of Var.var
| ACR_subset of Var.var list

type arg_desc =
| ADImplicit of Var.var
| ADExplicit of nat * arg_constrained_register

type arg_position =
| APout of nat
| APin of nat

type instruction_desc = { str : (unit -> char list); tin : atype list;
                          i_in : arg_desc list; tout : atype list;
                          i_out : arg_desc list;
                          conflicts : (arg_position * arg_position) list;
                          semi : sem_tuple exec sem_prod; i_valid : bool;
                          i_safe : safe_cond list }

type prim_x86_suffix =
| PVp of wsize
| PVs of signedness * wsize
| PVv of velem * wsize
| PVsv of signedness * velem * wsize
| PVx of wsize * wsize
| PVvv of velem * wsize * velem * wsize

type 'asm_op prim_constructor =
| PrimX86 of prim_x86_suffix list * (prim_x86_suffix -> 'asm_op option)
| PrimARM of (bool -> bool -> (char list, 'asm_op) result)

type 'asm_op asmOp = { _eqT : 'asm_op eqTypeC;
                       asm_op_instr : ('asm_op -> instruction_desc);
                       prim_string : (char list * 'asm_op prim_constructor)
                                     list }

type 'asm_op asm_op_t = 'asm_op

type 'asm_op sopn =
| Opseudo_op of pseudo_operator
| Oslh of slh_op
| Oasm of 'asm_op asm_op_t

type syscall_t =
| RandomBytes of wsize * positive

type cmp_kind =
| Cmp_int
| Cmp_w of signedness * wsize

type op_kind =
| Op_int
| Op_w of wsize

type wiop1 =
| WIwint_of_int of wsize
| WIint_of_wint of wsize
| WIword_of_wint of wsize
| WIwint_of_word of wsize
| WIwint_ext of wsize * wsize
| WIneg of wsize

type sop1 =
| Oword_of_int of wsize
| Oint_of_word of signedness * wsize
| Osignext of wsize * wsize
| Ozeroext of wsize * wsize
| Onot
| Olnot of wsize
| Oneg of op_kind
| Owi1 of signedness * wiop1

type wiop2 =
| WIadd
| WImul
| WIsub
| WIdiv
| WImod
| WIshl
| WIshr
| WIeq
| WIneq
| WIlt
| WIle
| WIgt
| WIge

type sop2 =
| Obeq
| Oand
| Oor
| Oadd of op_kind
| Omul of op_kind
| Osub of op_kind
| Odiv of signedness * op_kind
| Omod of signedness * op_kind
| Oland of wsize
| Olor of wsize
| Olxor of wsize
| Olsr of wsize
| Olsl of op_kind
| Oasr of op_kind
| Oror of wsize
| Orol of wsize
| Oeq of op_kind
| Oneq of op_kind
| Olt of cmp_kind
| Ole of cmp_kind
| Ogt of cmp_kind
| Oge of cmp_kind
| Ovadd of velem * wsize
| Ovsub of velem * wsize
| Ovmul of velem * wsize
| Ovlsr of velem * wsize
| Ovlsl of velem * wsize
| Ovasr of velem * wsize
| Owi2 of signedness * wsize * wiop2

type combine_flags =
| CF_LT of signedness
| CF_LE of signedness
| CF_EQ
| CF_NEQ
| CF_GE of signedness
| CF_GT of signedness

type opN =
| Opack of wsize * pelem
| Oarray of positive
| Ocombine_flags of combine_flags

type opN_safety =
| Ois_arr_init of positive
| Ois_barr_init of positive

module type TAG =
 sig
  type t

  val witness : t
 end

module VarInfo =
 struct
  type t = positive

  (** val witness : t **)

  let witness =
    XH
 end

type var_info = VarInfo.t

(** val dummy_var_info : var_info **)

let dummy_var_info =
  VarInfo.witness

type var_i = { v_var : Var.var; v_info : var_info }

type v_scope =
| Slocal
| Sglob

type gvar = { gv : var_i; gs : v_scope }

(** val mk_lvar : var_i -> gvar **)

let mk_lvar x =
  { gv = x; gs = Slocal }

type pexpr =
| Pconst of z
| Pbool of bool
| Parr_init of wsize * positive
| Pvar of gvar
| Pget of aligned * arr_access * wsize * gvar * pexpr
| Psub of arr_access * wsize * positive * gvar * pexpr
| Pload of aligned * wsize * pexpr
| Papp1 of sop1 * pexpr
| Papp2 of sop2 * pexpr * pexpr
| PappN of opN * pexpr list
| Pif of atype * pexpr * pexpr * pexpr

type eassert =
| Pexpr of pexpr
| PappN_safety of opN_safety * pexpr list
| Pis_var_init of var_i
| Pis_mem_init of pexpr * pexpr
| Pand of eassert * eassert

(** val plvar : var_i -> pexpr **)

let plvar x =
  Pvar (mk_lvar x)

type lval =
| Lnone of var_info * atype
| Lvar of var_i
| Lmem of aligned * wsize * var_info * pexpr
| Laset of aligned * arr_access * wsize * var_i * pexpr
| Lasub of arr_access * wsize * positive * var_i * pexpr

(** val lnone_b : var_info -> lval **)

let lnone_b vi =
  Lnone (vi, Abool)

type dir =
| UpTo
| DownTo

type range = (dir * pexpr) * pexpr

module type InstrInfoT =
 sig
  type t

  val witness : t

  val with_location : t -> t

  val is_inline : t -> bool

  val var_info_of_ii : t -> var_info
 end

module InstrInfo =
 struct
  type t = positive

  (** val witness : t **)

  let witness =
    XH

  (** val with_location : t -> t **)

  let with_location ii =
    ii

  (** val is_inline : t -> bool **)

  let is_inline _ =
    false

  (** val var_info_of_ii : t -> var_info **)

  let var_info_of_ii _ =
    dummy_var_info
 end

type instr_info = InstrInfo.t

type assgn_tag =
| AT_none
| AT_keep
| AT_rename
| AT_inline
| AT_phinode

type align =
| Align
| NoAlign

type assertion = assertion_label * eassert

type 'asm_op instr_r =
| Cassgn of lval * assgn_tag * atype * pexpr
| Copn of lval list * assgn_tag * 'asm_op sopn * pexpr list
| Csyscall of lval list * syscall_t * pexpr list
| Cassert of assertion
| Cif of pexpr * 'asm_op instr list * 'asm_op instr list
| Cfor of var_i * range * 'asm_op instr list
| Cwhile of align * 'asm_op instr list * pexpr * instr_info
   * 'asm_op instr list
| Ccall of lval list * funname * pexpr list
and 'asm_op instr =
| MkI of instr_info * 'asm_op instr_r

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_op_msb_t =
  wsize option * 'asm_op

type register =
| RAX
| RCX
| RDX
| RBX
| RSP
| RBP
| RSI
| RDI
| R8
| R9
| R10
| R11
| R12
| R13
| R14
| R15

type register_ext =
| MM0
| MM1
| MM2
| MM3
| MM4
| MM5
| MM6
| MM7

type xmm_register =
| XMM0
| XMM1
| XMM2
| XMM3
| XMM4
| XMM5
| XMM6
| XMM7
| XMM8
| XMM9
| XMM10
| XMM11
| XMM12
| XMM13
| XMM14
| XMM15

type rflag =
| CF
| PF
| ZF
| SF
| OF

type condt =
| O_ct
| NO_ct
| B_ct
| NB_ct
| E_ct
| NE_ct
| BE_ct
| NBE_ct
| S_ct
| NS_ct
| P_ct
| NP_ct
| L_ct
| NL_ct
| LE_ct
| NLE_ct

type x86_op =
| MOV of wsize
| MOVSX of wsize * wsize
| MOVZX of wsize * wsize
| CMOVcc of wsize
| XCHG of wsize
| ADD of wsize
| SUB of wsize
| MUL of wsize
| IMUL of wsize
| IMULr of wsize
| IMULri of wsize
| DIV of wsize
| IDIV of wsize
| CQO of wsize
| ADC of wsize
| SBB of wsize
| NEG of wsize
| INC of wsize
| DEC of wsize
| LZCNT of wsize
| TZCNT of wsize
| BSR of wsize
| SETcc
| BT of wsize
| CLC
| STC
| LEA of wsize
| TEST of wsize
| CMP of wsize
| AND of wsize
| ANDN of wsize
| OR of wsize
| XOR of wsize
| NOT of wsize
| ROR of wsize
| ROL of wsize
| RCR of wsize
| RCL of wsize
| SHL of wsize
| SHR of wsize
| SAL of wsize
| SAR of wsize
| SHLD of wsize
| SHRD of wsize
| RORX of wsize
| SARX of wsize
| SHRX of wsize
| SHLX of wsize
| MULX_lo_hi of wsize
| ADCX of wsize
| ADOX of wsize
| BSWAP of wsize
| POPCNT of wsize
| BTR of wsize
| BTS of wsize
| PEXT of wsize
| PDEP of wsize
| MOVX of wsize
| POR
| PADD of velem * wsize
| MOVD of wsize
| MOVV of wsize
| VMOV of wsize
| VMOVDQA of wsize
| VMOVDQU of wsize
| VPMOVSX of velem * wsize * velem * wsize
| VPMOVZX of velem * wsize * velem * wsize
| VPAND of wsize
| VPANDN of wsize
| VPOR of wsize
| VPXOR of wsize
| VPADD of velem * wsize
| VPSUB of velem * wsize
| VPAVG of velem * wsize
| VPMULL of velem * wsize
| VPMULH of wsize
| VPMULHU of wsize
| VPMULHRS of wsize
| VPMUL of wsize
| VPMULU of wsize
| VPEXTR of wsize
| VPINSR of velem
| VPSLL of velem * wsize
| VPSRL of velem * wsize
| VPSRA of velem * wsize
| VPSLLV of velem * wsize
| VPSRLV of velem * wsize
| VPSLLDQ of wsize
| VPSRLDQ of wsize
| VPSHUFB of wsize
| VPSHUFD of wsize
| VPSHUFHW of wsize
| VPSHUFLW of wsize
| VPBLEND of velem * wsize
| BLENDV of velem * wsize
| VPACKUS of velem * wsize
| VPACKSS of velem * wsize
| VSHUFPS of wsize
| VPBROADCAST of velem * wsize
| VMOVSHDUP of wsize
| VMOVSLDUP of wsize
| VPALIGNR of wsize
| VBROADCASTI128
| VPUNPCKH of velem * wsize
| VPUNPCKL of velem * wsize
| VEXTRACTI128
| VINSERTI128
| VPERM2I128
| VPERMD
| VPERMQ
| MOVEMASK of velem * wsize
| VPCMPEQ of velem * wsize
| VPCMPGT of velem * wsize
| VPSIGN of velem * wsize
| VPMADDUBSW of wsize
| VPMADDWD of wsize
| VMOVLPD
| VMOVHPD
| VPMINU of velem * wsize
| VPMINS of velem * wsize
| VPMAXU of velem * wsize
| VPMAXS of velem * wsize
| VPABS of velem * wsize
| VPTEST of wsize
| CLFLUSH
| PREFETCHT0
| PREFETCHT1
| PREFETCHT2
| PREFETCHNTA
| LFENCE
| MFENCE
| SFENCE
| RDTSC of wsize
| RDTSCP of wsize
| AESDEC
| VAESDEC of wsize
| AESDECLAST
| VAESDECLAST of wsize
| AESENC
| VAESENC of wsize
| AESENCLAST
| VAESENCLAST of wsize
| AESIMC
| VAESIMC
| AESKEYGENASSIST
| VAESKEYGENASSIST
| PCLMULQDQ
| VPCLMULQDQ of wsize
| SHA256RNDS2
| SHA256MSG1
| SHA256MSG2

type 't toIdent = { to_ident : ('t -> Ident.ident);
                    of_ident : (Ident.ident -> 't option) }

type ('reg, 'regx, 'xreg, 'rflag, 'cond) arch_toIdent = { toI_r : 'reg toIdent;
                                                          toI_rx : 'regx
                                                                   toIdent;
                                                          toI_x : 'xreg
                                                                  toIdent;
                                                          toI_f : 'rflag
                                                                  toIdent }

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) extra_op_t =
  'extra_op

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) extended_op =
| BaseOp of ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_op_msb_t
| ExtOp of ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) extra_op_t

type x86_extra_op =
| Oset0 of wsize
| Oconcat128
| Ox86MOVZX32
| Ox86MULX of wsize
| Ox86MULX_hi of wsize
| Ox86SLHinit
| Ox86SLHupdate
| Ox86SLHmove
| Ox86SLHprotect of reg_kind * wsize

type x86_extended_op =
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op

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
| JCsub_flags of char list * char list * jasmin_expr * jasmin_expr
| JCsbb of char list * char list * jasmin_expr * jasmin_expr * char list

(** val string_hash_Z : char list -> z **)

let rec string_hash_Z = function
| [] -> Z0
| c::rest ->
  Z.add (Z.of_nat (nat_of_ascii c))
    (Z.mul (Zpos (XI (XI (XI (XI XH))))) (string_hash_Z rest))

(** val string_to_ident : char list -> int **)

let string_to_ident s =
  of_Z (string_hash_Z s)

(** val int_to_ident : int -> Ident.ident **)

(* PATCH (2026-04-15): identity cast. The Coq axioms exist only because
   Cident.t is sealed in Jasmin's Rocq library; at runtime on the OCaml
   side the two types share the same representation. *)
let int_to_ident : int -> Ident.ident = Obj.magic

(** val int_to_funname : int -> funname **)

let int_to_funname : int -> funname = Obj.magic

(** val mk_var_from_string : char list -> var_i **)

let mk_var_from_string s =
  { v_var = { Var.vtype = (Aword U64); Var.vname =
    (int_to_ident (string_to_ident s)) }; v_info = dummy_var_info }

(** val to_pexpr : jasmin_expr -> pexpr **)

let rec to_pexpr = function
| JEvar x -> plvar (mk_var_from_string x)
| JElit v -> Pconst v
| JEadd (e1, e2) -> Papp2 ((Oadd (Op_w U64)), (to_pexpr e1), (to_pexpr e2))
| JEsub (e1, e2) -> Papp2 ((Osub (Op_w U64)), (to_pexpr e1), (to_pexpr e2))
| JEmul (e1, e2) -> Papp2 ((Omul (Op_w U64)), (to_pexpr e1), (to_pexpr e2))
| JEmulhuu (_, _) -> Pconst Z0
| JEand (e1, e2) -> Papp2 ((Oland U64), (to_pexpr e1), (to_pexpr e2))
| JEor (e1, e2) -> Papp2 ((Olor U64), (to_pexpr e1), (to_pexpr e2))
| JExor (e1, e2) -> Papp2 ((Olxor U64), (to_pexpr e1), (to_pexpr e2))
| JEshr (e1, e2) -> Papp2 ((Olsr U64), (to_pexpr e1), (to_pexpr e2))
| JEshl (e1, e2) -> Papp2 ((Olsl (Op_w U64)), (to_pexpr e1), (to_pexpr e2))
| JEltu (e1, e2) ->
  Papp2 ((Olt (Cmp_w (Unsigned, U64))), (to_pexpr e1), (to_pexpr e2))
| JEeq (e1, e2) -> Papp2 ((Oeq (Op_w U64)), (to_pexpr e1), (to_pexpr e2))
| JEload (base, off) ->
  Pload (Aligned, U64, (Papp2 ((Oadd (Op_w U64)), (to_pexpr base), (Pconst
    off))))

(** val mk_lval_from_string : char list -> lval **)

let mk_lval_from_string s =
  Lvar (mk_var_from_string s)

(** val di : instr_info **)

let di =
  InstrInfo.witness

(** val to_jasmin_cmd :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    x86_extended_op asmOp -> jasmin_cmd -> x86_extended_op instr list **)

let rec to_jasmin_cmd atoI section_asmop = function
| JCskip -> []
| JCseq (c1, c2) ->
  cat (to_jasmin_cmd atoI section_asmop c1)
    (to_jasmin_cmd atoI section_asmop c2)
| JCset (x, e) ->
  (MkI (di, (Cassgn ((mk_lval_from_string x), AT_none, (Aword U64),
    (to_pexpr e))))) :: []
| JCstore (base, off, v) ->
  let addr = Papp2 ((Oadd (Op_w U64)), (to_pexpr base), (Pconst off)) in
  (MkI (di, (Cassgn ((Lmem (Aligned, U64, dummy_var_info, addr)), AT_none,
  (Aword U64), (to_pexpr v))))) :: []
| JCcall (f, args) ->
  (MkI (di, (Ccall ([], (int_to_funname (string_to_ident f)),
    (map to_pexpr args))))) :: []
| JCif (e, ct, cf) ->
  (MkI (di, (Cif ((to_pexpr e), (to_jasmin_cmd atoI section_asmop ct),
    (to_jasmin_cmd atoI section_asmop cf))))) :: []
| JCwhile (e, body) ->
  (MkI (di, (Cwhile (NoAlign, (to_jasmin_cmd atoI section_asmop body),
    (to_pexpr e), di, [])))) :: []
| JCdecl (_, _, body) -> to_jasmin_cmd atoI section_asmop body
| JCadd_flags (cf, result0, a, b) ->
  let none_b = lnone_b dummy_var_info in
  (MkI (di, (Copn
  ((none_b :: ((mk_lval_from_string cf) :: (none_b :: (none_b :: (none_b :: (
  (mk_lval_from_string result0) :: [])))))), AT_none, (Oasm (BaseOp (None,
  (ADD U64)))), ((to_pexpr a) :: ((to_pexpr b) :: [])))))) :: []
| JCadcx (cf_out, result0, a, b, cf_in) ->
  (MkI (di, (Copn
    (((mk_lval_from_string cf_out) :: ((mk_lval_from_string result0) :: [])),
    AT_none, (Oasm (BaseOp (None, (ADCX U64)))),
    ((to_pexpr a) :: ((to_pexpr b) :: ((plvar (mk_var_from_string cf_in)) :: []))))))) :: []
| JCmulx (hi, lo, a, b) ->
  (MkI (di, (Copn
    (((mk_lval_from_string lo) :: ((mk_lval_from_string hi) :: [])), AT_none,
    (Oasm (BaseOp (None, (MULX_lo_hi U64)))),
    ((to_pexpr a) :: ((to_pexpr b) :: [])))))) :: []
| JCsub_flags (cf, result0, a, b) ->
  let none_b = lnone_b dummy_var_info in
  (MkI (di, (Copn
  ((none_b :: ((mk_lval_from_string cf) :: (none_b :: (none_b :: (none_b :: (
  (mk_lval_from_string result0) :: [])))))), AT_none, (Oasm (BaseOp (None,
  (SUB U64)))), ((to_pexpr a) :: ((to_pexpr b) :: [])))))) :: []
| JCsbb (cf_out, result0, a, b, cf_in) ->
  let none_b = lnone_b dummy_var_info in
  (MkI (di, (Copn
  ((none_b :: ((mk_lval_from_string cf_out) :: (none_b :: (none_b :: (none_b :: (
  (mk_lval_from_string result0) :: [])))))), AT_none, (Oasm (BaseOp (None,
  (SBB U64)))),
  ((to_pexpr a) :: ((to_pexpr b) :: ((plvar (mk_var_from_string cf_in)) :: []))))))) :: []
