
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

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

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val double : uint -> uint

  val succ_double : uint -> uint
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
 end

module Coq_Pos :
 sig
  val to_little_uint : positive -> uint

  val to_uint : positive -> uint
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val rev0 : 'a1 list -> 'a1 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val pow : z -> z -> z

  val compare : z -> z -> comparison

  val ltb : z -> z -> bool

  val to_int : z -> signed_int
 end

val eqb : char list -> char list -> bool

val append : char list -> char list -> char list

val concat : char list -> char list list -> char list

module NilEmpty :
 sig
  val string_of_uint : uint -> char list
 end

module NilZero :
 sig
  val string_of_uint : uint -> char list

  val string_of_int : signed_int -> char list
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

val lF : char list

val pp_zlit_u64 : z -> char list

val pp_expr : jasmin_expr -> char list

val pp_type : jasmin_type -> char list

val pp_cmd : char list -> jasmin_cmd -> char list

val string_in : char list -> char list list -> bool

val collect_set_vars : jasmin_cmd -> char list list

val dedup_strings : char list list -> char list list -> char list list

val function_locals : jasmin_func -> char list list

val pp_locals_decls : char list -> char list list -> char list

val pp_func : jasmin_func -> char list

val pp_module : jasmin_func list -> char list

val bn254_opt_jasmin : jasmin_func list
