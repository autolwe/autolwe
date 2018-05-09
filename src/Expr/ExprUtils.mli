(* * Additional functions on expressions
 * These functions do not require access to expression internals. *)

(* ** Imports *)
open Abbrevs
open Syms
open Expr
open Type


(* ** Construction functions
 * ----------------------------------------------------------------------- *)

val ty_prod_vs : VarSym.t list -> ty

val mk_GExp_Gen : Groupvar.id -> expr -> expr

val mk_Land_nofail : expr list -> expr

val mk_Lor_nofail : expr list -> expr

(* ** Indicator functions
 * ----------------------------------------------------------------------- *)

val is_V           : expr -> bool
val is_MapLookup   : expr -> bool
val is_FunCall     : expr -> bool
val is_Quant       : expr -> bool
val is_All         : expr -> bool
val is_Exists      : expr -> bool
val is_Tuple       : expr -> bool
val is_Unit        : expr -> bool
val is_Proj        : expr -> bool
val is_Cnst        : expr -> bool
val is_FNat        : expr -> bool
val is_FOne        : expr -> bool
val is_FZ          : expr -> bool
val is_True        : expr -> bool
val is_False       : expr -> bool
val is_GGen        : expr -> bool
val is_GOne        : expr -> bool
val is_GLog        : expr -> bool
val is_RoCall      : expr -> bool
val is_RoCall_ros  : expr -> RoSym.t -> bool
val is_GLog_gv     : Groupvar.id -> expr -> bool
val is_some_App    : expr -> bool
val is_App         : op -> expr -> bool
val is_FDiv        : expr -> bool
val is_FOpp        : expr -> bool
val is_GExp        : expr -> bool
val is_Ifte        : expr -> bool
val is_some_Nary   : expr -> bool
val is_Nary        : nop -> expr -> bool
val is_FPlus       : expr -> bool
val is_FMult       : expr -> bool
val is_Xor         : expr -> bool
val is_Eq          : expr -> bool
val is_InEq        : expr -> bool
val is_Not         : expr -> bool
val is_field_op    : op -> bool
val is_field_nop   : nop -> bool
val is_field_exp   : expr -> bool
val is_list_op     : op -> bool
val is_list_nop    : nop -> bool
val is_mat_op      : op -> bool
val is_mat_nop     : nop -> bool
val is_mat_exp     : expr -> bool
val is_list_exp    : expr -> bool
val is_matplus     : expr -> bool
val is_Land        : expr -> bool
val is_Lor         : expr -> bool

(* ** Destructor functions
 * ----------------------------------------------------------------------- *)

exception Destr_failure of string

val destr_V            : expr -> VarSym.t
val destr_Quant        : expr -> quant * (VarSym.t list * Olist.t) * expr
val destr_All          : expr -> (VarSym.t list * Olist.t) * expr
val destr_Exists       : expr -> (VarSym.t list * Olist.t) * expr
val destr_Tuple        : expr -> expr list
val destr_Proj         : expr -> int * expr
val destr_Cnst         : expr -> cnst
val destr_FNat         : expr -> int
val destr_App          : expr -> op * expr list
val destr_GMult        : expr -> (expr) list
val destr_GExp         : expr -> expr * expr
val destr_RoCall       : expr -> RoSym.t * expr
val destr_GLog         : expr -> expr
val destr_EMap         : expr -> EmapSym.t * expr * expr
val destr_FOpp         : expr -> expr
val destr_FMinus       : expr -> expr * expr
val destr_FInv         : expr -> expr
val destr_FDiv         : expr -> expr * expr
val destr_Eq           : expr -> expr * expr
val destr_Not          : expr -> expr
val destr_Ifte         : expr -> expr * expr * expr
val destr_FPlus        : expr -> expr list
val destr_FMult        : expr -> expr list
val destr_Xor          : expr -> expr list
val destr_Land         : expr -> expr list
val destr_Lor          : expr -> expr list
val destr_Quant_nofail : expr -> expr
val destr_Xor_nofail   : expr -> expr list
val destr_Land_nofail  : expr -> expr list
val destr_Lor_nofail   : expr -> expr list
val destr_Tuple_nofail : expr -> expr list
val destr_GExp_Gen     : Groupvar.id -> expr -> expr

(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

val pp_sort_expensive : bool ref

val pp_number_tuples : bool ref

val pp_cnst : F.formatter -> cnst -> Type.ty -> unit
val pp_expr  : F.formatter -> expr -> unit
val pp_expr_qual : qual:OrclSym.t qual -> F.formatter -> expr -> unit
val pp_op   : F.formatter -> op * expr list -> unit
val pp_nop  : F.formatter -> nop * expr list -> unit
val pp_expr_tnp : F.formatter -> expr -> unit

(* ** Useful functions on [expr]
 * ----------------------------------------------------------------------- *)

val e_iter_ty_maximal : ty -> (expr -> unit) -> expr -> unit

(** [e_vars e] returns the set of all variables in [e]. *)
val e_vars : expr -> Se.t

val has_log : expr -> bool

val is_ppt : expr -> bool

val se_of_list : expr list -> Se.t

val he_keys : 'a He.t -> Se.t

val se_disjoint : Se.t -> Se.t -> bool

val me_of_list : (Me.key * 'a) list -> 'a Me.t

val he_to_list : 'a He.t -> (expr * 'a) list

type ctxt = VarSym.t * expr

val ctxt_ty : ctxt -> ty * ty
val inst_ctxt : ctxt -> expr -> expr
val pp_ctxt : F.formatter -> ctxt -> unit

(** [sub t] is a generic subtraction function that
    returns context [(x1,x2,c)] and a [zero]
    such that forall e1 e2:t, [inst_ctxt c e1 e2] =E [e1 - e2]
    and [inst_ctxt c e2 e2] = [zero]. *)
val sub : ty -> (VarSym.t * ctxt) * expr

val is_Zero : expr -> bool

val mk_Zero   : ty -> expr

val typeError_to_string : ty * ty * expr * expr option * string -> string

val catch_TypeError : (unit -> 'a) -> 'a

type inverter = I of expr

val expr_of_inverter : inverter -> expr

val pp_inverter : F.formatter -> inverter -> unit

val e_size : expr -> int
