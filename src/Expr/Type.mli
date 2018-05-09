(* * Types (hashconsed) *)

(* ** Imports *)
open Abbrevs

(* ** Identifiers *)

(** length variables for bitstrings *)
module Lenvar : (module type of Id)

(** identifier for types *)
module Tysym : (module type of Id)

(** identifier for different permutations *)
module Permvar : (module type of Id)

(** identifier for different groups *)
module Groupvar : (module type of Id)

(* ** Types and type nodes *)


type mdim =
  | MDBase of Lenvar.id
  | MDPlus of mdim * mdim

val mdim_equal : mdim -> mdim -> bool
val pp_mdim : mdim -> string

type ty = private { ty_node : ty_node; ty_tag : int; }
and ty_node =
  | BS of Lenvar.id
  | Bool
  | Mat of (mdim * mdim)
  | List of (mdim * ty)
  | G of Groupvar.id
  | TySym of Tysym.id
  | Fq
  | Prod of ty list
  | Int (* used during extraction *)

val equal_ty   : ty -> ty -> bool
val concat_compat_ty : ty -> ty -> bool
val split_compat : ty -> bool
val hash_ty    : ty -> int
val compare_ty : ty -> ty -> int

(* list specific *)
val listmult_compat_ty : ty -> ty -> bool
val get_list_ty : ty -> (mdim * ty)
val listconcat_compat_ty : ty -> ty -> bool

(* matrix specific *)
val matmult_compat_ty : ty -> ty -> bool
val matmult_get_dim : ty -> ty -> (mdim * mdim) 
val get_split_dim : ty -> (mdim * mdim) 
val dim_of_mat : ty -> (mdim * mdim)

module Hsty : Hashcons.S with type t = ty

module Mty : Map.S with type key = ty
module Sty : Set.S with type elt = ty
module Hty : Hashtbl.S with type key = ty

val mk_ty : ty_node -> Hsty.t

(* ** Constructor functions *)

val mk_BS      : Lenvar.id -> ty
val mk_G       : Groupvar.id -> ty
val mk_TySym   : Tysym.id -> ty
val mk_Fq      : ty
val mk_Bool    : ty
val mk_Prod    : ty list -> ty
val mk_Int     : ty
val mk_Mat     : mdim -> mdim -> ty 
val mk_List    : mdim -> ty -> ty

(* ** Indicator and destructor functions *)


val is_G	      : ty -> bool
val is_BS         : ty -> bool
val is_Fq	      : ty -> bool
val is_Prod	      : ty -> bool
val is_Mat        : ty -> bool
val is_List       : ty -> bool
val is_ListOfTy   : ty -> ty -> bool
val is_MatList    : ty -> bool
val is_Mat_splittable : ty -> bool
val destr_G_exn	      : ty -> Groupvar.id
val destr_BS_exn      : ty -> Lenvar.id
val destr_Prod_exn    : ty -> ty list
val destr_Prod        : ty -> (ty list) option

(* ** Pretty printing *)

val pp_group : F.formatter -> Groupvar.id -> unit
val pp_ty    : F.formatter -> ty -> unit
