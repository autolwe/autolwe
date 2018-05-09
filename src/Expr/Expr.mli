(* * Typed algebraic expression. *)

(* ** Imports *)
open Type
open Syms


(* ** Expressions (hashconsed)
 * ----------------------------------------------------------------------- *)

(* *** Quantifiers *)

type quant = All | Exists

val neg_quant : quant -> quant

module Olist : sig
  type t =
    | ROlist of RoSym.t   (* list of adversary queries to random oracle *)
    | Olist  of OrclSym.t (* list of adversary queries to ordinary oracle *)

  val dom : t -> ty

  val hash : t -> int

  val equal : t -> t -> bool

  val pp : Format.formatter -> t -> unit
end

(* *** Types *)

type proj_type = Type.ty * Type.ty * Type.ty

type perm_type = IsInv | NotInv

type cnst =
  | GGen        (* generator of $\group$ (type defines group) *)
  | FNat of int (* Natural number in field, always $\geq 0$ *)
  | Z           (* $0$ bitstring (type defines length) *)
  | B of bool   (* boolean value *)
  | MatZero
  | MatId

type op =
  (* bilinear groups *)
  | GExp of Groupvar.id           (* exponentiation in $\group_i$ *)
  | GLog of Groupvar.id           (* discrete logarithm in $\group_i$ *)
  | GInv                          (* inverse in group *)
  | EMap of EmapSym.t             (* bilinear map *)
  (* prime field *)
  | FOpp                          (* additive inverse in $\field$ *)
  | FMinus                        (* subtraction in $\field$ *)
  | FInv                          (* mult. inverse in $\field$ *)
  | FDiv                          (* division in $\field$ *)
  (* logical operators *)
  | Eq                            (* equality *)
  | Not                           (* negation *)
  | Ifte                          (* if then else *)
  (* uninterpreted functions and random oracles *)
  | FunCall  of FunSym.t          (* function call (uninterpreted) *)
  | RoCall   of RoSym.t           (* random oracle call *)
  | MapLookup of MapSym.t         (* map lookup *)
  | MapIndom  of MapSym.t         (* map defined for given value *)
  | MatMult
  | MatOpp
  | MatTrans
  | MatConcat
  | MatSplitLeft
  | MatSplitRight
  | ListOp of op
  | ListOf

type nop =
  | GMult  (* multiplication in G (type defines group) *)
  | FPlus  (* plus in Fq *)
  | FMult  (* multiplication in Fq *)
  | MatPlus
  | Xor    (* Xor of bitstrings *)
  | Land   (* logical and *)
  | Lor    (* logical or *)
  | ListNop of nop

type binding = VarSym.t list * Olist.t

type expr = private {
  e_node : expr_node;
  e_ty   : ty;
  e_tag  : int
}
and expr_node =
  | V     of VarSym.t                 (* variables (program/logic/...) *)
  | Tuple of expr list              (* tuples *)
  | Proj  of int * expr             (* projection *)
  | Cnst  of cnst                   (* constants *)
  | App   of op * expr list         (* fixed arity operators *)
  | Nary  of nop * expr list        (* variable arity AC operators *)
  | Quant of quant * binding * expr (* quantifier *)

(* *** Equality, hashing, hash consing *)

val perm_type_hash : perm_type -> int
val cnst_hash : cnst -> int
val op_hash : op -> int
val nop_hash : nop -> int

val equal_expr : expr -> expr -> bool
val hash_expr : expr -> int
val compare_expr : expr -> expr -> int

module Hse : Hashcons.S with type t = expr

module Se : Set.S with type elt = expr
module He : Hashtbl.S with type key = expr
module Me : Map.S with type key = expr

(* ** Constructor functions
 * ----------------------------------------------------------------------- *)

(* *** Type checking *)

exception TypeError of (ty *  ty * expr * expr option * string)

val ensure_ty_G : Type.ty -> string -> Type.Groupvar.id
val ensure_list_ty : Type.ty -> string -> Type.mdim * Type.ty
val ensure_mat_ty : Type.ty -> Type.mdim * Type.mdim
val get_mat_mdims : Type.ty -> Type.mdim * Type.mdim

(* *** Constant mk functions *)

val mk_V           : VarSym.t -> expr
val mk_App         : op -> expr list -> ty -> expr
val mk_Nary        : nop -> expr list -> expr
val mk_FunCall     : FunSym.t -> expr -> expr
val mk_RoCall      : RoSym.t -> expr -> expr
val mk_MapLookup   : MapSym.t -> expr -> expr
val mk_MapIndom    : MapSym.t -> expr -> expr
val mk_Quant       : quant -> (VarSym.t list * Olist.t) -> expr -> expr
val mk_All         : (VarSym.t list * Olist.t) -> expr -> expr
val mk_Exists      : (VarSym.t list * Olist.t) -> expr -> expr
val mk_Tuple       : expr list -> expr
val mk_Proj        : int -> expr -> expr
val mk_GGen        : Groupvar.id -> expr
val mk_GOne        : Groupvar.id -> expr
val mk_FNat        : int -> expr
val mk_FOne        : expr
val mk_FZ          : expr
val mk_Z           : Lenvar.id -> expr
val mk_MatZero     : mdim -> mdim -> expr
val mk_ListOfMatZero : mdim -> mdim -> mdim -> expr
val mk_MatId      : mdim -> mdim -> expr
val mk_B           : bool -> expr
val mk_True        : expr
val mk_False       : expr
val mk_GMult       : expr list -> expr
val mk_GExp        : expr -> expr -> expr
val mk_GLog        : expr -> expr
val mk_GInv        : expr -> expr
val mk_EMap        : EmapSym.t -> expr -> expr -> expr
val mk_FOpp        : expr -> expr
val mk_FMinus      : expr -> expr -> expr
val mk_FInv        : expr -> expr
val mk_FDiv        : expr -> expr -> expr
val mk_Eq          : expr -> expr -> expr
val mk_Not         : expr -> expr
val mk_Ifte        : expr -> expr -> expr -> expr
val mk_ListOp      : op -> expr list -> expr
val mk_ListOf      : mdim -> expr -> expr
val mk_ListMatMult : expr -> expr -> expr
val mk_ListMatTrans    : expr -> expr
val mk_ListMatOpp      : expr -> expr
val mk_ListMatSplitLeft : expr -> expr
val mk_ListMatSplitRight : expr -> expr
val mk_ListMatConcat    : expr -> expr -> expr
val mk_MatMult     : expr -> expr -> expr
val mk_MatTrans    : expr -> expr
val mk_Trans       : expr -> expr
val mk_MatOpp      : expr -> expr
val mk_MatSplitLeft : expr -> expr
val mk_MatSplitRight : expr -> expr
val mk_SplitLeft   : expr -> expr
val mk_SplitRight  : expr -> expr
val mk_MatConcat    : expr -> expr -> expr
val mk_Concat      : expr -> expr -> expr
val mk_FPlus       : expr list -> expr
val mk_FMult       : expr list -> expr
val mk_Xor         : expr list -> expr
val mk_Land        : expr list -> expr
val mk_Lor         : expr list -> expr
val mk_InEq        : expr -> expr -> expr
val mk_ListNop     : nop -> expr list -> expr
val mk_MatPlus     : expr list -> expr
val mk_MatPlus_safe: expr list -> ty -> expr
val mk_ListMatPlus_safe: expr list -> ty -> expr


(* list forget / lift *)
val listForgetExprs : expr -> expr
val listRememberExprs : expr -> expr

(* ** Generic functions on [expr]
 * ----------------------------------------------------------------------- *)

(** [e_sub_map f e] non-recursively applies [f] to all
    direct sub-expressions of [e], e.g.,
    if [e=Xor(a,b)] then a new term [Xor(f a, f b)] is returned.
    [e_sub_map] saves hashcons calls by detecting when [f] returns
    its argument unchanged.
    [e_sub_map] raises an exception if [f] changes the type. *)
val e_sub_map : (expr -> expr) -> expr -> expr

(** [e_fold f acc e] applies [f] to all direct sub-expressions of [e], e.g.,
    the results for [e=Xor(a,b)] is [f (f acc a) b]. *)
val e_sub_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a

(** [e_sub_iter f e] executes [f] for all direct sub-expressions of [e]
    for [f] s side-effects. *)
val e_sub_iter : (expr -> unit) -> expr -> unit

(** [e_iter f e] executes [f] for all sub-expressions of [e] (including e)
    for [f] s side-effects. *)
val e_iter : (expr -> unit) -> expr -> unit

(** [e_exists p e] returns [true] if there is a subterms of [e] (including
    [e] itself) that satisfies [p]. *)
val e_exists : (expr -> bool) -> expr -> bool

(** [e_forall p e] returns [true] if all subterms of [e]
    (including [e] itself) satisfy [p]. *)
val e_forall : (expr -> bool) -> expr -> bool

(** [e_find p e] return the first [e'] that is a subterm of [e] and satisfies [p].
    If there is no such [e'], then [Not_found] is raised *)
val e_find : (expr -> bool) -> expr -> expr

(** [e_find_all p e] returns the the set of all [e'] that are subterms
    of [e] and satisfy [p]. *)
val e_find_all : (expr -> bool) -> expr -> Se.t

(** [e_map f e] applies [f] recursively to all subterms of [e] proceeding
    in a bottom-up fashion. *)
val e_map : (expr -> expr) -> expr -> expr

val e_map_ty_maximal : ty -> (expr -> expr) -> expr -> expr

(** [e_map_top f e] applies [f] recursively to all subterms of [e] proceeding
    in a top-down fashion. If [f] raises [Not_found], then [e_map_top]
    proceeds by applying [f] to the direct sub-expressions of the given
    expression. Otherwise, it returns without applying [f] to the
    subexpressions.  *)
val e_map_top : (expr -> expr) -> expr -> expr

(** [e_replace e1 e2 e] replaces all occurences of [e1] in [e] with [e2] *)
val e_replace : expr -> expr -> expr -> expr

(** [e_subst s e] replaces all occurences (in [e]) of elements [e1]
    in [dom(s)] with [s(e1)]. *)
val e_subst : expr Me.t -> expr -> expr
