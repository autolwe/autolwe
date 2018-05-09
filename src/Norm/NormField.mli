(* * Compute normal form of field expressions *)

open Expr
open PolyInterfaces

type fexp

module EP : (Poly with type var := expr and type coeff := Big_int.big_int)

val import_ipoly : string -> Poly.IP.t -> (int, Expr.expr) Hashtbl.t -> expr

val norm_fe : fexp -> Poly.ipoly * Poly.ipoly

val abstract_non_field_multiple :
      (Expr.expr -> Expr.He.key) ->
      Expr.expr list -> fexp list * int * (int, expr) Hashtbl.t

val ep_to_ip : EP.t list -> Poly.IP.t list * (int, Expr.expr) Hashtbl.t

val exp_of_poly : EP.t -> expr

val reduce : EP.t -> EP.t -> expr

val div : EP.t -> EP.t -> Expr.expr

val abstract_non_field : (expr -> He.key) -> expr -> fexp * int * (int, expr) Hashtbl.t

(* below not required for core rules *)

val polys_of_field_expr :  expr -> EP.t * EP.t option

val div_factors : EP.t -> EP.t -> expr list option

val div_factor : EP.t -> EP.t -> expr

val div_reduce : EP.t -> EP.t -> expr * expr

val div_EP : EP.t -> EP.t -> EP.t

val factor_out : expr -> EP.t -> EP.t * EP.t

module Hep : Hashtbl.S with type key = EP.t
