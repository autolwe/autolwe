(* * Normal form computation for expressions. *)

open Expr

(** [norm_expr e] computes the normal form of the expression [e], if strong is true,
    then and will be sorted and equations a = b will be simplified to a - b = 0. *)
val norm_expr : strong:bool -> expr -> expr

val norm_expr_weak : expr -> expr

val norm_expr_strong : expr -> expr

(** [equalmod_expr e1 e2] (strongly) normalizes both terms to check if they
    are equal modulo the equational theory. *)
val equalmod_expr : expr -> expr -> bool
