(* * Non-core functions for normal form *)

open Expr

val remove_tuple_proj : expr -> expr

val norm_expr_nice : expr -> expr

val destr_Eq_norm : expr -> expr option

val abbrev_ggen : expr -> expr

val destr_Neq_norm : expr -> expr option
