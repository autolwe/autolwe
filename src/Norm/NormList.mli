open Expr

val norm_list_expr : (expr -> expr) -> expr -> expr
val norm_list_ifte : (expr -> expr) -> expr -> expr -> expr -> expr
