open Expr

val norm_mat_expr : (expr -> expr) -> expr -> expr

val norm_ifte : (expr -> expr) -> expr -> expr -> expr -> expr
