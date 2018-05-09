open Expr
open ExprUtils

val solve_mat_list : (expr * inverter) list -> expr -> inverter
val solve_other_list : (expr * inverter) list -> expr -> inverter
