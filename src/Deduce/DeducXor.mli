(* * Deducibility of Xor expressions. *)

open Expr
open ExprUtils

(** [solve_xor ecs e] tries to compute an xor context that
    deduces [e] from [List.map fst es] and returns the
    context assuming that [List.map fst es] are the contexts
    for these known terms. *)
val solve_xor : (expr * inverter) list -> expr -> inverter
