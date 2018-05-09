(* * Deducibility for field expressions. *)

open Syms
open Expr
open ExprUtils

(** [solve_fq ecs e] tries to compute a field context that
    deduces [e] from [List.map snd es] and returns the
    context assuming that [List.map fst es] are the contexts
    for these known terms. *)
val solve_fq : (expr * inverter) list -> expr -> inverter

val solve_fq_vars_known : expr -> VarSym.t  -> expr

val solve_mixed_type : expr -> VarSym.t -> ctxt
