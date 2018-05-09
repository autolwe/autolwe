(* * Deducibility of expressions. *)

open Expr
open ExprUtils
open TheoryTypes

val invert : ?ppt_inverter:bool -> theory_state -> (expr * inverter) list -> expr -> inverter
