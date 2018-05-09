(* * Simplification rules *)

open Tactic

val t_simp : bool -> int -> tactic

val t_ctx_ev_maybe : int option -> tactic

val t_split_ineq : int -> tactic
