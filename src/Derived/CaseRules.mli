(* * Derived rules for dealing with [add_test], [case_ev], and [except]. *)

open Tactic
open TheoryTypes

val t_rexcept_maybe : int option -> (ParserTypes.parse_expr list) option -> tactic

val t_case_ev_maybe : tactic

val t_guard_maybe : tactic

val print_cases : theory_state -> theory_state * string
