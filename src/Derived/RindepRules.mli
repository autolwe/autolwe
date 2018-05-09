(* * Derived rules for dealing with random independence. *)

open Tactic
open TheoryTypes

val t_random_indep : theory_state -> bool -> tactic
