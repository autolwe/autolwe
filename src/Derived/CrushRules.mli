(* * Automated derived rules *)

open Tactic
open CoreRules
open TheoryTypes

val t_crush : bool -> int option -> theory_state -> proof_state -> tactic
