(* * Tactic engine: transformations of proof states. *)

open Abbrevs
open CoreTypes
open TheoryTypes
open ParserTypes

val pp_jus : int -> F.formatter -> judgment list -> unit

val handle_instr : bool -> theory_state -> instr -> theory_state * string

val handle_instrs : bool -> theory_state -> instr list -> theory_state * string

val eval_theory : string -> theory_state
