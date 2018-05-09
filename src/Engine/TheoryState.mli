(* * Goals and mappings from strings to variables/symbols. *)

open Type
open Nondet
open CoreRules
open TheoryTypes

val mk_ts : unit -> theory_state

val get_proof_state : theory_state -> proof_state

val get_proof_state_back : theory_state -> proof_state nondet

val get_proof_tree : theory_state -> proof_tree

val create_lenvar : theory_state -> string -> Lenvar.id

val create_groupvar : theory_state -> string -> Groupvar.id

(* val create_permvar : theory_state -> string -> Permvar.id *)
