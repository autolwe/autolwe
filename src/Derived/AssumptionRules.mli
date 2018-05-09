(* * Derived tactics for dealing with assumptions. *)

open Util
open TheoryTypes

val t_assm_dec_o : 
  TheoryTypes.theory_state ->
  string ->
  Util.direction ->
  ParserTypes.renaming list ->
  ParserTypes.range_o list ->
  Tactic.tactic

val t_assm_dec :
  ?i_assms:Util.Sstring.t ->
  theory_state ->
  bool ->
  string option ->
  direction option ->
  ((int * int) list) option ->
  (string list) option ->
  Tactic.tactic

val t_assm_comp :
  ?icases:Expr.Se.t ->
  theory_state ->
  bool ->
  string option ->
  ((int * int) list) option ->
  Tactic.tactic
