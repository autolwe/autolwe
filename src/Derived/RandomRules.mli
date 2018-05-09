(* * Derived rules for dealing with random samplings. *)

open TheoryTypes
open ParserTypes

val t_rnd_maybe :
  ?i_rvars:Syms.VarSym.S.t
  -> theory_state
  -> bool
  -> Game.gcmd_pos option
  -> parse_ctx option
  -> parse_ctx option
  -> Expr.expr option
  -> Tactic.tactic

val t_rnd_oracle_maybe :
  ?i_rvars:Syms.VarSym.S.t
  -> theory_state
  -> Game.ocmd_pos option
  -> parse_ctx option
  -> parse_ctx option
  -> Tactic.tactic
