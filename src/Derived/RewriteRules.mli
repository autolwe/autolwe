(* * Derived tactics for rewriting. *)

open Expr
open Tactic
open TheoryTypes
open Syms
open Game

val t_norm : ?fail_eq:bool -> ?strong:bool -> tactic

val t_rename : VarSym.t -> VarSym.t -> tactic

val t_norm_nounfold : tactic

val t_unfold_only : tactic

val t_norm_unknown : theory_state -> expr list -> tactic

val t_norm_solve : expr -> tactic

val t_let_abstract : int -> VarSym.t -> expr -> int option -> bool -> tactic

val t_let_abstract_oracle : ocmd_pos -> VarSym.t -> expr -> int option -> bool -> tactic

val t_let_unfold : int -> tactic

val t_norm_tuple_proj : tactic

val t_subst : int -> expr -> expr -> int option -> tactic

val t_abstract_deduce :
  keep_going:bool -> theory_state -> int -> VarSym.t -> expr -> int option -> tactic
