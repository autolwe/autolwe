(* * Well-formedness of games. *)

open Syms
open Expr

exception Wf_var_undef of VarSym.t * expr * VarSym.S.t

exception Wf_div_zero of Expr.expr list

type wf_check_type = CheckDivZero | NoCheckDivZero

type wf_state

val mk_wfs : unit -> wf_state

val ensure_name_fresh : wf_state -> Util.Sstring.elt -> wf_state

val ensure_names_fresh : wf_state -> Util.Sstring.elt list -> wf_state

val ensure_varname_fresh : wf_state -> VarSym.S.elt -> wf_state

val ensure_varnames_fresh : wf_state -> VarSym.S.elt list -> wf_state

val check_nonzero : wf_check_type -> wf_state -> Expr.expr -> bool

val wf_expr : wf_check_type -> wf_state -> Expr.expr -> unit

val wf_lcmds : wf_check_type -> wf_state -> (VarSym.S.t ref) option -> Game.lcmd list -> wf_state

val wf_odef : wf_check_type -> wf_state -> (VarSym.S.t ref) option-> Game.odef -> unit

val wf_gdef : wf_check_type -> Game.gcmd list -> wf_state

val wf_se : wf_check_type -> Game.sec_exp -> unit
