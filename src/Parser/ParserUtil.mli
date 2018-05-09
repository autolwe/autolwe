(* * Types and conversion functions for parsed types, expressions, ... *)

open Expr
open Type
open Game
open GameUtils
open Syms
open TheoryTypes
open ParserTypes

exception ParseError of string

val fail_parse : string -> 'a

val create_var : vmap -> theory_state -> string qual -> string -> ty -> VarSym.t

val get_oname_from_opos : sec_exp -> ocmd_pos -> string

val ty_of_parse_ty : theory_state -> parse_ty -> ty

val mk_Tuple : expr list -> expr

val bind_of_parse_bind :
  vmap -> theory_state -> (string * string) list -> (VarSym.t * RoSym.t) list

val expr_of_parse_expr : vmap -> theory_state -> string qual -> parse_expr -> expr

val lcmd_of_parse_lcmd : vmap -> theory_state -> oname:string -> lcmd -> Game.lcmd

val odef_of_parse_odef :
  vmap -> theory_state -> ParserTypes.odef -> Game.odef

val gcmd_of_parse_gcmd : vmap -> theory_state -> gcmd -> Game.gcmd

val gdef_of_parse_gdef : vmap -> theory_state -> gcmd list -> Game.gcmd list

val ev_of_parse_ev : vmap -> theory_state -> parse_ev -> ev

val se_of_parse_se : vmap -> theory_state -> gcmd list -> parse_ev -> sec_exp
