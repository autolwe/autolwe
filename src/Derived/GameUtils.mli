(* * Utility functions for cryptographic game definitions *)

(* ** Imports *)
open Abbrevs
open Expr
open Syms
open Game
open Type

(* ** Iterate with context
 * ----------------------------------------------------------------------- *)

type iter_pos =
  | InEv
  | InMain       of gcmd_pos
  | InOrclReturn of ocmd_pos * ty * ty
  | InOrcl       of ocmd_pos * ty * ty
    (* position, adversary argument type, oracle type *)

type iter_ctx = {
  ic_pos     : iter_pos;
  ic_isZero  : expr list;
  ic_nonZero : expr list
}

val pp_iter_pos : F.formatter -> iter_pos -> unit
val pp_iter_ctx : F.formatter -> iter_ctx -> unit

val empty_iter_ctx : iter_pos -> iter_ctx

val iter_ctx_obody_exp :
  ty -> int -> int -> expr list ->
  ?iexc:bool -> (iter_ctx -> expr -> unit) ->
  os -> Game.otype -> Game.lcmd list * Expr.expr -> unit
val iter_ctx_odecl_exp :
  ty -> int -> int -> expr list ->
  ?iexc:bool -> (iter_ctx -> expr -> unit) ->
  os -> odecl -> unit
val iter_ctx_gdef_exp  :
   ?iexc:bool ->
   (iter_ctx -> expr -> unit) ->
   gcmd list -> expr list
val iter_ctx_se_exp :
   ?iexc:bool -> (iter_ctx -> ev -> unit) -> sec_exp -> unit


(* ** Mappings from strings to variables
 * ----------------------------------------------------------------------- *)

type vmap = (string qual * string,VarSym.t) Hashtbl.t

val create_vmap     :  Syms.VarSym.S.t -> vmap
val merge_vmap      : vmap -> vmap -> vmap * (vs -> vs)
val vmap_of_vss     : VarSym.S.t -> vmap
val vmap_of_ves     : Se.t -> vmap
val vmap_of_globals : gdef -> vmap
val vmap_of_se      : sec_exp -> vmap
val ves_to_vss      : Se.t -> VarSym.S.t
val vmap_in_orcl    : sec_exp -> ocmd_pos -> vmap
