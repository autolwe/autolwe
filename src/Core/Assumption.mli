(* * Decisional and computational assumptions. *)

(* ** Imports *)

open Abbrevs
open Util
open Syms
open Expr
open Game

(* ** Decisional assumptions
 * ----------------------------------------------------------------------- *)

type assm_dec_orcls = 
  OrclSym.t * VarSym.t list * (obody * obody) * counter

(* adversary calls, same asym and returned variables,  
   argument and oracle on left and right      *)
type assm_dec_adv_call = {
   ad_ac_sym   : AdvSym.t;
   ad_ac_lv    : VarSym.t list;
   ad_ac_args  : expr * expr;
   ad_ac_orcls : assm_dec_orcls list;
  }
    
type assm_dec = {
  ad_name       : string;       (* name of assumption *)
  ad_inf        : bool;         (* information-theoretic assumption *)
  ad_prefix1    : gdef;         (* prefix for left *)
  ad_prefix2    : gdef;         (* prefix for right *)
  ad_acalls     : assm_dec_adv_call list;
  ad_symvars    : vs list list; (* symmetric in given variables *)
}

val pp_assm_dec :  F.formatter -> assm_dec -> unit

val mk_assm_dec : string -> bool -> gdef -> gdef -> (VarSym.t list) list -> assm_dec

val needed_vars_dec : direction  -> assm_dec -> VarSym.t list

val private_vars_dec : assm_dec -> Se.t

val inst_dec : VarSym.t VarSym.M.t -> assm_dec -> assm_dec

(* ** Computational assumptions
 * ----------------------------------------------------------------------- *)

type assm_type = A_Succ | A_Adv

val pp_atype : F.formatter -> assm_type -> unit

type assm_comp = private {
  ac_name       : string;       (*r name of assumption *)
  ac_inf        : bool;         (*r information-theoretic assumption *)
  ac_type       : assm_type;    (* type of assumption *)
  ac_prefix     : gdef;         (*r prefix of assumption *)
  ac_event      : expr;         (*r event expression *)
  ac_acalls     : (AdvSym.t * VarSym.t list * expr) list;
   (*r adversary calls (same asym) and arguments/returned variables *)
  ac_symvars    : vs list list; (*r symmetric in given variables *)
}

val pp_assm_comp :  F.formatter -> assm_comp -> unit

val mk_assm_comp : string -> bool -> assm_type -> gdef -> expr -> vs list list -> assm_comp

val private_vars_comp : assm_comp -> Se.t

val inst_comp : VarSym.t VarSym.M.t -> assm_comp -> assm_comp
