(* * Cryptographic game definitions *)

(* ** Imports and Abbreviations*)
open Abbrevs
open Type
open Expr
open Syms

(** Variable, adversary, oracle, function, and oracle list symbols. *)
type vs  = VarSym.t
type ads = AdvSym.t
type os  = OrclSym.t
type hs  = FunSym.t
type ors = Olist.t

(* ** Types for oracles, games, and security
 * ----------------------------------------------------------------------- *)

(** (Excepted) Distributions for sampling. *)
type distr = ty * expr list  (* uniform distr. over type except for given values *)
  with compare

(** List monad command for oracle definition. *)
type lcmd =
  | LLet   of VarSym.t * expr          (* LLet(xs,e):     let (x_1,..,x_k) = e *)
  | LMSet  of MapSym.t * expr * expr   (* LMSet(m,ek,ev): m[ek] <- ev          *)
  | LBind  of VarSym.t list * FunSym.t (* LBind(xs, h):   (x_1,..,x_k) <- L_h  *)
  | LSamp  of VarSym.t * distr         (* LSamp(x,d):     x <$ d               *)
  | LGuard of expr                     (* LGuard(t):      guard(t)             *)
  with compare

(** Oracle body *)
type obody = lcmd list * Expr.expr (* (ms, e): m1; ..; mk; return e *)
  with compare

(** Oracle body for hybrid oracle *)
type ohybrid = {
  oh_less    : obody; (* oracle body for queries <i *)
  oh_eq      : obody; (* oracle body for queries =i *)
  oh_greater : obody; (* oracle body for queries >i *)
} with compare

(** Oracle declaration *)
type odecl =
  | Oreg of obody   (* regular oracle *)
  | Ohyb of ohybrid (* hybrid oracle *)
  with compare

(** Oracle counter *)
type counter =
  | NoCounter
  | Once
  | CountVar of string
  with compare

(** Oracle definition. *)
type odef = OrclSym.t * VarSym.t list * odecl * counter
  (* (o,xs,ms,e): o(x_1,..,x_l) = [e | m_1, .., m_k] *)
  with compare

(** Game command. *)
type gcmd =
  | GLet    of VarSym.t * expr          (* GLet(xs,e):     let (x_1,..,x_k) = e             *)
  | GMSet   of MapSym.t * expr * expr   (* GMSet(m,ek,ev): m[ek] <- ev                      *)
  | GAssert of expr                     (* GAssert(e):     assert(e)                        *)
  | GSamp   of VarSym.t * distr         (* GSamp(x,d):     x <$ d                           *)
  | GCall   of VarSym.t list * AdvSym.t (* GCall(xs,e,os): (x1,..,xk) <@ A(e) with o1,..,ol *)
               * expr * odef list
  with compare

(** Game definition. *)
type gdef = gcmd list
  with compare

(** An event is just an expression *)
type ev = expr
  with compare

(** A security experiment consists of a game and an event. *)
type sec_exp = {
  se_gdef : gdef;
  se_ev   : ev;
} with compare


(* ** Equality and indicator functions *
 * ----------------------------------------------------------------------- *)

val equal_distr   : distr     -> distr     -> bool
val equal_lcmd    : lcmd      -> lcmd      -> bool
val equal_lcmds   : lcmd list -> lcmd list -> bool
val equal_obody   : obody     -> obody     -> bool
val equal_ohybrid : ohybrid   -> ohybrid   -> bool
val equal_odecl   : odecl     -> odecl     -> bool
val equal_odef    : odef      -> odef      -> bool
val equal_gcmd    : gcmd      -> gcmd      -> bool
val equal_gdef    : gdef      -> gdef      -> bool
val equal_sec_exp : sec_exp   -> sec_exp   -> bool

val is_call : gcmd -> bool
val has_call : gcmd list -> bool

val is_assert : gcmd -> bool
val has_assert : gcmd list -> bool

val destr_guard : lcmd -> expr

(** Hybrid oracle type *)
type ohtype = OHless | OHeq | OHgreater with compare

(** Oracle type *)
type otype = Onothyb | Oishyb of ohtype with compare

val is_hybrid : otype -> bool

(* ** Generic functions: [map_*_expr] and [iter_*_expr]
 * ----------------------------------------------------------------------- *)

(* *** map *)

val map_distr_exp : (expr -> expr) -> distr   -> distr
val map_lcmd_exp  : (expr -> expr) -> lcmd    -> lcmd
val map_obody_exp : (expr -> expr) -> obody   -> obody
val map_odecl_exp : (expr -> expr) -> odecl   -> odecl
(* val map_oh_exp    : (expr -> expr) -> ohtype  -> ohtype *)
val map_gcmd_exp  : (expr -> expr) -> gcmd    -> gcmd
val map_gdef_exp  : (expr -> expr) -> gdef    -> gdef
val map_se_exp    : (expr -> expr) -> sec_exp -> sec_exp

val map_ohybrid   : (obody -> obody) -> ohybrid -> ohybrid

(* *** iter *)

val iter_distr_exp        : ?iexc:bool -> (expr -> unit) -> distr   -> unit
val iter_lcmd_exp         : ?iexc:bool -> (expr -> unit) -> lcmd    -> unit
val iter_obody_exp        : ?iexc:bool -> (expr -> unit) -> obody   -> unit
val iter_ohybrid_exp      : ?iexc:bool -> (expr -> unit) -> ohybrid -> unit
val iter_odecl_exp        : ?iexc:bool -> (expr -> unit) -> odecl   -> unit
val iter_gcmd_exp         : ?iexc:bool -> (expr -> unit) -> gcmd    -> unit
val iter_gcmd_exp_orcl    : ?iexc:bool -> (expr -> unit) -> gcmd    -> unit
val iter_gcmd_exp_no_orcl : ?iexc:bool -> (expr -> unit) -> gcmd    -> unit
val iter_gdef_exp         : ?iexc:bool -> (expr -> unit) -> gdef    -> unit
val iter_se_exp           : ?iexc:bool -> (expr -> unit) -> sec_exp -> unit

(* ** Positions and replacement functions
 * ----------------------------------------------------------------------- *)

type gcmd_pos = int with compare

type oh_pos = (int * int) with compare

type ocmd_pos = (int * int * int * otype) with compare

type ocmd_pos_eq = (int * int * int) with compare


type se_ctxt = {
  sec_left  : gdef;
  sec_right : gdef;
  sec_ev    : expr;
}

type se_octxt = {
  seoc_asym      : ads;
  seoc_avars     : vs list;
  seoc_aarg      : expr;
  seoc_oleft     : odef list;
  seoc_oright    : odef list;
  seoc_obless    : obody option;
  seoc_obeq      : obody option;
  seoc_obgreater : obody option;
  seoc_osym      : os;
  seoc_oargs     : vs list;
  seoc_ocounter  : counter;
  seoc_return    : expr;
  seoc_cleft     : lcmd list;
  seoc_cright    : lcmd list;
  seoc_sec       : se_ctxt;
}

val get_se_gcmd : sec_exp -> gcmd_pos -> gcmd

val get_se_ctxt_len : sec_exp -> pos:int -> len:int -> gdef * se_ctxt

val get_se_ctxt : sec_exp -> int -> gcmd * se_ctxt

val set_se_ctxt : gcmd list -> se_ctxt -> sec_exp

val set_se_gcmd : sec_exp -> gcmd_pos -> gcmd list -> sec_exp

val get_obody : odecl -> otype -> obody

val get_se_lcmd :
  sec_exp -> ocmd_pos -> os * vs list * (lcmd list * lcmd * lcmd list) * expr * counter

val get_se_octxt_len : sec_exp -> ocmd_pos -> int -> lcmd list * se_octxt

val set_se_octxt : lcmd list -> se_octxt -> sec_exp

val get_se_octxt : sec_exp -> ocmd_pos -> lcmd * se_octxt

val set_se_lcmd : sec_exp -> ocmd_pos -> lcmd list -> sec_exp

(* ** Read and write variables
 * ----------------------------------------------------------------------- *)

val read_distr   : distr     -> Se.t
val read_lcmd    : lcmd      -> Se.t
val read_lcmds   : lcmd list -> Se.t
val write_lcmd   : lcmd      -> Se.t
val write_lcmds  : lcmd list -> Se.t
(* val read_obody   : obody     -> Se.t *)
(* val read_ohybrid : ohybrid   -> Se.t *)
(* val read_odecl   : odecl     -> Se.t *)
val read_odef    : odef      -> Se.t
val read_odefs   : odef list -> Se.t
val read_gcmd    : gcmd      -> Se.t
val read_gcmds   : gcmd list -> Se.t
val write_gcmd   : gcmd      -> Se.t
val write_gcmds  : gcmd list -> Se.t
val read_se      : sec_exp   -> Se.t
val asym_gcmd    : gcmd      -> AdvSym.t option
val asym_gcmds   : gcmd list -> AdvSym.t list

(* ** Find expressions that satisfy predicate
 * ----------------------------------------------------------------------- *)

(* val fold_union_e : string *)

val find_expr           : (expr -> bool) -> expr -> Se.t
val find_exprs          : (expr -> bool) -> expr list -> Se.t
val find_lcmd           : (expr -> bool) -> lcmd -> Se.t
val find_lcmds          : (expr -> bool) -> lcmd list -> Se.t
val find_obody          : (expr -> bool) -> obody -> Se.t
val find_ohybrid        : (expr -> bool) -> ohybrid -> Se.t
val find_odecl          : (expr -> bool) -> odecl -> Se.t
(* val find_oh             : (expr -> bool) -> oh -> Se.t *)
val find_all_gcmd       : (expr -> bool) -> gcmd -> Se.t
val find_all_gdef       : (expr -> bool) -> gdef -> Se.t
val find_global_ohybrid : (expr -> bool) -> ohybrid -> Se.t
(* val find_global_oh      : (expr -> bool) -> oh -> Se.t *)
val find_global_gcmd    : (expr -> bool) -> gcmd -> Se.t
val find_global_gdef    : (expr -> bool) -> gdef -> Se.t

(* ** Random oracle symbol occurences in RO calls
 * ----------------------------------------------------------------------- *)

(* val ro_syms_of_es : string *)
val ro_syms_expr        : expr -> RoSym.S.t
val ro_syms_all_gcmd    : gcmd -> RoSym.S.t
val ro_syms_all_gdef    : gdef -> RoSym.S.t
val ro_syms_global_gdef : gdef -> RoSym.S.t

(* ** Random oracle arguments for given RO symbol
 * ----------------------------------------------------------------------- *)

(* val harg_of_es : string *)

val is_H_call : RoSym.t -> expr -> bool

val hash_args_expr        : RoSym.t -> expr -> Se.t
val hash_args_all_gcmd    : RoSym.t -> gcmd -> Se.t
val hash_args_all_gdef    : RoSym.t -> gdef -> Se.t
val hash_args_global_gdef : RoSym.t -> gdef -> Se.t

(* ** Variable occurences
 * ----------------------------------------------------------------------- *)

(* val fold_union_vs : string *)
val set_of_list : vs list -> VarSym.S.t

val vars_expr : expr -> VarSym.S.t
val vars_exprs : expr list -> VarSym.S.t
val vars_lcmd : lcmd -> VarSym.S.t
val vars_lcmds : lcmd list -> VarSym.S.t
val vars_obody : obody -> VarSym.S.t
val vars_ohybrid : ohybrid -> VarSym.S.t
val vars_odecl : odecl -> VarSym.S.t
(* val vars_oh : string *)
val vars_all_gcmd : gcmd -> VarSym.S.t
val vars_all_gdef : gdef -> VarSym.S.t
val vars_global_ohybrid : ohybrid -> VarSym.S.t
(* val vars_global_oh : string *)
val vars_global_gcmd : gcmd -> VarSym.S.t
val vars_global_gdef : gdef -> VarSym.S.t

(* ** Variable renaming
 * ----------------------------------------------------------------------- *)

val subst_v_expr  : (vs -> vs) -> expr    -> expr
val subst_v_lcmd  : (vs -> vs) -> lcmd    -> lcmd
val subst_v_obody : (vs -> vs) -> obody   -> obody
val subst_v_odecl : (vs -> vs) -> odecl   -> odecl
val subst_v_odef  : (vs -> vs) -> odef    -> odef
val subst_v_gcmd  : (vs -> vs) -> gcmd    -> gcmd
val subst_v_gdef  : (vs -> vs) -> gdef    -> gdef
val subst_v_se    : (vs -> vs) -> sec_exp -> sec_exp

type renaming = vs VarSym.M.t

val id_renaming : renaming
val ren_injective : renaming -> bool
val pp_ren : F.formatter -> vs VarSym.M.t -> unit

(* ** Unification
 * ----------------------------------------------------------------------- *)

(* val ensure_same_length : string *)
(* val vht_to_map : string *)

val unif_vs    : vs VarSym.H.t -> vs    -> vs    -> unit
val unif_expr  : vs VarSym.H.t -> expr  -> expr  -> unit
val unif_lcmd  : vs VarSym.H.t -> lcmd  -> lcmd  -> unit
val unif_obody : vs VarSym.H.t -> obody -> obody -> unit
val unif_odecl : vs VarSym.H.t -> odecl -> odecl -> unit
val unif_odef  : vs VarSym.H.t -> odef  -> odef  -> unit
val unif_gcmd  : vs VarSym.H.t -> gcmd  -> gcmd  -> unit

val unif_se    : sec_exp -> sec_exp -> vs VarSym.M.t
val unif_gdef  : gdef    -> gdef    -> vs VarSym.M.t

(* ** Probabilistic polynomial time
 * ----------------------------------------------------------------------- *)

val has_log_distr : distr     -> bool
val has_log_lcmd  : lcmd      -> bool
val has_log_lcmds : lcmd list -> bool
val has_log_obody : obody     -> bool
val has_log_odecl : odecl     -> bool
val has_log_odef  : odef      -> bool
val has_log_gcmd  : gcmd      -> bool
val has_log_gcmds : gcmd list -> bool

val is_ppt_distr : distr     -> bool
val is_ppt_lcmd  : lcmd      -> bool
val is_ppt_lcmds : lcmd list -> bool
val is_ppt_obody : obody     -> bool
val is_ppt_odecl : odecl     -> bool
val is_ppt_odef  : odef      -> bool
val is_ppt_gcmd  : gcmd      -> bool
val is_ppt_gcmds : gcmd list -> bool
val is_ppt_se    : sec_exp   -> bool

(* ** Normal forms
 * ----------------------------------------------------------------------- *)

val norm_default : expr -> expr
val norm_distr : ?norm:(expr -> expr) -> expr Me.t -> distr   -> distr
(* val norm_obody : ?norm:(expr -> expr) -> expr Me.t -> obody   -> obody *)
(* val norm_odef  : ?norm:(expr -> expr) -> expr Me.t -> odef    -> odef *)
val norm_gdef  : ?norm:(expr -> expr) -> gdef    -> gdef * expr Me.t
val norm_se    : ?norm:(expr -> expr) -> sec_exp -> sec_exp

(* ** finite maps transformations
 * ----------------------------------------------------------------------- *)

val map_se_finmap :
  f_lookup:(MapSym.t -> expr -> expr) ->
  f_in_dom:(MapSym.t -> expr -> expr) ->
  f_LMSet:(MapSym.t -> expr -> expr -> lcmd list) ->
  f_GMSet:(MapSym.t -> expr -> expr -> gcmd list) ->
  sec_exp -> sec_exp
 

(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

val pp_ocounter : F.formatter -> counter -> unit
val pp_distr : qual:os qual -> F.formatter -> ty * expr list -> unit
val pp_v : F.formatter -> VarSym.t -> unit
val pp_binder : qual:os qual -> F.formatter -> vs list -> unit
val pp_lcmd : qual:os qual -> F.formatter -> lcmd -> unit
val pp_lcmds : qual:os qual -> F.formatter -> lcmd list -> unit
val pp_ilcmd : nonum:bool -> qual:os qual -> F.formatter -> int * lcmd -> unit
val pp_lcomp : nonum:bool -> qual:os qual -> F.formatter -> expr * lcmd list -> unit
val string_of_otype : ohtype -> string
val pp_ohtype : F.formatter -> ohtype -> unit
val pp_otype : F.formatter -> otype -> unit
val pp_obody :nonum:bool -> os -> ohtype option -> F.formatter -> lcmd list * expr -> unit
val pp_ohybrid : nonum:bool -> os -> F.formatter -> ohybrid -> unit
val pp_odecl : nonum:bool -> os -> F.formatter -> odecl -> unit
val pp_odef : nonum:bool -> F.formatter -> os * vs list * odecl * counter -> unit
val pp_gcmd : nonum:bool -> F.formatter -> gcmd -> unit
val pp_igcmd : F.formatter -> int * gcmd -> unit
val pp_gdef : nonum:bool -> F.formatter -> gcmd list -> unit
val pp_se : F.formatter -> sec_exp -> unit
val pp_se_nonum : F.formatter -> sec_exp -> unit
val pp_ps : F.formatter -> sec_exp list -> unit

(* ----------------------------------------------------------------------- *)
val sv_of_se : Expr.Se.t -> Syms.VarSym.S.t
val game_vars : gcmd list -> Syms.VarSym.S.t

