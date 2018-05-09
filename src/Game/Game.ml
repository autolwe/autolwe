(* * Cryptographic game definitions *)

(* ** Imports and Abbreviations*)
open Abbrevs
open Util
open Type
open Expr
open ExprUtils
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
  | LLet   of VarSym.t * expr          (* LLet(xs,e):    let (x_1,..,x_k) = e *)
  | LMSet  of MapSym.t * expr * expr   (* LMSet(m,es,e): m[es] <- e           *)
  | LBind  of VarSym.t list * FunSym.t (* LBind(xs, h):  (x_1,..,x_k) <- L_h  *)
  | LSamp  of VarSym.t * distr         (* LSamp(x,d):    x <$ d               *)
  | LGuard of expr                     (* LGuard(t):     guard(t)             *)
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

let equal_distr d1 d2 = compare_distr d1 d2 = 0

let equal_lcmd i1 i2 = compare_lcmd i1 i2 = 0

let equal_lcmds c1 c2 = list_eq_for_all2 equal_lcmd c1 c2

let equal_obody ob1 ob2 = compare_obody ob1 ob2 = 0

let equal_ohybrid oh1 oh2 = compare_ohybrid oh1 oh2 = 0

let equal_odecl od1 od2 = compare_odecl od1 od2 = 0

let equal_odef oh1 oh2 = compare_odef oh1 oh2 = 0

let equal_gcmd g1 g2 = compare_gcmd g1 g2 = 0

let equal_gdef c1 c2 = list_eq_for_all2 equal_gcmd c1 c2

let equal_sec_exp se1 se2 = compare_sec_exp se1 se2 = 0

let is_call = function
  | GCall _ -> true
  | _       -> false

let has_call c = L.exists is_call c

let is_assert = function
  | GAssert _ -> true
  | _         -> false

let has_assert c =  L.exists is_assert c

let destr_guard lcmd =
  match lcmd with
  | LGuard(e) -> e
  | _ -> assert false (* FIXME *)

(** Hybrid oracle type *)
type ohtype = OHless | OHeq | OHgreater with compare

(** Oracle type *)
type otype = Onothyb | Oishyb of ohtype with compare

let is_hybrid = function Onothyb -> false | Oishyb _ -> true

(* ** Generic functions: [map_*_expr] and [iter_*_expr]
 * ----------------------------------------------------------------------- *)

(* *** map *)

let map_distr_exp f (t,es) = (t, L.map f es)

let map_lcmd_exp f = function
  | LLet(vs,e)     -> LLet(vs,f e)
  | LMSet(m,ek,ev) -> LMSet(m,f ek,f ev)
  | LBind(vs,h)    -> LBind(vs,h)
  | LSamp(v,d)     -> LSamp(v,map_distr_exp f d)
  | LGuard(e)      -> LGuard(f e)


let map_ohybrid f {oh_less; oh_eq; oh_greater} = {
  oh_less    = f oh_less;
  oh_eq      = f oh_eq;
  oh_greater = f oh_greater;
}

let map_obody_exp f (ms,e) =
  L.map (map_lcmd_exp f) ms, f e

let map_odecl_exp f = function
  | Oreg od -> Oreg (map_obody_exp f od)
  | Ohyb oh -> Ohyb (map_ohybrid (map_obody_exp f) oh)

let map_oh_exp f (o,vs,od,c) =
  (o,vs,map_odecl_exp f od,c)

let map_gcmd_exp f = function
  | GLet(vs,e)          -> GLet(vs,f e)
  | GMSet(m,ek,e)       -> GMSet(m,f ek,f e)
  | GAssert(e)          -> GAssert(f e)
  | GSamp(v,d)          -> GSamp(v,map_distr_exp f d)
  | GCall(vs,asym,e,os) -> GCall(vs,asym,f e,L.map (map_oh_exp f) os)

let map_gdef_exp f gdef =
  L.map (map_gcmd_exp f) gdef

let map_se_exp f se = {
  se_gdef = map_gdef_exp f se.se_gdef;
  se_ev   = f se.se_ev;
}

(* *** iter *)

let iter_distr_exp ?iexc:(iexc=false) f (_,es) =
  if iexc then L.iter f es

let iter_lcmd_exp ?iexc:(iexc=false) f = function
  | LLet(_,e)     -> f e
  | LMSet(_,ek,e) -> f ek; f e
  | LBind(_)      -> ()
  | LSamp(_,d)    -> iter_distr_exp ~iexc f d
  | LGuard(e)     -> f e

let iter_obody_exp ?iexc:(iexc=false) f (ms,e) =
  L.iter (iter_lcmd_exp ~iexc f) ms; f e

let iter_ohybrid_exp ?iexc:(iexc=false) f { oh_less; oh_eq; oh_greater} =
  iter_obody_exp ~iexc f oh_less;
  iter_obody_exp ~iexc f oh_eq;
  iter_obody_exp ~iexc f oh_greater

let iter_odecl_exp ?iexc:(iexc=false) f = function
  | Oreg od -> iter_obody_exp ~iexc f od
  | Ohyb oh -> iter_ohybrid_exp ~iexc f oh

let iter_oh_exp ?iexc:(iexc=false) f (_o,_vs,od,_c) =
  iter_odecl_exp ~iexc f od

let iter_gcmd_exp ?iexc:(iexc=false) f = function
  | GLet(_,e)
  | GAssert(e)      -> f e
  | GMSet(_,ek,e)   -> f ek; f e
  | GSamp(_,d)      -> iter_distr_exp ~iexc f d
  | GCall(_,_,e,od) -> f e; L.iter (iter_oh_exp ~iexc f) od

let iter_gcmd_exp_orcl ?iexc:(iexc=false) f = function
  | GLet(_,_)
  | GMSet(_,_,_)
  | GAssert(_)
  | GSamp(_,_)      -> ()
  | GCall(_,_,_,od) -> L.iter (iter_oh_exp ~iexc f) od

let iter_gcmd_exp_no_orcl ?iexc:(iexc=false) f gcmd = match gcmd with
  | GMSet(_,ek,e)  -> f ek; f e
  | GLet(_,e)
  | GAssert(e)
  | GCall(_,_,e,_) -> f e
  | GSamp(_,d)     -> iter_distr_exp ~iexc f d

let iter_gdef_exp ?iexc:(iexc=false) f gdef =
  L.iter (iter_gcmd_exp_no_orcl ~iexc f) gdef;
  L.iter (iter_gcmd_exp_orcl ~iexc f) gdef

let iter_se_exp ?iexc:(iexc=false) f se =
  iter_gdef_exp ~iexc f se.se_gdef; f se.se_ev

(* ** Pretty printing
 * ----------------------------------------------------------------------- *)

let pp_distr ~qual fmt (ty,es) =
  match es with
  | [] -> pp_ty fmt ty
  | _  -> F.fprintf fmt "@[<hov 2>%a \\ {@[<hov 0>%a}@]@]" pp_ty ty
            (pp_list "," (pp_expr_qual ~qual)) es

(* let pp_v fmt v = F.fprintf fmt "%a_%i" Vsym.pp v (Id.tag v.Vsym.id) *)
let pp_v ~qual fmt v = 
  Format.fprintf fmt "%a" (VarSym.pp_qual ~qual) v 
                 

let pp_binder ~qual fmt vs =
  match vs with
  | [v] -> pp_v ~qual fmt v
  | _   -> F.fprintf fmt "(@[<hov 0>%a@])" (pp_list "," (pp_v ~qual)) vs

let pp_v = pp_v ~qual:Unqual

let pp_lcmd ~qual fmt = function
  | LLet(vs,e)  ->
    F.fprintf fmt "@[<hov 2>let %a =@ %a@]"
      (pp_binder ~qual) [vs]
      (pp_expr_qual ~qual) e
  | LBind(vs,h) ->
    F.fprintf fmt "@[<hov 2>%a <-@ L_%a@]" (pp_binder ~qual) vs FunSym.pp h
  | LMSet(ms,ek,e) when is_Unit ek ->
    F.fprintf fmt "@[<hov 2>%a :=@ %a@]"
      MapSym.pp ms (pp_expr_qual ~qual) e
  | LMSet(ms,ek,e) ->
    F.fprintf fmt "@[<hov 2>%a[%a] :=@ %a@]"
      MapSym.pp ms (pp_expr_qual ~qual) ek (pp_expr_qual ~qual) e
  | LSamp(v,d)  ->
    F.fprintf fmt "@[<hov 2>%a <-$@ %a@]"
      (pp_binder ~qual) [v]
      (pp_distr ~qual) d
  | LGuard(e) -> F.fprintf fmt "guard (%a)" (pp_expr_qual ~qual) e

let pp_lcmds ~qual fmt lc = 
  Format.fprintf fmt "@[<v>%a@]"
    (pp_list ";@ " (pp_lcmd ~qual)) lc

let pp_ilcmd ~nonum ~qual fmt (i,lc) =
  if nonum
  then (pp_lcmd ~qual fmt) lc
  else F.fprintf fmt "%3i: %a" i (pp_lcmd ~qual) lc

let pp_lcomp ~nonum ~qual fmt (e,m) =
  match m with
  | [] ->
    F.fprintf fmt "%sreturn %a"
      (if nonum then "" else "1: ")
      (pp_expr_qual ~qual) e

  | _  ->
    F.fprintf fmt "@[%a;@\n%sreturn %a@]"
      (pp_list ";@\n" (pp_ilcmd ~nonum ~qual))
      (num_list m)
      (if nonum then "" else F.sprintf "%3i: " (L.length m + 1))
      (pp_expr_qual ~qual) e

let string_of_otype = function
  | OHless    -> "<"
  | OHeq      -> "="
  | OHgreater -> ">"

let pp_ohtype fmt oht = pp_string fmt (string_of_otype oht)

let pp_otype fmt = function
  | Onothyb     -> pp_string fmt "no hybrid"
  | Oishyb  oht -> pp_ohtype fmt oht

let pp_obody ~nonum osym ootype fmt (ms,e) =
  F.fprintf fmt "{%s@\n  @[<v>%a@] }"
    (match ootype with None -> "" | Some ot -> " (* "^string_of_otype ot^" *)")
    (pp_lcomp ~nonum ~qual:(Qual osym)) (e,ms)

let pp_ohybrid ~nonum osym fmt oh =
  F.fprintf fmt "[@\n  @[<v>%a@]@\n  @[<v>%a@]@\n  @[<v>%a@]@\n]"
    (pp_obody ~nonum osym (Some OHless))    oh.oh_less
    (pp_obody ~nonum osym (Some OHeq))      oh.oh_eq
    (pp_obody ~nonum osym (Some OHgreater)) oh.oh_greater

let pp_odecl ~nonum osym fmt = function
  | Oreg od -> pp_obody ~nonum osym None fmt od
  | Ohyb oh -> pp_ohybrid ~nonum osym fmt oh

let pp_ocounter fmt = function
  | NoCounter  -> pp_string fmt ""
  | CountVar s -> F.fprintf fmt "[counter=%s]" s
  | Once       -> pp_string fmt "[once]"


let pp_odef ~nonum fmt (o, vs, od, c) =
  F.fprintf fmt "@[<v>%a(@[<hov 0>%a@])%a = %a@]"
    OrclSym.pp o
    (pp_list "," (VarSym.pp_qual ~qual:(Qual o))) vs
    pp_ocounter c
    (pp_odecl ~nonum o) od

let pp_gcmd ~nonum fmt gc = match gc with
  | GLet(vs,e) ->
    F.fprintf fmt "@[<hov 2>let %a =@ %a@]" (pp_binder ~qual:Unqual) [vs] pp_expr e
  | GMSet(ms,ek,e) when is_Unit ek ->
    F.fprintf fmt "@[<hov 2>%a :=@ %a@]"
      MapSym.pp ms pp_expr e
  | GMSet(ms,ek,e) ->
    F.fprintf fmt "@[<hov 2>%a[%a] :=@ %a@]" MapSym.pp ms pp_expr ek pp_expr e
  | GAssert(e) ->
    F.fprintf fmt "@[<hov 2>assert(%a)@]" pp_expr e
  | GSamp(v,d) ->
    F.fprintf fmt "@[<hov 2>%a <-$@ %a@]"
      (pp_binder ~qual:Unqual) [v]
      (pp_distr ~qual:Unqual) d
  | GCall(vs,asym,e,[]) ->
    F.fprintf fmt "@[<hov 2>%a <-@ %a(@[%a@])@]"
      (pp_binder ~qual:Unqual) vs AdvSym.pp asym pp_expr_tnp e
  | GCall(vs,asym,e,od) ->
    F.fprintf fmt "@[<hov 2>%a <-@ %a(@[%a@]) with@\n%a@]"
      (pp_binder ~qual:Unqual) vs AdvSym.pp asym
      pp_expr_tnp e
      (pp_list ",@;" (pp_odef ~nonum)) od

let pp_igcmd fmt (i,gc) =
  F.fprintf fmt "@[%3i: %a@]" i (pp_gcmd ~nonum:false) gc

let pp_gdef ~nonum fmt gd =
  if nonum then
    pp_list ";@ " (pp_gcmd ~nonum) fmt gd
  else
    pp_list ";@ " pp_igcmd fmt (num_list gd)

let pp_se fmt se =
  F.fprintf fmt "@[<v 0>%a;@,: %a@]" (pp_gdef ~nonum:false) se.se_gdef
    pp_expr se.se_ev

let pp_se_nonum fmt se =
  F.fprintf fmt "@[<v 0>%a;@,: %a@]" (pp_gdef ~nonum:true) se.se_gdef
    pp_expr se.se_ev

let pp_ps fmt ps =
  let se_idxs =
    let i = ref 0 in L.map (fun ps -> incr i; (!i, ps)) ps
  in
  let pp_se_idx fmt (i,se) = F.fprintf fmt "@[%i.@[ %a @]@]" i pp_se se in
  F.fprintf fmt "%a\n--------------------\n\n"
    (pp_list "\n\n" pp_se_idx) se_idxs

(* ** Positions and replacement functions
 * ----------------------------------------------------------------------- *)

type gcmd_pos = int with compare

type oh_pos = (int * int) with compare

type ocmd_pos = (int * int * int * otype) with compare

type ocmd_pos_eq = (int * int * int) with compare

let get_se_gcmd se p = L.nth se.se_gdef p

type se_ctxt = {
  sec_left  : gdef;
  sec_right : gdef;
  sec_ev    : expr
}

let get_se_ctxt_len se ~pos ~len =
  let rhd,tl =  cut_n pos se.se_gdef in
  let cmds, cright = cut_n len tl in
  L.rev cmds, { sec_left = rhd; sec_right = cright; sec_ev = se.se_ev}

let get_se_ctxt se pos =
  match get_se_ctxt_len se ~pos ~len:1 with
  | [cmd], ctxt ->
    cmd, ctxt
  | _ -> assert false

let set_se_ctxt cmds {sec_left; sec_right; sec_ev} =
  { se_gdef = L.rev_append sec_left (cmds @ sec_right);
    se_ev   = sec_ev }

let set_se_gcmd se pos cmds =
  assert (pos >= 0 && pos < L.length se.se_gdef);
  let _, ctxt = get_se_ctxt se pos in
  set_se_ctxt cmds ctxt

let get_obody od otype =
  match otype, od with
  | Onothyb,          Oreg ob -> ob
  | Oishyb OHless,    Ohyb oh -> oh.oh_less
  | Oishyb OHeq,      Ohyb oh -> oh.oh_eq
  | Oishyb OHgreater, Ohyb oh -> oh.oh_greater
  | _ -> assert false

let get_se_lcmd se (i,j,k,otype) =
  match get_se_gcmd se i with
  | GCall(_,_,_,ods) ->
    let (o,vs,od,c) = L.nth ods j in
    let (ms,e) = get_obody od otype in
    o,vs,split_n k ms, e, c
  | _ -> assert false

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
  seoc_sec       : se_ctxt
}

let get_se_octxt_len se (i,j,k,ootype) len =
  match get_se_ctxt se i with
  | GCall(vsa,asym,e,os), sec ->
    let rohd, (o,vs,od,c), otl = split_n j os in
    let (ms,oe) = get_obody od ootype in
    let rhd, tl = cut_n (min k (List.length ms)) ms in
    let cmds,cright = cut_n len tl in
    let obless = match ootype with
      | Oishyb (OHeq |  OHgreater) -> Some (get_obody od (Oishyb OHless))
      | _ -> None
    in
    let obeq = match ootype with
      | Oishyb (OHless | OHgreater) -> Some (get_obody od (Oishyb OHeq))
      | _ -> None
    in
    let obgreater = match ootype with
      | Oishyb (OHless | OHeq) -> Some (get_obody od (Oishyb OHgreater))
      | _ -> None
    in
    let ctx =
      { seoc_asym      = asym;
        seoc_avars     = vsa;
        seoc_aarg      = e;
        seoc_oright    = rohd;
        seoc_oleft     = otl;
        seoc_obless    = obless;
        seoc_obeq      = obeq;
        seoc_obgreater = obgreater;
        seoc_osym      = o;
        seoc_oargs     = vs;
        seoc_ocounter  = c;
        seoc_return    = oe;
        seoc_cleft     = rhd;
        seoc_cright    = cright;
        seoc_sec       = sec }
    in
    L.rev cmds, ctx
  | i, _ -> 
    Format.eprintf "get_se_octxt_len: %a"
                   (pp_gcmd ~nonum:true) i;
    assert false

let set_se_octxt lcmds c =
  let ms = L.rev_append c.seoc_cleft (lcmds@c.seoc_cright) in
  let ob = (ms,c.seoc_return) in
  let odecl =
    match c.seoc_obless, c.seoc_obeq,  c.seoc_obgreater with
    | None,    None,     None   -> Oreg ob
    | None,    Some oe, Some og -> Ohyb { oh_less = ob; oh_eq = oe; oh_greater = og }
    | Some ol, None,    Some og -> Ohyb { oh_less = ol; oh_eq = ob; oh_greater = og }
    | Some ol, Some oe, None    -> Ohyb { oh_less = ol; oh_eq = oe; oh_greater = ob }
    | _ -> assert false
  in
  let odef = (c.seoc_osym,c.seoc_oargs,odecl,c.seoc_ocounter) in
  let os = L.rev_append c.seoc_oleft (odef :: c.seoc_oright) in
  let i = [GCall(c.seoc_avars, c.seoc_asym, c.seoc_aarg, os)] in
  set_se_ctxt i c.seoc_sec

let get_se_octxt se p =
  match get_se_octxt_len se p 1 with
  | [cmd], ctxt -> cmd, ctxt
  | _           -> assert false

let set_se_lcmd se p cmds =
  let _, ctxt = get_se_octxt se p in
  set_se_octxt cmds ctxt

(* ** Read and write variables
 * ----------------------------------------------------------------------- *)

(* *** General purpose functions. *)

let fold_union f es =
  L.fold_left (fun s e -> Se.union s (f e)) Se.empty es

let add_binding xs =
  fold_union (fun x -> Se.singleton (mk_V x)) xs

(* *** Distributions. *)

let read_distr (_,es) = fold_union e_vars es

(* *** Oracle definitions. *)

let read_lcmd = function
  | LLet(_,e) | LGuard e -> e_vars e
  | LMSet(_,ek,e)        -> Se.union (e_vars ek) (e_vars e)
  | LBind _              -> Se.empty
  | LSamp(_,d)           -> read_distr d

let read_lcmds c = fold_union read_lcmd c

let write_lcmd = function
  | LLet(x,_) | LSamp(x,_) -> Se.singleton (mk_V x)
  | LMSet(_,_,_)           -> Se.empty
  | LBind (xs,_)           -> add_binding xs
  | LGuard _               -> Se.empty

let write_lcmds c = fold_union write_lcmd c

let read_obody xs (lcmd,e) =
  let r = Se.union (read_lcmds lcmd) (e_vars e) in
  let w = Se.union (add_binding xs) (write_lcmds lcmd) in
  Se.diff r w

let read_ohybrid xs oh =
  Se.union (read_obody xs oh.oh_less)
    (Se.union (read_obody xs oh.oh_eq) (read_obody xs oh.oh_greater))

let read_odecl xs = function
  | Oreg od -> read_obody xs od
  | Ohyb oh -> read_ohybrid xs oh

(** We assume oracles do not overshadow variables from main. *)
let read_odef (_,xs,odecl,_) =
  read_odecl xs odecl

let read_odefs odefs = fold_union read_odef odefs

(* *** Main body. *)

let read_gcmd = function
  | GLet(_,e)          -> e_vars e
  | GMSet(_,ek,e)        -> Se.union (e_vars ek) (e_vars e)
  | GAssert(e)         -> e_vars e
  | GSamp(_,d)         -> read_distr d
  | GCall(_,_,e,odefs) -> Se.union (e_vars e) (read_odefs odefs)

let read_gcmds c = fold_union read_gcmd c

let write_gcmd = function
  | GLet (x,_) | GSamp (x,_) -> Se.singleton (mk_V x)
  | GMSet(_,_,_)             -> Se.empty
  | GAssert(_)               -> Se.empty
  | GCall (xs,_,_,_)         -> add_binding xs

let write_gcmds c = fold_union write_gcmd c

let asym_gcmd = function
  | GCall(_,asym,_,_) -> Some asym
  | _                 -> None

let asym_gcmds gcmds =
  L.map asym_gcmd gcmds |> cat_Some

(* *** Security experiments *)

let read_se se = Se.union (read_gcmds se.se_gdef) (e_vars se.se_ev)

(* ** Find expressions that satisfy predicate
 * ----------------------------------------------------------------------- *)

let fold_union_e f xs =
  L.fold_right Se.union (L.map f xs) Se.empty

let find_expr p e = e_find_all p e

let find_exprs p es = fold_union_e (find_expr p) es

let find_lcmd p = function
  | LLet(_,e)     -> find_expr p e
  | LMSet(_,ek,e) -> Se.union (find_expr p ek) (find_expr p e)
  | LSamp(_,d)    -> find_exprs p (snd d)
  | LBind(_,_)    -> Se.empty
  | LGuard(e)     -> find_expr p e

let find_lcmds p c = fold_union_e (find_lcmd p) c

let find_obody p (cmd,e) =
  Se.union (find_expr p e) (find_lcmds p cmd)

let find_ohybrid p oh =
  Se.union (find_obody p oh.oh_less)
    (Se.union (find_obody p oh.oh_eq) (find_obody p oh.oh_greater))

let find_odecl p = function
  | Oreg od -> find_obody p od
  | Ohyb oh -> find_ohybrid p oh

let find_oh p (_,_,odecl,_) = find_odecl p odecl

let find_all_gcmd p = function
  | GLet(_,e)     -> find_expr p e
  | GMSet(_,ek,e) -> Se.union (find_expr p ek) (find_expr p e)
  | GAssert(e)    -> find_expr p e
  | GSamp(_,d)    -> find_exprs p (snd d)
  | GCall(_,_,e,odefs) ->
    Se.add e (fold_union_e (find_oh p) odefs)

let find_all_gdef p gdef =
  fold_union_e (find_all_gcmd p) gdef

let find_global_ohybrid p oh =
  find_obody p oh.oh_eq

let find_global_oh p (_,_,odecl,_) =
  match odecl with
  | Oreg _  -> Se.empty
  | Ohyb oh -> find_global_ohybrid p oh

let find_global_gcmd p = function
  | GLet(_,e)     -> find_expr p e
  | GAssert(e)    -> find_expr p e
  | GMSet(_,ek,e) -> Se.union (find_expr p ek) (find_expr p e)
  | GSamp(_,d)    -> find_exprs p (snd d)
  | GCall(_,_,e,odefs) ->
    Se.add e (fold_union_e (find_global_oh p) odefs)

let find_global_gdef p gdef = fold_union_e (find_global_gcmd p) gdef

(* ** Random oracle symbol occurences in RO calls
 * ----------------------------------------------------------------------- *)

let ro_syms_of_es es =
  Se.fold (fun e s -> RoSym.S.add (fst (destr_RoCall e)) s) es RoSym.S.empty

let ro_syms_expr e = ro_syms_of_es (find_expr is_RoCall e)

let ro_syms_all_gcmd gcmd = ro_syms_of_es (find_all_gcmd is_RoCall gcmd)

let ro_syms_all_gdef gdef = ro_syms_of_es (find_all_gdef is_RoCall gdef)

let ro_syms_global_gdef gdef = ro_syms_of_es (find_global_gdef is_RoCall gdef)

(* ** Random oracle arguments for given RO symbol
 * ----------------------------------------------------------------------- *)

let harg_of_es es =
  Se.fold (fun e s ->
           if is_RoCall e then Se.add (snd (destr_RoCall e)) s
           else s) es Se.empty

let is_H_call h e = is_RoCall e && RoSym.equal h (fst (destr_RoCall e))

let hash_args_expr h e = harg_of_es (find_expr (is_H_call h) e)

let hash_args_all_gcmd h gcmd = harg_of_es (find_all_gcmd (is_H_call h) gcmd)

let hash_args_all_gdef h gdef = harg_of_es (find_all_gdef (is_H_call h) gdef)

let hash_args_global_gdef h gdef = harg_of_es (find_global_gdef (is_H_call h) gdef)

(* ** Variable occurences
 * ----------------------------------------------------------------------- *)

let fold_union_vs f xs =
  L.fold_right VarSym.S.union (L.map f xs) VarSym.S.empty

let set_of_list vs = L.fold_right VarSym.S.add vs VarSym.S.empty

let vars_expr e =
  Se.fold (fun e s -> VarSym.S.add (destr_V e) s) (e_vars e) VarSym.S.empty

let vars_exprs es = fold_union_vs vars_expr es

let vars_lcmd = function
  | LLet(v,e)     -> VarSym.S.add v (vars_expr e)
  | LMSet(_,ek,e) -> VarSym.S.union (vars_expr ek) (vars_expr e)
  | LSamp(v,d)    -> VarSym.S.add v (vars_exprs (snd d))
  | LBind(vs,_)   -> set_of_list vs
  | LGuard(e)     -> vars_expr e

let vars_lcmds c = fold_union_vs vars_lcmd c

let vars_obody (cmd,e) =
  (VarSym.S.union (vars_expr e) (vars_lcmds cmd))

let vars_ohybrid oh =
  VarSym.S.union (vars_obody oh.oh_less)
    (VarSym.S.union (vars_obody oh.oh_eq) (vars_obody oh.oh_greater))

let vars_odecl od =
  match od with
  | Oreg od -> vars_obody od
  | Ohyb oh -> vars_ohybrid oh

let vars_oh (_,vs,odecl,_) =
  VarSym.S.union (set_of_list vs) (vars_odecl odecl)

let vars_all_gcmd = function
  | GLet(v,e)     -> VarSym.S.add v (vars_expr e)
  | GMSet(_,ek,e) -> VarSym.S.union (vars_expr ek) (vars_expr e)
  | GAssert(e)    -> vars_expr e
  | GSamp(v,d)    -> VarSym.S.add v (vars_exprs (snd d))
  | GCall(vs,_,e,odefs) ->
    VarSym.S.union
      (fold_union_vs vars_oh odefs)
      (VarSym.S.union (vars_expr e) (set_of_list vs))

let vars_all_gdef gdef = fold_union_vs vars_all_gcmd gdef

let vars_obody (cmd,e) =
  (VarSym.S.union (vars_expr e) (vars_lcmds cmd))

let vars_global_ohybrid oh =
  (vars_obody oh.oh_eq)

let vars_global_oh (_,vs,odecl,_) =
  match odecl with
  | Oreg _  -> VarSym.S.empty
  | Ohyb oh -> VarSym.S.union (set_of_list vs) (vars_global_ohybrid oh)

let vars_global_gcmd = function
  | GLet(v,e)     -> VarSym.S.add v (vars_expr e)
  | GMSet(_,ek,e) -> VarSym.S.union (vars_expr ek) (vars_expr e)
  | GAssert(e)    -> vars_expr e
  | GSamp(v,d)    -> VarSym.S.add v (vars_exprs (snd d))
  | GCall(vs,_,e,odefs) ->
    VarSym.S.union
      (fold_union_vs vars_global_oh odefs)
      (VarSym.S.union (vars_expr e) (set_of_list vs))

let vars_global_gdef gdef = fold_union_vs vars_global_gcmd gdef

(* ** Variable renaming
 * ----------------------------------------------------------------------- *)

let subst_v_expr tov =
  let aux e =
    match e.e_node with
    | V v -> mk_V (tov v)
    | _   -> raise Not_found
  in
  e_map_top aux

let subst_v_lcmd tov = function
  | LLet (v, e)      -> LLet(tov v, subst_v_expr tov e)
  | LMSet (m, ek, e) -> LMSet(m, subst_v_expr tov ek, subst_v_expr tov e)
  | LBind (vs,lh)    -> LBind (L.map tov vs, lh)
  | LSamp(v,d)       -> LSamp(tov v, map_distr_exp (subst_v_expr tov) d)
  | LGuard e         -> LGuard (subst_v_expr tov e)

let subst_v_obody tov (lc,e) =
  let lc = L.map (subst_v_lcmd tov) lc in
  let e = subst_v_expr tov e in
  (lc, e)

let subst_v_odecl tov = function
  | Oreg ob -> Oreg (subst_v_obody tov ob)
  | Ohyb oh -> Ohyb (map_ohybrid (subst_v_obody tov) oh)

let subst_v_odef tov (o,vs,od,c) =
  let vs = L.map tov vs in
  let od = subst_v_odecl tov od in
  (o, vs, od, c)

let subst_v_gcmd tov = function
  | GLet(v,e)        -> GLet(tov v, subst_v_expr tov e)
  | GAssert(e)       -> GAssert(subst_v_expr tov e)
  | GMSet (m, ek, e) -> GMSet(m, subst_v_expr tov ek, subst_v_expr tov e)
  | GSamp(v, d)      -> GSamp(tov v, map_distr_exp (subst_v_expr tov) d)
  | GCall(vs, asym, e, odefs) ->
    GCall(L.map tov vs, asym, subst_v_expr tov e,
          L.map (subst_v_odef tov) odefs)

let subst_v_gdef tov = L.map (subst_v_gcmd tov)

let subst_v_ev tov = subst_v_expr tov

let subst_v_se tov se = {
  se_gdef = subst_v_gdef tov se.se_gdef;
  se_ev   = subst_v_ev tov se.se_ev;
}

type renaming = vs VarSym.M.t

let id_renaming = VarSym.M.empty

let ren_injective sigma =
  try
    let inv = VarSym.H.create 134 in
    VarSym.M.iter
      (fun _ v' ->
        if VarSym.H.mem inv v'
        then raise Not_found
        else VarSym.H.add inv v' ())
      sigma;
    true
  with
    Not_found ->
      false

let pp_ren fmt ren =
  pp_list "," (pp_pair VarSym.pp VarSym.pp) fmt (VarSym.M.bindings ren)

(* ** Unification
 * ----------------------------------------------------------------------- *)

let ensure_same_length l1 l2 =
  if L.length l1 <> L.length l2 then raise Not_found

let unif_vs ren v1 v2 =
  if not (VarSym.equal v1 v2) then
    VarSym.H.add ren v1 v2

(* FIXME: pretty incomplete *)
let unif_expr ren e1 e2 =
  match e1.e_node, e2.e_node with
  | Quant(_,(binders1,_),_), Quant(_,(binders2,_),_) ->
    ensure_same_length binders1 binders2;
    L.iter2 (unif_vs ren) binders1 binders2
  | _ -> ()

let unif_lcmd ren lc1 lc2 =
  match lc1,lc2 with
  | LLet(v1,_), LLet(v2,_)
  | LSamp(v1,_), LSamp(v2,_) ->
    unif_vs ren v1 v2
  | LBind(vss1,_), LBind(vss2,_) ->
    ensure_same_length vss1 vss2;
    L.iter2 (unif_vs ren) vss1 vss2
  | LGuard(_), LGuard(_)
  | LMSet(_,_,_), LMSet(_,_,_) ->
    ()
  | _ ->
    raise Not_found

let unif_obody ren (lcmds1,_) (lcmds2,_) =
  ensure_same_length lcmds1 lcmds2;
  L.iter2 (unif_lcmd ren) lcmds1 lcmds2

let unif_odecl ren odecl1 odecl2 =
  match odecl1, odecl2 with
  | Oreg ob1,    Oreg ob2 -> unif_obody ren ob1 ob2
  | Ohyb oh1, Ohyb oh2 ->
    unif_obody ren oh1.oh_less    oh2.oh_less;
    unif_obody ren oh1.oh_eq      oh2.oh_eq;
    unif_obody ren oh1.oh_greater oh2.oh_greater
  | _, _ -> raise Not_found

let unif_odef ren (_,vs1,od1,_) (_,vs2,od2,_) =
  ensure_same_length vs1 vs2;
  L.iter2 (unif_vs ren) vs1 vs2;
  unif_odecl ren od1 od2

let unif_gcmd ren gcmd1 gcmd2 =
  match gcmd1, gcmd2 with
  | GLet(v1,_), GLet(v2,_)
  | GSamp(v1,_), GSamp(v2,_) -> unif_vs ren v1 v2
  | GMSet(_,_,_), GMSet(_,_,_)
  | GAssert(_), GAssert(_) -> ()
  | GCall(vs1,_,_,odefs1), GCall(vs2,_,_,odefs2) ->
    ensure_same_length vs1 vs2;
    ensure_same_length odefs1 odefs2;
    L.iter2 (unif_vs ren) vs1 vs2;
    L.iter2 (unif_odef ren) odefs1 odefs2
  | _ -> raise Not_found

let unif_gdef ren gd1 gd2 =
  ensure_same_length gd1 gd2;
  L.iter2 (unif_gcmd ren) gd1 gd2

let vht_to_map ht =
  VarSym.H.fold (fun v x m -> VarSym.M.add v x m) ht VarSym.M.empty

(** We only support an outermost exists binder *)
let unif_se se1 se2 =
  try
    let ren = VarSym.H.create 134 in
    unif_gdef ren se1.se_gdef se2.se_gdef;
    unif_expr ren se1.se_ev se2.se_ev;
    vht_to_map ren
  with
    Not_found ->
      F.printf "no unifier found!\n%!";
      raise Not_found

let unif_gdef g1 g2 =
  let ren = VarSym.H.create 134 in
  unif_gdef ren g1 g2;
  vht_to_map ren

(* ** Probabilistic polynomial time
 * ----------------------------------------------------------------------- *)

let has_log_distr (_,es) = L.exists has_log es

let has_log_lcmd = function
  | LLet(_,e) | LGuard e -> has_log e
  | LMSet(_,ek,e)        -> has_log ek || has_log e
  | LBind _              -> false
  | LSamp(_,d)           -> has_log_distr d

let has_log_lcmds c = L.exists has_log_lcmd c

let has_log_obody (cmd,e) = has_log e || has_log_lcmds cmd

let has_log_odecl od =
  match od with
  | Oreg od -> has_log_obody od
  | Ohyb oh -> L.exists has_log_obody [ oh.oh_less; oh.oh_eq; oh.oh_greater ]

let has_log_odef (_,_,od,_) = has_log_odecl od

let has_log_gcmd = function
  | GLet(_,e) | GAssert(e) -> has_log e
  | GMSet(_,ek,e)          -> has_log ek || has_log e
  | GSamp(_,d)             -> has_log_distr d
  | GCall(_,_,e,ods)       -> has_log e || L.exists has_log_odef ods

let has_log_gcmds c = L.exists has_log_gcmd c

let is_ppt_distr (_,es) = L.for_all is_ppt es

let is_ppt_lcmd = function
  | LLet(_,e) | LGuard e -> is_ppt e
  | LMSet(_,ek,e)        -> is_ppt ek || is_ppt e
  | LBind _              -> true
  | LSamp(_,d)           -> is_ppt_distr d

let is_ppt_lcmds c = L.for_all is_ppt_lcmd c

let is_ppt_obody (cmd,e) = is_ppt e && is_ppt_lcmds cmd

let is_ppt_odecl od =
  match od with
  | Oreg ob -> is_ppt_obody ob
  | Ohyb oh -> L.exists is_ppt_obody [ oh.oh_less; oh.oh_eq; oh.oh_greater ]

let is_ppt_odef (_,_,od,_) = is_ppt_odecl od

let is_ppt_gcmd = function
  | GLet(_,e) | GAssert(e) -> is_ppt e
  | GMSet(_,ek,e)          -> is_ppt ek || is_ppt e
  | GSamp(_,d)             -> is_ppt_distr d
  | GCall(_,_,e,od)        -> is_ppt e || L.for_all is_ppt_odef od

let is_ppt_gcmds c = L.for_all is_ppt_gcmd c

let is_ppt_se se = is_ppt_gcmds se.se_gdef && is_ppt se.se_ev

(* ** Normal forms
 * ----------------------------------------------------------------------- *)

let norm_default = Norm.norm_expr_strong

let norm_distr ?norm:(nf=norm_default) s (ty,es) =
  (ty, L.map (fun e -> nf (e_subst s e)) es)

let norm_obody ?norm:(nf=norm_default) s exported_defs (lc,e) =
  let do_export, add_export =
    match exported_defs with
    | None -> false, fun _ _ -> ()
    | Some map_r -> true, fun v e -> map_r := Me.add v e !map_r
  in
  let rec aux s rc ~do_export lc =
    match lc with
    | [] -> (L.rev rc, nf (e_subst s e))
    | LLet (v, e) :: lc' ->
      let e = nf (e_subst s e) in
      let v = mk_V v in
      let s = Me.add v e s in
      add_export v e;
      aux s rc ~do_export lc'
    | (LBind (vs,_) as i)::lc' ->
      let s = L.fold_left (fun s v -> Me.remove (mk_V v) s) s vs in
      aux s (i::rc) ~do_export:false lc'
    | LMSet(m,ek,e) :: lc' ->
      let ek = nf (e_subst s ek) in
      let e  = nf (e_subst s e)  in
      aux s (LMSet(m,ek,e)::rc) ~do_export lc'
    | LSamp(v,d) :: lc' ->
      let d = norm_distr ~norm:nf s d in
      let s = Me.remove (mk_V v) s in
      aux s (LSamp(v,d)::rc) ~do_export lc'
    | LGuard e :: lc' ->
      aux s (LGuard (nf (e_subst s e)) :: rc) ~do_export:false lc' in
  aux s [] ~do_export lc

let norm_odef ?norm:(nf=norm_default) s exported_defs (o,vs,od,c) =
  let od =
    match od with
    | Oreg ob -> Oreg (norm_obody ~norm:nf s None ob)
    | Ohyb oh ->
      Ohyb
        { oh_less    = norm_obody ~norm:nf s None          oh.oh_less;
          oh_eq      = norm_obody ~norm:nf s exported_defs oh.oh_eq;
          oh_greater = norm_obody ~norm:nf s None          oh.oh_greater }
  in
  (o,vs,od,c)

let norm_gdef ?norm:(nf=norm_default) g =
  let rec aux s rc lc =
    match lc with
    | [] -> L.rev rc, s
    | GLet(v,e) :: lc' ->
      let e = nf (e_subst s e) in
      let v = mk_V v in
      let s = Me.add v e s in
      aux s rc lc'
    | GMSet(m,ek,e) :: lc' ->
      let ek = nf (e_subst s ek) in
      let e  = nf (e_subst s e)  in
      aux s (GMSet(m,ek,e) :: rc) lc'
    | GAssert(e) :: lc' ->
      let e = nf (e_subst s e) in
      aux s (GAssert(e) :: rc) lc'
    | GSamp(v, d) :: lc' ->
      let d = norm_distr ~norm:nf s d in
      let s = Me.remove (mk_V v) s in
      aux s (GSamp(v,d) :: rc) lc'
    | GCall(vs, asym, e, odefs) :: lc'->
      let e = nf (e_subst s e) in
      let exported_defs = ref Me.empty in
      let odefs = L.map (norm_odef ~norm:nf s (Some exported_defs)) odefs in
      let s = Me.fold (fun k v s -> Me.add k v s) !exported_defs s in
      let s = L.fold_left (fun s v -> Me.remove (mk_V v) s) s vs in
      aux s (GCall(vs, asym, e, odefs)::rc) lc'
  in
  aux Me.empty [] g

let norm_se ?norm:(nf=norm_default) se =
  let g,s = norm_gdef ~norm:nf se.se_gdef in
  { se_gdef = g;
    se_ev   = nf (e_subst s se.se_ev) }



(* ** finite maps transformations
 * ----------------------------------------------------------------------- *)

let map_expr_finmap ~f_lookup ~f_in_dom =
  let aux e =
    match e.e_node with
    | App(MapIndom(ms),[ek])  -> f_in_dom ms ek
    | App(MapLookup(ms),[ek]) -> f_lookup ms ek
    | _   -> raise Not_found
  in
  e_map_top aux

let map_lcmd_finmap ~f_lookup ~f_in_dom ~f_LMSet lcmd =
  let mef = map_expr_finmap ~f_lookup ~f_in_dom in
  match lcmd with
  | LLet (v, e)      -> [LLet(v, mef e)]
  | LMSet (m, ek, e) -> f_LMSet m (mef ek) (mef e)
  | LBind (vs,lh)    -> [LBind (vs, lh)]
  | LSamp(v,d)       -> [LSamp(v, map_distr_exp mef d)]
  | LGuard e         -> [LGuard (mef e)]

let map_obody_finmap ~f_lookup ~f_in_dom ~f_LMSet (lc,e)=
  let e = map_expr_finmap ~f_lookup ~f_in_dom e in
  let lc = L.concat (L.map (map_lcmd_finmap ~f_lookup ~f_in_dom ~f_LMSet) lc) in
  (lc, e)

let map_odecl_finmap ~f_lookup ~f_in_dom ~f_LMSet od =
  let mob = map_obody_finmap ~f_lookup ~f_in_dom ~f_LMSet in
  match od with
  | Oreg ob -> Oreg (mob ob)
  | Ohyb oh -> Ohyb (map_ohybrid mob oh)

let map_odef_finmap ~f_lookup ~f_in_dom ~f_LMSet (o,vs,od,c) =
  let od = map_odecl_finmap ~f_lookup ~f_in_dom ~f_LMSet od in
  (o, vs, od, c)

let map_gcmd_finmap ~f_lookup ~f_in_dom ~f_LMSet ~f_GMSet gcmd =
  let mef = map_expr_finmap ~f_lookup ~f_in_dom in
  match gcmd with 
  | GLet(v,e)        -> [GLet(v, mef e)]
  | GAssert(e)       -> [GAssert(mef e)]
  | GMSet (m, ek, e) -> f_GMSet m (mef ek) (mef e)
  | GSamp(v, d)      -> [GSamp(v, map_distr_exp mef d)]
  | GCall(vs, asym, e, odefs) ->
    [GCall(vs, asym, mef e,
           L.map (map_odef_finmap ~f_lookup ~f_in_dom ~f_LMSet) odefs)]

let map_gdef_finmap ~f_lookup ~f_in_dom ~f_LMSet ~f_GMSet gcmds =
  L.concat (L.map (map_gcmd_finmap ~f_lookup ~f_in_dom ~f_GMSet ~f_LMSet) gcmds)

let map_se_finmap ~f_lookup ~f_in_dom ~f_LMSet ~f_GMSet se = {
  se_gdef = map_gdef_finmap ~f_lookup ~f_in_dom ~f_GMSet ~f_LMSet se.se_gdef;
  se_ev   = map_expr_finmap ~f_lookup ~f_in_dom se.se_ev;
}


(* -------------------------------------------------------------------- *)
let sv_of_se se = 
  Se.fold (fun e s ->
      match e.e_node with
      | V v -> VarSym.S.add v s
      | _   -> assert false) se VarSym.S.empty 

let game_vars g = 
  let addv se v = Se.add (mk_V v) se in
  let addc se c = 
    match c with 
    | GLet(x, _) -> addv se x
    | GMSet(_x,_,_) -> (* addv se x *) se
    | GAssert _ -> se
    | GSamp(x,_) -> addv se x
    | GCall(xs,_,_,os) ->
      let se = List.fold_left addv se xs in
      let addo se (_,vs,od,_) = 
        let se =  List.fold_left addv se vs in
        match od with
        | Oreg (lc,_) -> Se.union se (write_lcmds lc)
        | Ohyb {oh_less = (lc1,_); oh_eq = (lc2,_); oh_greater = (lc3,_)} ->
          Se.union (Se.union se (write_lcmds lc1))
                   (Se.union (write_lcmds lc2) (write_lcmds lc3)) in
      List.fold_left addo se os in
  let se = List.fold_left addc Se.empty g in
  sv_of_se se 
