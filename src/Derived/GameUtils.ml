(* * Utility functions for cryptographic game definitions *)

(* ** Imports *)
open Abbrevs
open Util
open Expr
open ExprUtils
open Syms
open Game
open Type
open NormUtils

(* ** Iterate with context
 * ----------------------------------------------------------------------- *)

type iter_pos =
  | InEv
  | InMain       of gcmd_pos
  | InOrclReturn of ocmd_pos * ty * ty
  | InOrcl       of ocmd_pos * ty * ty
    (* position, adversary argument type, oracle type *)

let pp_iter_pos fmt ip =
  match ip with
  | InEv                                  -> F.fprintf fmt "inEv"
  | InMain(i)                             -> F.fprintf fmt "inMain(%i)" i
  | InOrcl((gpos,o_idx,opos,otype),_,_)  ->
    F.fprintf fmt "inOrcl(%i,%i,%i,%a)" gpos o_idx opos pp_otype otype
  | InOrclReturn((gpos,o_idx,_,_),_,_) -> F.fprintf fmt "inOreturn(%i,%i)" gpos o_idx

type iter_ctx = {
  ic_pos     : iter_pos;
  ic_isZero  : expr list;
  ic_nonZero : expr list
}

let empty_iter_ctx pos = {
  ic_pos     = pos;
  ic_isZero  = [];
  ic_nonZero = []
}

let pp_iter_ctx fmt ic =
  F.fprintf fmt "pos: %a, isZero: %a, nonZero: %a"
    pp_iter_pos ic.ic_pos
    (pp_list " /\\ " (pp_around "" " = 0" pp_expr)) ic.ic_isZero
    (pp_list " /\\ " (pp_around "" " <> 0" pp_expr)) ic.ic_nonZero

let iter_ctx_obody_exp argtype gpos o_idx nz ?iexc:(iexc=false) f o ootype (ms,e) =
  let tests = ref 0 in
  let nonZero = ref nz in
  let isZero  = ref [] in
  let go _lcmd_idx lcmd =
    let ctx = { (empty_iter_ctx (InOrcl((gpos,o_idx,!tests,ootype),argtype,o.OrclSym.dom)))
                  with ic_nonZero = !nonZero; ic_isZero = !isZero }
    in
    match lcmd with
    | LLet(_,e) ->
      f ctx e
    | LMSet(_,ek,e) ->
      f ctx ek; f ctx e
    | LBind(_) ->
      ()
    | LSamp(v,(_,es)) ->
      if iexc then L.iter (f ctx) es;
      let ve = mk_V v in
      let neqs = L.map (fun e -> destr_Eq_norm (mk_Eq ve e)) es in
      nonZero := cat_Some neqs @ !nonZero
    | LGuard(e)  ->
      incr tests;
      f ctx e;
      isZero := (cat_Some (L.map destr_Eq_norm [e])) @ !isZero;
      nonZero := (cat_Some (L.map destr_Eq_norm [e])) @ !nonZero
  in
  L.iteri go ms;
  let ctx = { ic_pos = InOrclReturn((gpos,o_idx,!tests,ootype),argtype,o.OrclSym.dom);
              ic_nonZero = !nonZero; ic_isZero = !isZero }
  in
  f ctx e

let iter_ctx_odecl_exp argtype gpos o_idx nz ?iexc:(iexc=false) f os od =
  match od with
  | Oreg ob -> iter_ctx_obody_exp argtype gpos o_idx nz ~iexc f os Onothyb ob
  | Ohyb oh ->
    iter_ctx_obody_exp argtype gpos o_idx nz ~iexc f os (Oishyb OHless) oh.oh_less;
    iter_ctx_obody_exp argtype gpos o_idx nz ~iexc f os (Oishyb OHeq) oh.oh_eq;
    iter_ctx_obody_exp argtype gpos o_idx nz ~iexc f os (Oishyb OHgreater) oh.oh_greater

let iter_ctx_oh_exp argtype gpos o_idx nz ?iexc:(iexc=false) f (os,_vs,od,_c) =
  iter_ctx_odecl_exp argtype gpos o_idx nz ~iexc f os od

let iter_ctx_gdef_exp ?iexc:(iexc=false) f gdef =
  let nonZero = ref [] in
  let go pos gcmd =
    let ctx = { ic_pos = InMain(pos); ic_isZero = []; ic_nonZero = !nonZero } in
    match gcmd with
    | GLet(_,e) ->
      f ctx e
    | GMSet(_,ek,e) ->
      f ctx ek; f ctx e
    | GAssert(e) ->
      f ctx e
    | GCall(_,_,e,ods) ->
      f ctx e;
      L.iteri
        (fun oi -> iter_ctx_oh_exp e.e_ty pos oi !nonZero ~iexc f)
        ods
    | GSamp(v,(_,es)) ->
      if iexc then L.iter (f ctx) es;
      let ve = mk_V v in
      let neqs = L.map (fun e -> destr_Eq_norm (mk_Eq ve e)) es in
      nonZero := cat_Some neqs @ !nonZero
  in
  L.iteri go gdef;
  !nonZero

let iter_ctx_se_exp ?iexc:(iexc=false) f se =
  let nz = iter_ctx_gdef_exp ~iexc f se.se_gdef in
  let main_expr = se.se_ev in
  if is_Land main_expr then (
    let conjs = destr_Land main_expr  in
    let (ineqs,eqs) = L.partition is_Not conjs in
    let nonZero = ref nz in
    let _ctx = { ic_pos = InEv; ic_isZero = []; ic_nonZero = nz } in
    let iter_ineq ineq =
      (* f ctx ineq; *) (* FIXME: useless for the case we are interested in *)
      match destr_Neq_norm ineq with
      | Some e ->
        nonZero := e :: !nonZero
      | None -> ()
    in
    L.iter iter_ineq ineqs;
    let ctx = { ic_pos = InEv; ic_isZero = []; ic_nonZero = !nonZero } in
    L.iter (f ctx) eqs
  ) else (
    let ctx = { ic_pos = InEv; ic_isZero = []; ic_nonZero = nz } in
    f ctx main_expr
  )

(* ** Mappings from strings to variables
 * ----------------------------------------------------------------------- *)

type vmap = (string qual * string,VarSym.t) Hashtbl.t

let create_vmap sv = 
  let addv mvar v = 
    let q = map_qual OrclSym.to_string v.VarSym.qual in
    let x = Id.name v.VarSym.id in
    Hashtbl.add mvar (q,x) v in
  let avars = Hashtbl.create 10 in
  VarSym.S.iter (addv avars) sv;
  avars

(** Given two variable maps [vm_1] and [vm_2], return a new map [vm] and
    a variable renaming [sigma] such that:
    - for all [s in dom(vm_1)], [vm(s) = vm_1(s)]
    - for all [s in dom(vm_2) \ dom(vm_1)], [vm(s) = vm_2(s)]
    - for all [s in dom(vm_2) \cap dom(vm_1)], [vm(s) = sigma(vm_2(s))] *)
let merge_vmap vm1 vm2 =
  let sigma = VarSym.H.create 134 in
  let vm  = Hashtbl.copy vm1 in
  let pp s vs = 
    let pp_qual fmt (q,s) = 
      match q with
      | Qual s1 -> Format.fprintf fmt "%s`%s" s1 s
      | _       -> Format.fprintf fmt "%s" s in
    Format.eprintf "%a -> %a(%i)@."
                   pp_qual s 
                   Game.pp_v vs (Id.tag vs.VarSym.id) in
  Format.eprintf "vm1 =@.";
  Hashtbl.iter pp vm1;
  Format.eprintf "vm2 =@.";
  Hashtbl.iter pp vm2;
  Hashtbl.iter
    (fun s vs ->
      if Hashtbl.mem vm1 s
      then VarSym.H.add sigma vs (Hashtbl.find vm1 s)
      else Hashtbl.add vm s vs)
    vm2;
  vm, (fun vs -> try VarSym.H.find sigma vs with Not_found -> vs)

let vmap_of_vss vss =
  let vm = Hashtbl.create 134 in
  VarSym.S.iter
    (fun vs ->
       Hashtbl.add vm
         (map_qual (fun os -> Id.name os.OrclSym.id) vs.VarSym.qual, VarSym.to_string vs)
         vs)
    vss;
  vm

let vmap_of_ves ves =
  let vm = Hashtbl.create 134 in
  Se.iter
    (fun v ->
      let vs = destr_V v in
      Hashtbl.add vm
        (map_qual (fun os -> Id.name os.OrclSym.id) vs.VarSym.qual, VarSym.to_string vs)
        vs)
    ves;
  vm

let vmap_of_globals gdef = vmap_of_vss (vars_global_gdef gdef)

let vmap_of_se se =
  let rec vmap_aux s0 ev =
    if is_Quant ev then
      let (_,(vs,_),ev) = destr_Quant ev in
      List.fold_left (fun s v -> VarSym.S.add v s) (vmap_aux s0 ev) vs
    else
      s0
  in
  vmap_of_vss (vmap_aux (vars_global_gdef se.se_gdef) se.se_ev)


let ves_to_vss ves =
  Se.fold (fun e vss -> VarSym.S.add (destr_V e) vss) ves VarSym.S.empty

let vmap_in_orcl se op =
  let (i,_,_,_) = op in
  let gdef_before =
    let rbefore, _ = cut_n i se.se_gdef in
    L.rev rbefore
  in
  let _,seoc = get_se_octxt_len se op 0 in
  vmap_of_vss
    (VarSym.S.union
       (VarSym.S.union (vars_global_gdef gdef_before)
          (ves_to_vss (write_lcmds seoc.seoc_cleft)))
       (set_of_list seoc.seoc_oargs))
