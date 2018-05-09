open Abbrevs
open Util
open Type
open Expr
open ExprUtils
open Game 
open TheoryTypes
open TheoryState
open CoreTypes
open CoreRules
open File
open Syms
module Ht = Hashtbl


(*let pp_debug a = Format.eprintf a*)
let pp_debug a = Format.ifprintf Format.err_formatter a

(** game translation *)
let assertion = "assertion"
let ec_keyword = 
  [ "var"; "module"; "type"; "op"; "pred"; "lemma"; 
    "res"; "rnd"; "proc"; "fun"; "forall"; "exists"; 
    "m"; "g1"; "e"; "tt"; "beta"; "alpha"; "delta"; "arg";
    assertion
]


let reloc_tbl = Hashtbl.create 0

let check_cap s = s.[0] <> Char.lowercase s.[0]

let exclude_private s = 
  try Hashtbl.find reloc_tbl s
  with Not_found ->
    let s' = 
      if List.mem s ec_keyword || check_cap s then "__"^s else s in
    Hashtbl.add reloc_tbl s s';
    s' 
       
let pvar modn v = 
  modn, exclude_private (Vsym.to_string v)

let globals gdef = 
  let glob = gdef_global_vars gdef in
  List.map (fun v ->
     MCvar(pvar [] v, Tzc v.Vsym.ty)) (Vsym.S.elements glob)

let _mk_eget file h e = 
  let hi = Fsym.H.find file.hvar h in
  hi.h_eget e

let _mk_fget file mem h f = 
  let hi = Fsym.H.find file.hvar h in
  hi.h_fget mem f

let op_of_op file ty = function
  | GExp _  -> Opow
  | GLog gv -> Ostr ((gvar_mod file gv) ^ ".log")
  | GInv    -> Ostr ((gvar_mod file (destr_G_exn ty)) ^ ".([-])") (* FIXME: this should be fixed in CyclicGroup *)
  | FOpp    -> Oopp
  | FMinus  -> Osub
  | FInv    -> Ostr "F.inv"
  | FDiv    -> Odiv
  | Eq      -> Oeq
  | Not     -> Onot
  | Ifte    -> assert false
  | EMap bm -> Ostr  ((bvar_mod file bm) ^ ".e")
  | Perm _  -> assert false
  | (ProjKeyElem _|FunCall _|RoCall _|RoLookup _) -> fixme "undefined"

let op_of_nop ty = function
  | FPlus -> Oadd
  | FMult -> Omul
  | Xor   -> 
    begin match ty.ty_node with 
    | BS _ -> Opow
    | Bool  -> assert false
    | _     -> assert false
    end
  | Land -> Oand
  | GMult -> Omul

let string_of_cnst file ty = function
  | GGen   -> fsprintf "%s.g" (gvar_mod file (destr_G_exn ty))
  | FNat i -> fsprintf "(F.ofint %i)" i
  | Z      -> fsprintf "%s.zeros" (lvar_mod file (destr_BS_exn ty))
  | B b    -> fsprintf "%b" b
  | MatZero-> fsprintf "matzero"
  | MatId -> fsprintf "matid"

let rec expression file e = 
  match e.e_node with 
  | V v -> Epv (pvar [] v)
  (* | H(h,e) ->  mk_eget file h (expression file e) *)
  | Tuple es -> Etuple (List.map (expression file) es)
  | Proj (i,e) -> Eproj(i+1, expression file e) 
  | Cnst c -> Ecnst (string_of_cnst file e.e_ty c)
  | App(Ifte,[e1;e2;e3]) -> 
    Eif(expression file e1, expression file e2, expression file e3)
  | App(op,es) ->
    Eapp(op_of_op file e.e_ty op, List.map (expression file) es)
  | Nary(Land, es) ->
    begin match List.rev es with
    | [] -> assert false
    | e :: es ->
      let op = op_of_nop e.e_ty Land in
      List.fold_left 
        (fun e e1 -> Eapp(op,[expression file e1; e])) 
        (expression file e) es
    end
  | Nary(op,es) -> 
    begin match es with
    | [] -> assert false
    | e::es -> 
      let op = op_of_nop e.e_ty op in
      List.fold_left (fun e e1 -> Eapp(op,[e;expression file e1])) 
        (expression file e) es 
    end
  | Quant _ (* | ProjPermKey _ *) -> assert false

let rec formula file prefix mem 
    ?(local=Vsym.S.empty) ?(flocal=Vsym.S.empty) e = 
  match e.e_node with 
  | V v -> 
    if Vsym.S.mem v flocal then Fv(pvar [] v, None)
    else if Vsym.S.mem v local then Fv (pvar [] v, mem)
    else Fv (pvar prefix v, mem)
  (* | H(h,e) ->  mk_fget file mem h (formula file prefix mem ~local ~flocal e) *)
  | Tuple es -> Ftuple (List.map (formula file prefix mem ~local ~flocal) es)
  | Proj (i,e) -> Fproj(i+1, formula file prefix mem ~local ~flocal e) 
  | Cnst c -> Fcnst (string_of_cnst file e.e_ty c)
  | App(Eq,[e1;e2]) -> 
    f_eq (formula file prefix mem ~local ~flocal e1) 
         (formula file prefix mem ~local ~flocal e2)
  | App(Ifte,[e1;e2;e3]) -> 
    Fif(formula file prefix mem ~local ~flocal e1, 
        formula file prefix mem ~local ~flocal e2, 
        formula file prefix mem ~local ~flocal e3)
  | App(op,es) ->
    Fapp(op_of_op file e.e_ty op, List.map (formula file prefix mem ~local ~flocal) es)
  | Nary(Land, es) ->
    begin match List.rev es with
    | [] -> assert false
    | e :: es ->
      let op = op_of_nop e.e_ty Land in
      List.fold_left 
        (fun e e1 -> Fapp(op,[formula file prefix mem ~local ~flocal e1; e])) 
        (formula file prefix mem ~local ~flocal e) es
    end
  | Nary(op,es) -> 
    begin match es with
    | [] -> assert false
    | e::es -> 
      let op = op_of_nop e.e_ty op in
      List.fold_left 
        (fun e e1 -> Fapp(op,[e;formula file prefix mem ~local ~flocal e1])) 
        (formula file prefix mem ~local ~flocal e) es 
    end
  | Quant _ (* | ProjPermKey _ *) -> assert false
  
let rec init_res_expr ty = 
  match ty.ty_node with 
  | BS lv    -> Expr.mk_Z lv
  | Bool     -> Expr.mk_True
  | G gv     -> Expr.mk_GGen gv
  | Fq       -> Expr.mk_FZ
  | Prod tys -> Expr.mk_Tuple (List.map init_res_expr tys)
  | Int      -> assert false
  | KeyPair _ | KeyElem _ -> assert false

let log_oracle modn osym = 
  modn, Format.sprintf "log%s" (Osym.to_string osym)

let oracle_info info osym = 
  try Osym.H.find info.adv_g.oinfo osym
  with Not_found -> assert false

let q_oracle_i info osym = 
  try (oracle_info info osym).obound
  with Not_found -> assert false

let q_oracle file osym = 
  let info = adv_info file in
  q_oracle_i info osym

let oracle file (osym,param,lc,ret) = 
  let res = "_res" in
  let vres = [],res in
  let rec body lc = 
    match lc with
    | [] -> [Iasgn([vres], expression file ret)]
    | LLet (v,e) :: lc -> 
      Iasgn ([pvar [] v],expression file e) :: body lc
    | LSamp (v,(ty,r)) :: lc -> 
      Irnd ([pvar [] v], ty, List.map (expression file) r) :: body lc
    | LBind (_vs, _h) :: _ -> assert false 
    (*      while (res <> None && dom <> []) {
            e = hd dom;
            dom = tl dom;
            vs = h.[e];
            body
            } *)
    | LGuard e :: lc-> [Iif (expression file e, body lc, [])] in
  let vc  = log_oracle [] osym in
  let log = e_pv vc in 
  let c   = e_length log in 
  let q   = Ecnst (q_oracle file osym) in 
  let init_res lc = 
    let e = expression file (init_res_expr osym.Osym.codom) in
    let et = Etuple (List.map (fun v -> e_pv (pvar [] v)) param) in
    [ Iasgn([vres], e);
      Iif (e_lt c q, Iasgn([vc],e_cons et log):: lc, []) ] in
  {
    f_name = "o" ^ Osym.to_string osym;
    f_def = Fbody {
    f_param = List.map (fun v -> pvar [] v, v.Vsym.ty) param;
    f_local = (vres, osym.Osym.codom) :: 
      List.map (fun e ->  
        let v = destr_V e in 
        (pvar [] v, v.Vsym.ty)) (Se.elements (write_lcmds lc));
    f_res   = Some (vres, Tzc osym.Osym.codom);
    f_body  = init_res (body lc); }
  }

let asym_to_string a = "a"^Asym.to_string a

let ginstr file adv = function
  | GLet (v,e) -> Iasgn ([pvar [] v],expression file e)
  | GSamp(v,(ty,r)) -> 
    Irnd ([pvar [] v], ty, List.map (expression file) r)
  | GCall(vs,a,e,_) -> 
    let es = destr_Tuple_nofail e in
    Icall(List.map (pvar []) vs, (adv, asym_to_string a),
          List.map (expression file) es)
  | GAssert e ->
    let asst = ([], assertion) in
    Iasgn([asst], Eapp(Oand, [e_pv asst; expression file e]))

let instructions file adv gdef =   
  List.map (ginstr file adv) gdef 

(* --------------------------------------------------------------------- *)
(* Initialize file *)

module Ass = Assumption

let add_assumption_dec file name assum =
  let advty = top_name file ("Adv_"^name) in
  let ngame1 = top_name file ("G_"^name^"1") in
  let ngame2 = top_name file ("G_"^name^"2") in

  let do_local v = (pvar [] v, v.Vsym.ty) in
  let locals_end = 
    List.fold_left (fun l (_,xs,_) -> 
      List.fold_left (fun l x -> do_local x :: l) l xs) [] assum.Ass.ad_acalls in
  let mA = mod_name "A" [] in

  (* build the module type for A *)
  let amodty = {
    modt_name  = advty;
    modt_param = [];
    modt_proc  = 
      List.map (fun (a,xs,arg) ->
        let aty = (fst arg).e_ty in
        let rty = mk_Prod (List.map (fun xs -> xs.Vsym.ty) xs) in
        (asym_to_string a, [None, aty], rty, [])) assum.Ass.ad_acalls;
  } in

  let g_end i = 
    List.map (fun (a,xs,arg) ->
      let arg = if i = 1 then fst arg else snd arg in
      let args = destr_Tuple_nofail arg in
      Icall(List.map (pvar []) xs, (mA, asym_to_string  a), 
            List.map (expression file) args)) assum.Ass.ad_acalls in
  let vres = 
    let (_,xs,_) = L.last assum.Ass.ad_acalls in
    L.last xs in
  assert (equal_ty vres.Vsym.ty mk_Bool);
  let game name gdef i = 
    let locals = 
      Vsym.S.fold (fun v l -> do_local v :: l) 
        (gdef_global_vars gdef) locals_end in
    
    let init = instructions file mA gdef in
    let gend = g_end i in
    let main = {
      f_name = "main";
      f_def = Fbody {
        f_param = [];
        f_local = locals;
        f_res = Some (pvar [] vres, Tzc mk_Bool);
        f_body = init @ gend;
      }
    } in
    { mod_name = name;
      mod_param = ["A", advty];
      mod_body = Mod_def [MCfun main];
    } in 
  let g1 = game ngame1 assum.Ass.ad_prefix1 1 in
  let g2 = game ngame2 assum.Ass.ad_prefix2 2 in
  

  let info = {
    ad_name  = assum.Ass.ad_name;
    ad_advty = amodty;
    ad_cmd1  = g1;
    ad_cmd2  = g2; 
  } in
  Ht.add file.assump_dec name info

let add_assumption_comp file name assum =
  let advty = top_name file ("Adv_"^name) in
  let ngame = top_name file ("G_"^name) in

  let mA = mod_name "A" [] in

  (* build the module type for A *)
  let amodty = {
    modt_name  = advty;
    modt_param = [];
    modt_proc  = 
      List.map (fun (a,xs,arg) ->
        let aty = arg.e_ty in
        let rty = mk_Prod (List.map (fun xs -> xs.Vsym.ty) xs) in
        (asym_to_string a, [None, aty], rty, [])) assum.Ass.ac_acalls;
  } in

  (* build the main module *)
  let do_local v = (pvar [] v, v.Vsym.ty) in
  let locals_end = 
    List.fold_left (fun l (_,xs,_) -> 
      List.fold_left (fun l x -> do_local x ::l) l xs) [] assum.Ass.ac_acalls in

  let game = 
    let res = ([],"_res") in
    let local = 
      Vsym.S.fold (fun v l -> do_local v :: l)
        (gdef_global_vars assum.Ass.ac_prefix) locals_end in 
    let init = instructions file mA assum.Ass.ac_prefix in
    let g_end = 
      List.map (fun (a,xs,arg) ->
        let args = destr_Tuple_nofail arg in
        Icall(List.map (pvar []) xs, (mA, asym_to_string  a), 
              List.map (expression file) args)) assum.Ass.ac_acalls in
    let i_ret = [ Iasgn([res], expression file assum.Ass.ac_event)] in
    let main = {
      f_name = "main";
      f_def = Fbody {
        f_param = [];
        f_local = (res,mk_Bool) :: local;
        f_res = Some (res, Tzc mk_Bool);
        f_body = 
          init @ g_end @ i_ret;
      }
    } in
    { mod_name = ngame;
      mod_param = ["A", advty];
      mod_body = Mod_def [MCfun main];
    } in 

  let info = {
    ac_name  = assum.Ass.ac_name;
    ac_kind  = assum.Ass.ac_type;
    ac_advty = amodty;
    ac_cmd   = game;
  } in
  Ht.add file.assump_comp name info
  
let add_assumptions file ts = 
  Mstring.iter (fun n a -> add_assumption_dec  file n a) ts.ts_assms_dec;
  Mstring.iter (fun n a -> add_assumption_comp file n a) ts.ts_assms_comp

let init_file ts = 
  let file = empty_file in
  add_lvars    file ts;
  add_gvars    file ts;
  add_bilinears file ts;
  add_hashs     file ts;
  add_assumptions file ts;  
  file

(* --------------------------------------------------------------------- *)
(* Initialize file *)

let oracles file oinfo = 
  { mod_name = "O";
    mod_param = [];
    mod_body = Mod_def 
      (List.rev 
      (Osym.H.fold (fun os (oparams,obody,ores) l ->
        MCfun(oracle file (os, oparams, obody, ores))::l) oinfo [])) }

let log_oracles_i info = 
  Osym.H.fold (fun o _ l -> (log_oracle [] o, o.Osym.dom) :: l) 
    info.adv_g.oinfo []  

let log_oracles file = log_oracles_i (adv_info file)
   
let game ?(local=`Local) ?(pinfo=[]) file g =
  try find_game file g 
  with Not_found ->
    let oinfo = Osym.H.create 7 in
    let add_oinfo (o,params,od) = 
      let (body,e) = match od with Oreg b -> b | _ -> assert false in
      Osym.H.add oinfo o (params,body,e) in
    let mk_info i = 
      match i with
      | GCall(_,_,_,odef) -> List.iter add_oinfo odef
      | _ -> () in
    List.iter mk_info g;
    
    let (nA,tA) = adv_decl file in
    let vcs = log_oracles file in
    let cdecls = List.map (fun (v,ty) -> MCvar (v, List ty)) vcs in
    let globs = globals g in 
    let m_orcl = oracles file oinfo in
    let alias = (mod_name nA [mod_name "O" []]) in (* FIXME add the H oracle *)
    let m_adv = {
      mod_name = nA;
      mod_param = [];
      mod_body = Mod_alias alias;
    } in
    let init_vcs = List.map (fun (v,_) -> Iasgn([v], e_nil)) vcs in
    let decl_assert, init_assert = 
      if Game.has_assert g then 
        let assertion = ([],assertion) in
        [MCvar (assertion, Tzc mk_Bool)], [Iasgn([assertion], e_true)]
      else [], [] in
    let f_main = 
      { f_name = "main";
        f_def = Fbody {
        f_param = [];
        f_local = [];
        f_res   = None;
        f_body  = init_assert @ init_vcs @ 
                  instructions file (mod_name nA []) g;}
      } in
    let comp = 
      decl_assert @ cdecls @ globs @ [MCmod m_orcl;
                       MCmod m_adv;
                       MCfun f_main] in
    let name = top_name file ("M__"^(fsprintf "%a" Rules.pp_path pinfo^"__")) in
    let modu = 
      { mod_name  = name;
        mod_param = [nA,tA];
        mod_body  = Mod_def comp;
      } in
    
    bind_game file local g modu;

    modu

let init_section file name pft =
  let name = start_section file name in
  let g = pft.pt_ju.ju_se.se_gdef in
  init_adv_info file g;
  ignore (game ~local:`Global file g);
  name 
  
let flocal_ev _ev = 
  List.fold_left (fun se (vs,_) -> 
    List.fold_left (fun se v -> Vsym.S.add v se) se vs) 
    Vsym.S.empty (fixme "Event.binding ev")

let extract_ev _file _modm _mem _se =
  fixme "" (*
  let ev = se.se_ev in
  let ev = 
    if not (is_Quant ev) then 
      formula file modm mem ev 
    else      
      let flocal = flocal_ev ev in
      let do_bd (vs,ors) body =
        let o = Oracle.destr_as_Osym_t ors in
        let ty = mk_Prod (List.map (fun v -> v.Vsym.ty) vs) in
        let ty = 
          Printer.pp_type file F.str_formatter ty;
          F.flush_str_formatter () in
        let bd = List.map (fun v -> snd (pvar [] v)) vs in
        Fquant_in((Event.quant ev), (bd, ty, body), 
                  (Fv (log_oracle modm o, mem))) in
      List.fold_right do_bd (Event.binding ev)
        (formula ~flocal file modm mem (Event.expr ev))  in
  if Game.has_assert se.se_gdef then
    f_and (Fv((modm, assertion), mem)) ev
  else ev *)

let extract_pr_se ?(local=`Local) file mem se =
  let modm  = game ~local file se.se_gdef in
  let modma = {mn = modm.mod_name; ma = [adv_mod file]} in
  let ev = extract_ev file [modm.mod_name] None se in
  Fpr((modma,"main"), mem, [], ev)

let extract_pr ?(local=`Local) file mem ju =
  extract_pr_se ~local file mem ju.ju_se

let extract_full_pr ?(local=`Local) file mem ju =
  let pr1 = extract_pr ~local file mem ju in
  let full, abs = match ju.ju_pr with
    | Pr_Succ | Pr_Adv -> pr1, `BOUND
    | Pr_Dist se -> 
      let pr2 = extract_pr_se ~local file mem se in
      Fabs (f_rsub pr1 pr2), `ABS in
  pr1, full, abs
        

let mem = "m"
let cmp_eq = true
let cmp_le = false
let mk_cmp f1 cmp f2 = 
  if cmp = cmp_eq then f_eq f1 f2 else f_le f1 f2
let forall_mem f = Fforall_mem(mem, f)

let add_pr_lemma ?(pinfo=[])file f proof = 
  let name = top_name file ("lem__"^(fsprintf "%a" Rules.pp_path pinfo^"__")) in
  let body = forall_mem f in
  add_local file (Clemma(true, name,body,proof));
  name

let get_game file g = 
  try find_game file g
  with Not_found -> assert false

let pr_admit s _file fmt () =
  F.fprintf fmt "(* %s *) admit." s

let pp_swap nvc side fmt (p,i) = 
  F.fprintf fmt "swap{%i} %i %i" side (nvc + p+1) i

let pp_swaps nvc side fmt sw = 
  if sw <> [] then
    F.fprintf fmt "@[%a.@]@ " (pp_list ";@ " (pp_swap nvc side)) sw

let init_same_ev intros file ev tac =
  let nA = adv_name file in
  let pp_ev fmt ev = 
    match ev with
    | None -> F.fprintf fmt "_"
    | Some ev -> Printer.pp_form fmt ev in
  let open_pp fmt () = 
    F.fprintf fmt "@[<v>%sbyequiv (_: ={glob %s} ==> %a);@ " 
      (if intros then "intros &m;" else "") nA pp_ev ev;
    F.fprintf fmt "  [ proc | by [] | by %s].@ " tac in
  let close_pp fmt () = 
    F.fprintf fmt "@]" in
  open_pp,close_pp

let init_same intros file ju1 ju2 = 
  let g1 = get_game file ju1.ju_se.se_gdef in
  let g2 = get_game file ju2.ju_se.se_gdef in
  let ev = None in
  let open_pp, close_pp = 
    init_same_ev intros file ev "[]" in
  g1, g2, open_pp, close_pp

let pr_swap sw ju1 ju2 file =
  let _,_,open_pp, close_pp = init_same false file ju1 ju2 in
  let nvc = List.length (log_oracles file) in
  let toskip = 
    if has_assert ju1.ju_se.se_gdef then nvc + 1 else nvc in
  fun fmt () ->
    open_pp fmt ();
    pp_swaps toskip 1 fmt sw;
    F.fprintf fmt "sim.";
    close_pp fmt ()

let invert_swap sw = 
  List.fold_left (fun sw (p,i) -> (p+i, -i)::sw) [] sw

(* --------------------------------------------------------------------- *)
(* Tactics *)

type tactic = 
  | Admit
  | Rnd
  | Skip
  | Wp       of int * int
  | Wp1      of int
  | Auto
  | Progress of string list
  | Algebra
  | Smt 
  | Call     of form 
  | If
  | Proc
  | Apply    of string
  | Seq      of int * int * form
  | TOr      of tactic list
  | TRepeat  of tactic
  | TSeq     of tactics
  | TSeqSub  of tactic * tactics 
  | Tstring  of string

and tactics = tactic list

type tcommand = 
  | Tac of tactic
  | TSub of tcommands list

and tcommands = tcommand list

let add_wp i1 i2 cont = 
  match cont with
  | Tac (Wp(i1',i2')) :: _ | Tac (TSeq (Wp(i1',i2')::_)) :: _ ->
    assert (i1' <= i1);
    assert (i2' <= i2);
    cont
  | Tac ((Rnd | Skip | If) as t1) :: cont ->
    Tac (TSeq [Wp(i1,i2);t1]) :: cont
  | Tac (TSeq ts) :: cont ->
    Tac (TSeq (Wp(i1,i2)::ts)) :: cont
  | _ -> Tac(Wp(i1,i2)) :: cont

let add_wp1 i1 cont = 
  match cont with
  | Tac (Wp1 i1') :: _ | Tac (TSeq (Wp1 i1' :: _)) :: _ ->
    assert (i1' <= i1);
    cont
  | Tac ((Rnd | Skip | If) as t1) :: cont ->
    Tac (TSeq [Wp1 i1;t1]) :: cont
  | Tac (TSeq ts) :: cont ->
    Tac (TSeq (Wp1 i1 ::ts)) :: cont
  | _ -> Tac(Wp1 i1) :: cont


let add_rnd cont = 
  match cont with
  | Tac ((Rnd | Skip | Wp _ | If) as t1) :: cont ->
    Tac (TSeq [Rnd;t1]) :: cont
  | Tac (TSeq ts) :: cont ->
    Tac (TSeq (Rnd::ts)) :: cont
  | _ -> Tac Rnd :: cont

let t_algebra = TSeq[Algebra; 
                     Tstring 
                       "rewrite ?supp_def ?FSet.mem_single;progress;algebra *"
                    (* ; Smt *)
                    ]
let t_spa = TSeq [Skip;Progress [];t_algebra]
let t_aa  = TSeq [Auto;t_algebra]
let t_id  = TSeq []

let t_pr_if = 
  (* Tstring "by progress;algebra *;smt" *)
  Tstring "by progress;algebra *"

let pp_congr_quant ~_semi _fmt _ev =
  fixme "undefined"
  (*
  match (Event.binding ev) with
  | [] -> ()
  | [vs,_] -> 
    F.fprintf fmt 
      "apply %s_congr=> [[%a]];iota zeta%s"
      (if (Event.quant ev) = Expr.All then "all" else "any")
      (pp_list " " (fun fmt _ -> F.fprintf fmt "_")) vs
      (if semi then ";" else "")
  | _ -> assert false (* Not implemented *)
  *)

let _pp_impl_quant _fmt _ev = fixme "undefined"
  (*
  match (Event.binding ev) with
  | [] -> F.fprintf fmt "by []."
  | [vs,_] -> 
    F.fprintf fmt 
      "by move=> &hr;apply %s_impl=> [[%a]];iota."
      (if (Event.quant ev) = Expr.All then "all" else "any")
      (pp_list " " (fun fmt _ -> F.fprintf fmt "_")) vs
  | _ -> assert false *)

let rec pp_tac fmt = function
  | Admit     -> F.fprintf fmt "admit" 
  | Rnd       -> F.fprintf fmt "rnd" 
  | Skip      -> F.fprintf fmt "skip"
  | Wp(i1,i2) -> F.fprintf fmt "wp %i %i" i1 i2
  | Wp1 i1    -> F.fprintf fmt "wp %i" i1
  | Auto      -> F.fprintf fmt "auto" 
  | Progress s-> 
    if s = [] then F.fprintf fmt "progress" 
    else 
      F.fprintf fmt "progress @[[%a]@]" 
        (pp_list "@ " (fun fmt -> F.fprintf fmt "%s")) s
  | Algebra   -> F.fprintf fmt "algebra *"
  | Smt       -> F.fprintf fmt "smt"
  | Call inv  -> F.fprintf fmt "call (_:%a)" Printer.pp_form inv
  | If        -> F.fprintf fmt "if" 
  | Proc      -> F.fprintf fmt "proc"
  | Seq (i1,i2,f) -> 
    F.fprintf fmt "@[seq %i %i :@ (@[%a@])@]" i1 i2 Printer.pp_form f
  | Apply s   -> F.fprintf fmt "apply %s" s
  | TOr []    -> ()
  | TOr [t]   -> pp_tac fmt t
  | TOr ts    -> 
    F.fprintf fmt "(@[%a@])" (pp_list " ||@ " pp_tac) ts
  | TRepeat t -> F.fprintf fmt "do ?%a" pp_tac t
  | TSeq lt   -> 
    if lt <> [] then
      F.fprintf fmt "@[<hov>(%a)@]" (pp_list ";@ " pp_tac) lt 
  | TSeqSub(t, ts) ->
    F.fprintf fmt "@[<hov 2>%a;@ [ @[<hov 0>%a@]]@]" 
      pp_tac t
      (pp_list " |@ " pp_tac) ts
  | Tstring s -> F.fprintf fmt "%s" s


let rec pp_cmd fmt = function
  | Tac (TSeq lt) ->
    if lt <> [] then
      F.fprintf fmt "@[<hov>%a.@]" (pp_list ";@ " pp_tac) lt 
  | Tac t -> F.fprintf fmt "%a." pp_tac t
  | TSub ts -> 
    F.fprintf fmt "  @[<v>%a@]" 
      (pp_list "@ @ " pp_cmds) ts
      
and pp_cmds fmt tacs=
  F.fprintf fmt "@[<v>%a@]" (pp_list "@ " pp_cmd) tacs 



type conv_info = {
  loc1 : Vsym.S.t;
  loc2 : Vsym.S.t;
  passert1 : int;
  passert2 : int;
  pos1 : int;
  pos2 : int;
  tacs : tcommands;
  invs : form
}

let add_let_info file g v e side loc info = 
  let s = if side then Some "1" else Some "2" in
  let loc1 = if side && loc then Vsym.S.add v info.loc1 else info.loc1 in
  let loc2 = if not side && loc then Vsym.S.add v info.loc2 else info.loc2 in
  let local = if side then loc1 else loc2 in
  let e1 = formula file [g.mod_name] s ~local e in
  let e2 = formula file [g.mod_name] s ~local (Expr.mk_V v) in
  { info with
    loc1 = loc1;
    loc2 = loc2;
    pos1 = if side then info.pos1 + 1 else info.pos1;
    pos2 = if side then info.pos2 else info.pos2 + 1;
    tacs = 
      add_wp (info.pos1 - info.passert1) (info.pos2 - info.passert2) info.tacs;
    invs = f_and (f_eq e1 e2) info.invs }

let add_assert_info file g1 e1 g2 e2 info = 
  let e1 = formula file [g1.mod_name] (Some "1") e1 in
  let e2 = formula file [g2.mod_name] (Some "2") e2 in
  let pos1 = info.pos1 + 1 and pos2 = info.pos2 + 1 in
  { 
    loc1 = info.loc1;
    loc2 = info.loc2;
    passert1 = pos1;
    passert2 = pos2;
    pos1;
    pos2;
    tacs = add_wp info.pos1 info.pos2 info.tacs;
    invs = f_and e1 (f_and e2 info.invs) }

let add_rnd_info file g1 g2 v1 v2 l1 l2 loc info = 
  let loc1 = if loc then Vsym.S.add v1 info.loc1 else info.loc1 in
  let loc2 = if loc then Vsym.S.add v2 info.loc2 else info.loc2 in
  let e1 = formula file [g1.mod_name] (Some "1") ~local:loc1 (Expr.mk_V v1) in
  let e2 = formula file [g2.mod_name] (Some "2") ~local:loc2 (Expr.mk_V v2) in
  let add_restr side e l invs = 
    let g,s,local = 
      if side then g1.mod_name, Some "1", loc1
      else g2.mod_name, Some "2", loc2 in
    let l = List.map (formula file [g] s ~local) l in
    List.fold_left (fun invs e' -> f_and (f_neq e e') invs) invs l in
  let invs = add_restr true e1 l1 info.invs in
  let invs = add_restr false e2 l2 invs in
  { info with
    loc1 = loc1;
    loc2 = loc2;
    pos1 = info.pos1 + 1;
    pos2 = info.pos2 + 1;
    tacs = add_rnd info.tacs;
    invs = f_and (f_eq e1 e2) invs }

let add_guard file g1 g2 e1 e2 info tacs =
  let e1 = formula file [g1.mod_name] (Some "1") ~local:info.loc1 e1 in
  let e2 = formula file [g2.mod_name] (Some "2") ~local:info.loc2 e2 in 
  let t = f_and e1 e2 in
  { info with
    loc1 = info.loc1;
    loc2 = info.loc2;
    pos1 = 0;
    pos2 = 0;
    tacs = tacs; 
    invs = f_and t info.invs } 
  
let init_inv_oracle p1 p2 inv =
  let add_eq f v1 v2 = 
    f_and (f_eq (Fv(pvar [] v1, Some "1")) (Fv(pvar [] v2, Some "2"))) f in
  List.fold_left2 add_eq 
    (f_and (f_eq (Fv(([],"_res"), Some "1")) (Fv(([],"_res"), Some "2"))) inv)
    p1 p2

(*let mk_eq_ *)
let mk_eq_expr_p file ?(local=Vsym.S.empty) p1 p2 e = 
  f_eq 
    (formula file [p1] (Some "1") ~local e)
    (formula file [p2] (Some "2") ~local e)

let mk_eq_exprs_p file ?(local=Vsym.S.empty) p1 p2 es =
  match Se.elements es with
  | [] -> f_true
  | e::es -> 
    List.fold_left (fun eq e -> f_and eq (mk_eq_expr_p file ~local p1 p2 e))
      (mk_eq_expr_p file ~local p1 p2 e) es
  
let mk_eq_exprs file ?(local=Vsym.S.empty) g1 g2 es =
  mk_eq_exprs_p file ~local g1.mod_name g2.mod_name es

let mk_eq_vcs_p g1 g2 vcs = 
  match vcs with
  | [] -> f_true
  | v::vs ->
    let mk_eq v = f_eq (Fv((g1,v),Some "1")) (Fv((g2,v),Some "2")) in
    List.fold_left (fun eq v -> f_and eq (mk_eq v)) (mk_eq v) vs 

let mk_eq_vcs g1 g2 vcs = 
  match vcs with
  | [] -> f_true
  | v::vs ->
    let mk_eq v = f_eq (f_v g1 v "1") (f_v g2 v "2") in
    List.fold_left (fun eq v -> f_and eq (mk_eq v)) (mk_eq v) vs 

let pp_inv file ?(local=Vsym.S.empty) g fmt (x,inv) = 
  let flocal = Vsym.S.singleton x in
  let f = formula file [g.mod_name] (Some "2") ~local ~flocal inv in
  let s = snd (pvar [] x) in
  F.fprintf fmt "@[<hov 2>(fun (%s:%a),@ %a)@]"
    s (Printer.pp_type file) x.Vsym.ty Printer.pp_form f 

let mu_x_def file fmt ty = 
  match ty.ty_node with
  | BS lv -> 
    F.fprintf fmt "%a.Dword.mu_x_def" Printer.pp_mod_name (mod_lvar file lv)
  | Bool ->
    F.fprintf fmt "Bool.Dbool.mu_x_def"
  | G gv -> F.fprintf fmt "%s.Distr.mu_x_def_in" (get_gvar file gv).tvar_mod
  | Fq    -> F.fprintf fmt "FDistr.mu_x_def_in"
  | Prod _
  | Int
  | KeyPair _
  | KeyElem _ -> assert false

let supp_def file fmt ty = 
  match ty.ty_node with
  | BS lv -> 
    F.fprintf fmt "%a.Dword.in_supp_def" Printer.pp_mod_name (mod_lvar file lv)
  | Bool ->
    F.fprintf fmt "Bool.Dbool.supp_def"
  | G gv ->  F.fprintf fmt "%s.Distr.supp_def" (get_gvar file gv).tvar_mod
  | Fq    -> F.fprintf fmt "FDistr.supp_def"
  | Prod _
  | Int
  | KeyPair _
  | KeyElem _ -> assert false

let rnd_loosless file fmt (ty, l) =
 match ty.ty_node, l with
  | BS lv, []-> 
    F.fprintf fmt "%a.Dword.lossless" Printer.pp_mod_name (mod_lvar file lv)
  | BS _, _ -> assert false (* FIXME *)
  | Bool, []  ->
    F.fprintf fmt "Bool.Dbool.lossless"
  | Bool, _ -> assert false (* FIXME *) 
  | G gv, []  ->
    F.fprintf fmt "%s.Distr.lossless" (get_gvar file gv).tvar_mod
  | G gv, [_]  ->
    F.fprintf fmt "%s.Distr.lossless_excp" (get_gvar file gv).tvar_mod
  | G _, _ -> assert false
  | Fq, []    -> 
    F.fprintf fmt "FDistr.lossless"
  | Fq, [_]    -> 
    F.fprintf fmt "FDistr.lossless_excp"
  | Fq, _ 
  | Prod _, _
  | Int   , _
  | KeyPair _, _  
  | KeyElem _,_  -> assert false

let t_rnd_loosless file ty f l = 
  F.fprintf F.str_formatter
    "rnd; conseq (_ : _ ==> %a);[progress; apply %a | ]"
    Printer.pp_form f (rnd_loosless file) (ty,l);
  Tac (Tstring (F.flush_str_formatter ())) 

let lossless_lcmds file lc =
  let rec aux i lc tacs = 
    match lc with 
    | [] -> 
      add_wp1 i tacs
    | LLet _::lc ->
      aux (i+1) lc (add_wp1 i tacs) 
    | LSamp(_,(ty,l))::lc ->
      aux (i+1) lc ((t_rnd_loosless file ty f_true l) :: tacs)
    | LBind _ :: _ -> assert false (* FIXME *)
    | LGuard _ :: lc ->
      let tacs2 = aux 0 lc [Tac Auto] in
      if i = 0 then 
        let tif = "if;[ | auto]" in
        assert (tacs = [Tac Auto]);
        Tac (Tstring tif) :: tacs2
      else
        let tif = 
          F.fprintf F.str_formatter "seq %i;[ | if;[ | auto]]" i;
          Tac (Tstring (F.flush_str_formatter ())) in
        [tif; TSub [tacs; tacs2]] in
  aux 0 lc [Tac Auto]

let lossless_orcl file (_,_,odecl) =  
  match odecl with
  | Oreg (lc, _) -> 
    Tac (Tstring "proc;sp 1;if;[ | auto];sp 1") :: lossless_lcmds file lc
  | Ohyb _       -> assert false  

let pr_lossless g file form i lc = 
  let rec aux i lc tacs = 
    match lc with 
    | [] -> tacs
    | GLet _::lc | GAssert _ :: lc ->
      aux (i+1) lc (add_wp1 i tacs)
    | GSamp(_,(ty,l))::lc ->
      aux (i+1) lc ((t_rnd_loosless file ty form l) :: tacs)
    | GCall(_,a,_,odef)::lc ->
      let call = 
        F.fprintf F.str_formatter "call (%s_ll (<:%s(%s).O) %a)" 
          (asym_to_string a) g.mod_name (adv_name file)
          (pp_list " " (fun fmt _ -> F.fprintf fmt "_")) odef;
        Tac (Tstring (F.flush_str_formatter ())) in
      let torcl = List.map (lossless_orcl file) odef in
      let tacs = 
        if torcl = [] then call :: tacs 
        else call :: TSub torcl :: tacs in
      aux (i+1) lc tacs in
  aux i lc [Tac Auto]

let eq_assert g1 g2 = 
  let assert1 = Fv(([g1.mod_name],assertion), Some "1") in
  let assert2 = Fv(([g2.mod_name],assertion), Some "2") in
  (f_eq assert1 assert2)

let post_assert g1 g2 post = 
  let assert1 = Fv(([g1.mod_name],assertion), Some "1") in
  let assert2 = Fv(([g2.mod_name],assertion), Some "2") in
  assert2, f_and (f_eq assert1 assert2) (f_imp assert2 post)

(* --------------------------------------------------------------------- *)
(* Certify conv rule*)

let build_conv_proof nvc eqvc file g1 g2 lc1 lc2 = 
  let add_info1 v1 e1 loc info = 
    add_let_info file g1 v1 e1 true loc info in
  let add_info2 v2 e2 loc info = 
    add_let_info file g2 v2 e2 false loc info in
  let add_rnd v1 v2 l1 l2 loc info = 
    add_rnd_info file g1 g2 v1 v2 l1 l2 loc info in
  let prove_orcl info (o1,p1,od1) (o2,p2,od2) =
    let (lc1,_) = match od1 with Oreg b -> b | _ -> assert false (* FIXME *) in
    let (lc2,_) = match od2 with Oreg b -> b | _ -> assert false (* FIXME *) in
    let rec aux lc1 lc2 info = 
      match lc1, lc2 with
      | [], [] -> add_wp info.pos1 info.pos2 info.tacs
      | LLet (v1,e1)::lc1, _ ->
        aux lc1 lc2 (add_info1 v1 e1 true info)
      | _, LLet (v2,e2)::lc2 ->
        aux lc1 lc2 (add_info2 v2 e2 true info)
      | LSamp(v1,(_,l1))::lc1, LSamp(v2,(_,l2))::lc2 ->
        aux lc1 lc2 (add_rnd v1 v2 l1 l2 true info) 
      | LBind _ :: _, LBind _ :: _ -> assert false (* FIXME *)
      | LGuard e1 :: lc1, LGuard e2 :: lc2 ->
        let tacs = aux lc1 lc2 (add_guard file g1 g2 e1 e2 info [Tac t_spa]) in
        if info.pos1 = 0 && info.pos2 = 0 then 
          Tac (TSeqSub(If, [t_pr_if; t_id; t_aa])) :: tacs 
        else
          Tac (Seq (info.pos1, info.pos2, info.invs)) ::
            TSub [info.tacs] ::
            Tac (TSeqSub(If, [t_pr_if; t_id; t_aa])) ::
            tacs 
      | _, _ -> assert false in
    let inv = init_inv_oracle p1 p2 info.invs in
    let info = 
      { loc1 = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p1;
        loc2 = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p2;
        passert1 = 0; passert2 = 0;
        pos1 = 0; pos2 = 0;
        tacs = [Tac t_spa];
        invs  = inv } in
    let tacs = aux lc1 lc2 info in
    let no1 = snd (log_oracle [] o1) in
    let no2 = snd (log_oracle [] o2) in
    Tac (Tstring "proc;sp 1 1;if;[by done | | by done]") :: 
    Tac (Tstring (Format.sprintf "sp 1 1;elim * => %s_R %s_L" no1 no2)) ::
    tacs in
        
  let add_call vs1 odef1 vs2 odef2 info = 
    let prove_orcl o1 o2 = prove_orcl info o1 o2 in
    let mk_eq v1 v2 = 
      let e1 = formula file [g1.mod_name] (Some "1") (Expr.mk_V v1) in
      let e2 = formula file [g2.mod_name] (Some "2") (Expr.mk_V v2) in 
      f_eq e1 e2 in
    let eqs = List.map2 mk_eq vs1 vs2 in
    let pr_orcls = List.map2 prove_orcl odef1 odef2 in
    { loc1 = info.loc1;
      loc2 = info.loc2;
      passert1 = 0; passert2 = 0;
      pos1 = info.pos1 + 1;
      pos2 = info.pos2 + 1;
      tacs = Tac (Call info.invs) :: TSub pr_orcls :: info.tacs;
      invs = List.fold_left (fun f eq -> f_and eq f) info.invs eqs } in
  (* the game are now ju ju' *)
  (* collect the distributions *)
  let ds = 
    List.fold_left (fun ds c ->
      match c with GSamp(_,(ty,l)) when l <> [] -> Sty.add ty ds | _ -> ds)
      Sty.empty lc1 in
  let t_end = 
    let ts = 
      Sty.fold (fun ty l ->
        F.fprintf F.str_formatter
          "by apply (in_excepted_diff %a)" 
          (Printer.pp_ty_distr file) ty;
        let s = F.flush_str_formatter () in
        Tstring s :: l) ds [Tstring "by algebra *;(try done);elimIF;algebra *" ] in
    if ts = [] then [] else [TOr ts] in
  
  let rec aux lc1 lc2 info = 
    match lc1, lc2 with
    | [], [] -> info
    | GLet (v1,e1)::lc1, _ ->
      aux lc1 lc2 (add_info1 v1 e1 false info)
    | _, GLet (v2,e2)::lc2 ->
      aux lc1 lc2 (add_info2 v2 e2 false info)
    | GSamp(v1,(_,l1))::lc1, GSamp(v2,(_,l2))::lc2 ->
      aux lc1 lc2 (add_rnd v1 v2 l1 l2 false info) 
    | GCall(vs1,_,_,odef1)::lc1, GCall(vs2,_,_,odef2)::lc2 ->
      aux lc1 lc2 (add_call vs1 odef1 vs2 odef2 info)
    | GAssert e1 :: lc1 , GAssert e2 :: lc2 ->
      let info = add_assert_info file g1 e1 g2 e2 info in
      let p1 = info.pos1 and p2 = info.pos2 in
      let tac1 = info.tacs in
      let assert2, cut = 
        post_assert g1 g2 (f_and (Feqglob (adv_name file)) info.invs) in

      let info = 
        { info with tacs = 
            [ Tac (TSeq
              (Tstring "skip; move=> &1 &2 [H1 H2]; move:H1;rewrite H2 /=" :: 
                Progress [] ::t_end))] } in
      let info = aux lc1 lc2 info in
      let s2 = 
        F.fprintf F.str_formatter "(%a)" Printer.pp_form assert2;
        F.flush_str_formatter () in
      let tac2 = 
        let tll = 
          F.fprintf F.str_formatter
            "seq %i 0 : true;[conseq _ (_: _ ==> true : = 1%%r) | conseq _ _ (_: _ ==> true : = 1%%r)]" (List.length lc1);
          Tac (Tstring (F.flush_str_formatter ())) in

        [Tac (Tstring ("case "^s2)) ;
          TSub [info.tacs; 
                [Tac (Tstring ("conseq * (_ : _ ==> true)"));
                 Tac (Tstring ("+ move=> &1 &2 [H1 H2]; move:H1; (cut -> : "^s2^
                                  "= false by rewrite neqF)=> //"));
                 tll;
                 TSub [ pr_lossless g1 file f_true 0 lc1; 
                        pr_lossless g2 file f_true 0 lc2]
                 ]] ] in
      let tacs = 
        [Tac (Seq(p1,p2,cut));
         TSub [ tac1; tac2]] in
      { info with tacs }
      
    | _, _ -> assert false in
  let info = 
    { loc1 = Vsym.S.empty; loc2 = Vsym.S.empty;
      pos1 = nvc; pos2 = nvc; passert1 = 0; passert2 = 0;
      tacs = [Tac (TSeq (Auto::Progress []::t_end))]; invs = eqvc } in
   
  aux lc1 lc2 info 


let pr_conv sw1 ju1 ju ju' ju2 sw2 file = 
  let g1 = get_game file ju1.ju_se.se_gdef in
  let g2 = get_game file ju2.ju_se.se_gdef in
  let vcs = log_oracles file in
  let eqvc = mk_eq_vcs g1 g2 (List.map fst vcs) in
  let nvc = 
    if has_assert ju.ju_se.se_gdef then 1 + List.length vcs 
    else List.length vcs in
  let info = 
    build_conv_proof nvc eqvc file g1 g2 ju.ju_se.se_gdef ju'.ju_se.se_gdef in 
  let forpost = 
    if ExprUtils.is_False ju1.ju_se.se_ev
       || ExprUtils.is_False ju2.ju_se.se_ev then
      "progress[not];algebra*;(try done);elimIF;algebra*"
    else
      "progress;algebra*;(try done);elimIF;algebra*" in
  let forpost = 
    if not (is_Quant ju.ju_se.se_ev) then forpost
    else 
      (F.fprintf F.str_formatter "progress [-split];%a%s"
        (pp_congr_quant ~_semi:true) ju.ju_se.se_ev forpost;
       F.flush_str_formatter ()) in
  let post,forpost = 
    if has_assert ju.ju_se.se_gdef then 
      let assert2, post = post_assert g1 g2 info.invs in
      let forpost = 
        F.fprintf F.str_formatter "move=> &1 &2 [] ->;case (%a);%s"
        Printer.pp_form assert2 forpost;
        F.flush_str_formatter () in
      post, forpost
    else info.invs, forpost in
      
  let open_pp, close_pp = 
    init_same_ev false file (Some post) forpost in 
  fun fmt () -> 
    open_pp fmt (); 
    F.fprintf fmt "(* conv rule *)@ ";
    pp_swaps nvc 1 fmt sw1;
    pp_swaps nvc 2 fmt (invert_swap sw2);
    pp_cmds fmt info.tacs;
    close_pp fmt ()

(* --------------------------------------------------------------------- *)
(* Certify rnd rule *)

let rec auto_sim g1 g2 lc tacs = 
  match lc with 
  | [] -> tacs 
  | GAssert _ :: lc | GLet _ :: lc | GSamp _ :: lc -> auto_sim g1 g2 lc tacs
  | GCall(_, _, _, os) :: lc ->
    let tcall = 
      if os = [] then Call f_true
      else
        let vcs = List.map (fun (o,_,_) -> log_oracle [] o) os in
        let r = Se.elements (Game.read_odefs os) in
        let r = List.map (fun e -> pvar [] (destr_V e)) r in
        let inv = mk_eq_vcs g1 g2 (vcs @ r) in
        F.fprintf F.str_formatter "call (_: %a);[ %a | ]"
          Printer.pp_form inv
          (pp_list " | " (fun fmt _ -> F.fprintf fmt "sim")) os;
        Tstring (F.flush_str_formatter ()) in
    auto_sim g1 g2 lc (Tac (TSeq [Auto;tcall]) :: tacs) 

let pr_random (pos,inv1,inv2) ju1 ju2 file =
  let g1 = get_game file ju1.ju_se.se_gdef in
  let g2 = get_game file ju2.ju_se.se_gdef in
  let vcs = log_oracles file in
  let eqvc = mk_eq_vcs g1 g2 (List.map fst vcs) in
  let nvc = 
    if has_assert ju1.ju_se.se_gdef then 1 + List.length vcs 
    else List.length vcs in
  let hd1,c1,tl1 = Util.split_n pos ju1.ju_se.se_gdef in 
  let c2 = List.nth ju2.ju_se.se_gdef (pos + 1) in
  let x1, x2 = 
    match c1, c2 with
    | GSamp(x1,_), GLet(x2,_) -> x1, x2
    | _, _ -> assert false in

  let eqfv =  
    mk_eq_exprs file g1 g2 (Se.remove (mk_V x1) (e_vars ju1.ju_se.se_ev)) in
  let eqx = 
    f_eq (Fv (pvar [g1.mod_name] x1, Some "1"))
         (Fv (pvar [g2.mod_name] x2, Some "2")) in
  let eqpost = f_and eqfv eqx in
  let npos = pos + nvc in
  let lc1 = List.rev hd1 in
  let lc2 = L.take pos ju2.ju_se.se_gdef in

  let assert2, post, forpost = 
    if has_assert lc1 then 
      let assert2, post = post_assert g1 g2 eqpost in
      let forpost = 
        F.fprintf F.str_formatter "move=> &1 &2 [] ->;case (%a)"
        Printer.pp_form assert2;
        F.flush_str_formatter () in
      Some assert2, post, forpost
    else None, eqpost, "[]" in

  let open_pp, close_pp = 
    init_same_ev false file (Some post) forpost in 

  let info = build_conv_proof nvc eqvc file g1 g2 lc1 lc2 in 
  let to_cut = f_and (Feqglob (adv_name file)) (f_and eqvc info.invs) in
  let to_cut = 
    if assert2 = None then to_cut else snd (post_assert g1 g2 to_cut) in
 
  
  let lossless1 = 
    if assert2 = None then [] 
    else 
      let assert1 = Fv(([g1.mod_name],assertion), None) in
      pr_lossless g1 file (f_not assert1) 0 (c1::tl1) in
  let lossless2 = 
    if assert2 = None then [] 
    else 
      let assert2 = Fv(([g2.mod_name],assertion), None) in
      pr_lossless g2 file (f_not assert2) 0 (L.drop pos ju2.ju_se.se_gdef) in

  fun fmt () ->
    open_pp fmt ();
    F.fprintf fmt "seq %i %i : (%a).@ " npos npos Printer.pp_form to_cut;
    F.fprintf fmt "  %a@ " pp_cmds info.tacs;
    let pr_rnd fmt () = 
      F.fprintf fmt "@[<hov 2>wp 1 1;rnd@ %a@ %a;skip.@]@ "
        (pp_inv file g2) inv2 (pp_inv file g2) inv1 in
    let pr_end fmt () = 
      let ty = (fst inv1).Vsym.ty in 
      let ty' = (fst inv2).Vsym.ty in
      let mu_x_def fmt () = 
        if equal_ty ty ty' then F.fprintf fmt "!%a" (mu_x_def file) ty
        else F.fprintf fmt "%a %a" (mu_x_def file) ty (mu_x_def file) ty' in
      F.fprintf fmt "progress; (by rewrite %a ||@ " mu_x_def ();
      F.fprintf fmt "           by apply %a ||@ " (supp_def file) ty;
      F.fprintf fmt "           by algebra*;(try done);elimIF;algebra* )." in
    if assert2 = None then begin
      F.fprintf fmt "sim.@ "; 
      pr_rnd fmt ();
      pr_end fmt ();
      close_pp fmt ()
    end else begin
      let assert2 = O.get assert2 in
      F.fprintf fmt "case (%a).@ " Printer.pp_form assert2; 
      F.fprintf fmt "  @[<v>%a@ " pp_cmds (auto_sim g1 g2 tl1 []);
      pr_rnd fmt ();
      F.fprintf fmt "move=> &1 &2 [H1 H2]; move: H1;rewrite H2.@ ";
      pr_end fmt ();
      F.fprintf fmt "@]@ ";
      let g1 = g1.mod_name and g2 = g2.mod_name in
      let a = assertion in
      F.fprintf fmt "seq %i 0 : (!%s.%s{1} /\\ !%s.%s{2});@ " 
        (List.length tl1 + 1) g1 a g2 a;
      F.fprintf fmt 
        "  [conseq * _ (_ : !%s.%s ==> !%s.%s : =1%%r);[ by [] | by [] | ]|@ " 
        g1 a g1 a;
      F.fprintf fmt 
        "   conseq * _ _ (_ : !%s.%s ==> !%s.%s : =1%%r);" g2 a g2 a;
      F.fprintf fmt "   [ by move=> &1 &2 [H1 H2];@ ";
      F.fprintf fmt "     (cut -> : (%s.%s{1})= false by rewrite neqF);@ " g1 a;
      F.fprintf fmt "     (cut -> : (%s.%s{2})= false by rewrite neqF)@ " g2 a;
      F.fprintf fmt "   | by [] | ] ].@ "; 
      F.fprintf fmt "%a@ " pp_cmds lossless1;
      pp_cmds fmt lossless2;
      close_pp fmt ()
    end

(* --------------------------------------------------------------------- *)
(* Certify rnd_oracle rule*)
        
let pr_random_orcl (pos, inv1, inv2) ju1 ju2 file =
  let g1,g2,open_pp, close_pp = init_same false file ju1 ju2 in
  let vcs = log_oracles file in
  let eqvc = mk_eq_vcs g1 g2 (List.map fst vcs) in
  let nvc = List.length vcs in
  let se1 = ju1.ju_se in
  let se2 = ju2.ju_se in

  let _i, ctxt = Game.get_se_octxt se1 pos in
  let _i, ctxt2 = Game.get_se_octxt se2 pos in
  let jctxt = ctxt.seoc_sec in
  let write1 = write_gcmds jctxt.sec_left in
  let writec = add_binding ctxt.seoc_avars in
  let write1c = Se.union write1 writec in
  let write2 = write_gcmds jctxt.sec_right in
  let write = Se.union write1c write2 in
  (* The proof of the oracle *)
  let ginv = f_and (mk_eq_exprs file g1 g2 write1) eqvc in
  let p1 = ctxt.seoc_oargs and p2 = ctxt2.seoc_oargs in
  let iinv = init_inv_oracle p1 p2 ginv in
  let add_info1 v1 e1 loc info = 
    add_let_info file g1 v1 e1 true loc info in
  let add_info2 v2 e2 loc info = 
    add_let_info file g2 v2 e2 false loc info in
  let add_rnd v1 v2 loc info = add_rnd_info file g1 g2 v1 v2 loc info in
  let rec aux lc1 lc2 info = 
    match lc1, lc2 with
    | [], [] -> info
    | LLet (v1,e1)::lc1, _ ->
      aux lc1 lc2 (add_info1 v1 e1 true info)
    | _, LLet (v2,e2)::lc2 ->
      aux lc1 lc2 (add_info2 v2 e2 true info)
    | LSamp(v1,(_,l1))::lc1, LSamp(v2,(_,l2))::lc2 ->
      aux lc1 lc2 (add_rnd v1 v2 l1 l2 true info) 
    | LBind _ :: _, LBind _ :: _ -> assert false (* FIXME *)
    | LGuard e1 :: lc1, LGuard e2 :: lc2 ->
      let info' = aux lc1 lc2 (add_guard file g1 g2 e1 e2 info []) in
      let tacs = 
        if info.pos1 = 0 && info.pos2 = 0 then 
          Tac (TSeqSub(If, [t_pr_if; t_id; t_aa])) :: info'.tacs 
        else
          Tac (Seq (info.pos1, info.pos2, info.invs)) ::
            TSub [info.tacs] ::
            Tac (TSeqSub(If, [t_pr_if; t_id; t_aa])) ::
            info'.tacs in
      { info' with tacs = tacs }
    | _, _ -> assert false in
  let info = 
    { loc1 = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p1;
      loc2 = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p2;
      pos1 = 0; pos2 = 0; passert1 = 0; passert2 = 0;
      tacs = [];
      invs  = iinv } in
  let info = aux ctxt.seoc_cleft ctxt2.seoc_cleft info in
  let nA = adv_name file in
  fun fmt () ->
    (* FIXME use init_same_ev as in pr_rw_oracle *)
    open_pp fmt ();
    F.fprintf fmt "conseq (_: _ ==> @[%a@]) => //.@ "
      Printer.pp_form (mk_eq_exprs file g1 g2 write);
    let len = nvc + List.length jctxt.sec_left in

    F.fprintf fmt "seq %i %i : (@[={glob A} /\\ %a@]);@ " len len
      Printer.pp_form ginv;
    F.fprintf fmt "  [ by sim | ].@ ";
    if jctxt.sec_right <> [] then begin
      F.fprintf fmt "seq %i %i : (@[={glob %s} /\\ %a@]);@ " 
        1 1 nA
        Printer.pp_form  (f_and (mk_eq_exprs file g1 g2 write1c) eqvc);
      F.fprintf fmt "  [ | by sim ].@ "
    end;

    F.fprintf fmt "call (_: @[%a@]).@ "
      Printer.pp_form ginv;
    List.iter (fun _ -> F.fprintf fmt "  by sim.@ ") ctxt.seoc_oleft;
    (* Start proof of the oracle *)
    F.fprintf fmt "  proc;sp 1 1;if;[by done | | by done].@ ";
    F.fprintf fmt "  seq 1 1 : (@[%a@]);[by sim | ].@ "
      Printer.pp_form iinv;
    F.fprintf fmt "  @[%a@]@ " pp_cmds info.tacs;
    F.fprintf fmt "  sim.@ ";
    F.fprintf fmt "  wp 1 1.@ ";
    F.fprintf fmt "  @[<hov 2>rnd@ %a@ %a.@]@ "
      (pp_inv file ~local:info.loc2 g2) inv2 (pp_inv file ~local:info.loc2 g2)
      inv1;
    F.fprintf fmt "  @[<hov 2>conseq (_: _ ==>@ %a).@]@ " 
      Printer.pp_form info.invs;
    let ty = (fst inv1).Vsym.ty in 
    F.fprintf fmt "    progress.@ ";
    F.fprintf fmt "      by algebra *.@ ";
    F.fprintf fmt "      by rewrite !%a.@ " (mu_x_def file) ty;
    F.fprintf fmt "      by apply %a.@ " (supp_def file) ty;
    F.fprintf fmt "      by algebra *.@ ";
    F.fprintf fmt "    auto.@ ";
    
    (* End proof of the oracle *)
    List.iter (fun _ -> F.fprintf fmt "  by sim.@ ") ctxt.seoc_oright;
    F.fprintf fmt "auto.";
    close_pp fmt ()

(* --------------------------------------------------------------------- *)
(* Certify rw_orcl rule *)
  
let pr_rw_orcl ((i,_oi,_j,_ootype) as op,dir) ju1 ju2 file = 
  let g1, g2, open_pp, close_pp = init_same false file ju1 ju2 in

  let vcs = log_oracles file in
  let eqvc = mk_eq_vcs g1 g2 (List.map fst vcs) in
  let nvc = List.length vcs in

  let se1 = ju1.ju_se in
  let lg, se_o = Game.get_se_octxt se1 op in
  let n1 = nvc + List.length se_o.seoc_sec.sec_left in
  let w1 = Game.write_gcmds (List.rev se_o.seoc_sec.sec_left) in
  let ev1 = f_and eqvc (mk_eq_exprs file g1 g2 w1) in
  let gc, _ = Game.get_se_ctxt se1 i in
  let w2 = Se.union w1 (Game.write_gcmd gc) in
  let ev2 = f_and eqvc (mk_eq_exprs file g1 g2 w2) in
  let nA = adv_name file in
  let pp_invA fmt ev = 
    F.fprintf fmt "={glob %s} /\\ %a" nA Printer.pp_form ev in
  let add_bind_info add_tac v info =
    let loc1 = Vsym.S.add v info.loc1 in
    let loc2 = Vsym.S.add v info.loc2 in
    let e1 = formula file [g1.mod_name] (Some "1") ~local:loc1 (Expr.mk_V v) in
    let e2 = formula file [g2.mod_name] (Some "2") ~local:loc2 (Expr.mk_V v) in
    { loc1 = loc1; 
      loc2 = loc2;
      pos1 = info.pos1 + 1; passert1 = 0;
      pos2 = info.pos2 + 1; passert2 = 0;
      tacs = add_tac info.tacs;
      invs = f_and info.invs (f_eq e1 e2) } in
  let add_let_info v info =
    add_bind_info (add_wp info.pos1 info.pos2) v info in
  let add_rnd_info v info = 
    add_bind_info add_rnd v info in
  let t_bydone = Tstring "by done" in
  let rec aux lc info = 
    match lc with
    | [] -> info
    | LLet(v,_) :: lc ->
      aux lc (add_let_info v info)
    | LSamp(v,_):: lc ->
      aux lc (add_rnd_info v info)
    | LBind _ :: _ -> assert false
    | LGuard _e :: lc ->
      let info' = aux lc info in
      let tacs = 
        if info.pos1 = 0 && info.pos2 = 0 then 
          Tac (TSeqSub(If, [t_bydone; t_id; t_bydone])) :: info'.tacs 
        else
          Tac (Seq (info.pos1, info.pos2, info.invs)) ::
            TSub [info.tacs] ::
            Tac (TSeqSub(If, [t_bydone; t_id; t_bydone])) ::
            info'.tacs in
      { info with tacs = tacs } in
  
  let p1 = se_o.seoc_oargs in
  let iinv = init_inv_oracle p1 p1 ev1 in
  let loc = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p1 in
  let info0 = 
    { loc1 = loc; loc2 = loc;
      pos1 = 0; pos2 = 0;passert1 = 0; passert2 = 0;
      tacs = []; invs  = iinv } in
  let info1 = aux se_o.seoc_cleft info0 in

  let t_end n = 
    let rec pp_intro n =
      if n = 0 then Format.sprintf "[H1 H2]" 
      else Format.sprintf "[%s H%i]" (pp_intro (n-1)) (n+2) in
    let rec pp_gen n = 
      if n =0 then ""
      else Format.sprintf "H%i %s" (n+2) (pp_gen (n-1)) in
    let s = 
      Format.sprintf "by move=> &m1 &m2 %s;move: H1 %s;try (rewrite %sH2)"
        (pp_intro n) (pp_gen n) 
        (if dir = LeftToRight then "" else "-")
     in
    Tstring s in


  let rec aux2 nend n lc info =
    match lc with
    | [] -> info.tacs @ [Tac (TSeq [Auto; (t_end nend)])]
    | LLet(v,_) :: lc ->
      aux2 nend (n+1) lc (add_let_info v info)
    | LSamp(v,_):: lc ->
      aux2 nend (n+1) lc (add_rnd_info v info)
    | LBind _ :: _ -> assert false
    | LGuard e :: lc ->
      if info.pos1 = 0 && info.pos2 = 0 then
         Tac (TSeqSub(If, [t_end nend; t_id; t_bydone]))::
         aux2 (nend+1) (n+1) lc (add_guard file g1 g2 e e info [])
      else
         Tac (Seq (info.pos1, info.pos2, info.invs)) ::
         TSub ([info.tacs; [Tac (TSeq [Skip; t_end nend])]]) ::
         Tac (TSeqSub(If, [t_end n; t_id; t_bydone]))::
         aux2 (n+1) (n+1) lc (add_guard file g1 g2 e e info []) in

  let cond = match lg with LGuard t -> t | _ -> assert false in
  let info2 = add_guard file g1 g2 cond cond info1 [] in
  let tac_end = aux2 0 0 se_o.seoc_cright info2 in 
  fun fmt () ->
    open_pp fmt ();
    F.fprintf fmt "(* Rewrite oracle *)@ ";
    F.fprintf fmt "seq %i %i : (%a); first by sim.@ " n1 n1 pp_invA ev1;
    if se_o.seoc_sec.sec_right <> [] then
      F.fprintf fmt "seq 1 1 : (%a); last by sim.@ " pp_invA ev2;
    F.fprintf fmt "call (_: %a);last by done.@ " Printer.pp_form ev1;
    (* Proof of oracles *)
    let pp_other fmt os =
      pp_list "" (fun fmt _ -> F.fprintf fmt "  by sim.@ ") fmt os in
    pp_other fmt se_o.seoc_oleft;
    F.fprintf fmt "  proc;sp 1 1;if;[ by done | | by done].@ ";
    F.fprintf fmt "  %a" pp_cmds 
      [Tac (TSeqSub (Seq(1, 1, iinv), [Auto; t_id]))];
    F.fprintf fmt "  %a@ " pp_cmds info1.tacs;
    F.fprintf fmt "  if;[by done | | by done].@ ";
    F.fprintf fmt "  @[<v>%a@]" pp_cmds tac_end;
    pp_other fmt se_o.seoc_oright;
    close_pp fmt ()

(* --------------------------------------------------------------------- *)
(* Certify assumptions *)

let split_ranges ranges c = 
  (* skip the initialisation of random variables *)
  let rc, c = 
    match ranges with
    | [] -> assert false
    | (i1,_) :: _ -> cut_n i1 c in
  let rec aux r c = 
    match r with 
    | [] -> if (c<> []) then raise Not_found; [] 
    | (i1,i2) :: r -> 
      let rc1, c0 = cut_n (i2 - i1 + 1) c in
      List.rev rc1 :: aux r c0 in
  rc, aux ranges c
  
let get_asgn1 = function
  | Iasgn ([v],e) -> v,e 
  | _ -> assert false

let get_rnd1 = function
  | Irnd([v],_,_) -> v
  | _ -> assert false

let extract_assum file ranges dir assum pft pft' = 
  let g  = game file pft.pt_ju.ju_se.se_gdef in
  let nvc = List.length (log_oracles file) in
  let ainfo = 
    try Ht.find file.assump_dec assum.Ass.ad_name 
    with Not_found -> assert false in
  let comp = match g.mod_body with 
    | Mod_def cmp -> cmp 
    | _ -> assert false in
  let comp, f = 
    match List.rev comp with 
    | MCfun f :: r -> List.rev r, f
    | _ -> assert false in
  let init_vc, c = Util.cut_n nvc (f_body f) in
  let rc,cs = split_ranges ranges c in
  let priv = 
    List.fold_left (fun s i -> let (_,v) = get_rnd1 i in Sstring.add v s)
      Sstring.empty rc in
  (* The private variables should be remove *)
  let tokeep = function
    | MCvar ((_,v),_) -> not (Sstring.mem v priv) 
    | _ -> true in
  let comp = List.filter tokeep comp in
  (* build the code for the adversary *)
  let first = ref true in
  let do_adv (asym, lr, zarg) c = 
    pp_debug "extract_assum:do_adv@.";
    let arg, _ = get_asgn1 (List.hd c) in 
    let varg = ([],"_arg") in
    let c = List.tl c in
    let retc = L.drop (List.length c - List.length lr) c in
    let retv = List.map (fun i -> fst (get_asgn1 i)) retc in
    let vres = ([],"_res") in
    let tres = mk_Prod (List.map (fun v -> v.Vsym.ty) lr) in
    let dres = vres, tres in
    let body = 
      Iasgn([arg], e_pv varg) ::
        c @ [Iasgn([vres], e_tuple (List.map e_pv retv))] in
    let body = 
      if !first then (first := false;List.rev_append init_vc body)
      else body in
     MCfun 
       { f_name = asym_to_string asym;
         f_def = Fbody {
           f_param = [varg, (fst zarg).e_ty];
           f_local = [dres];
           f_res   = Some (vres, Tzc tres);
           f_body  = body}
       } in
  let advname = top_name file ("Fadv_"^ainfo.ad_name) in 
  let fadv = 
    { mod_name = advname;
      mod_param = g.mod_param;
      mod_body = Mod_def (comp @ List.map2 do_adv assum.Ass.ad_acalls cs) } in
  add_game file `Top fadv;
  let fa = mod_name fadv.mod_name [mod_name (adv_name file) []] in
  let a1 = mod_name ainfo.ad_cmd1.mod_name [fa] in
  let a2 = mod_name ainfo.ad_cmd2.mod_name [fa] in
  let pr = extract_pr file mem pft.pt_ju in
  let pr' = extract_pr file mem pft'.pt_ju in
  let pra1 = Fpr((a1,"main"), mem, [], Fv(([],"res"),None)) in
  let pra2 = Fpr((a2,"main"), mem, [], Fv(([],"res"),None)) in
  let pra, pra' = if dir = LeftToRight then pra1, pra2 else pra2, pra1 in
  let _nA = adv_name file in

  let abs = Fabs (f_rsub pra1 pra2) in

  let proof fmt () =
    let pp_form = Printer.pp_form in
    F.fprintf fmt "@[<v>(* Assumption decitional *)@ ";
    F.fprintf fmt "move=> &m.@ ";
    F.fprintf fmt "cut -> : %a = %a.@ " pp_form pr pp_form pra;
    F.fprintf fmt "+ byequiv (_: _ ==> _) => //;proc;inline *;do!(sim;auto).@ ";
    F.fprintf fmt "cut -> : %a = %a.@ " pp_form pr' pp_form pra';
    F.fprintf fmt "+ byequiv (_: _ ==> _) => //;proc;inline *;do!(sim;auto).@ ";
    F.fprintf fmt "by %s.@]" 
      (if dir = LeftToRight then "done" else "rewrite ZooUtil.abs_minusC") in 
  let lemma = 
    add_pr_lemma ~pinfo:pft.pt_info file 
      (mk_cmp (Fabs (f_rsub pr pr')) cmp_eq abs)
      (Some proof) in
  lemma, pr, abs 
    
let extract_assum_comp file ranges assum pft =
  let g  = game file pft.pt_ju.ju_se.se_gdef in
  let nvc = List.length (log_oracles file) in

  let ainfo = 
    try Ht.find file.assump_comp assum.Ass.ac_name 
    with Not_found -> assert false in
 
  let comp = match g.mod_body with 
    | Mod_def cmp -> cmp 
    | _ -> assert false in
  let comp, f = 
    match List.rev comp with 
    | MCfun f :: r -> List.rev r, f
    | _ -> assert false in
  let init_vc, c = Util.cut_n nvc (f_body f) in
  let rc,cs = split_ranges ranges c in
 
  let priv = 
    List.fold_left (fun s i -> let (_,v) = get_rnd1 i in Sstring.add v s)
      Sstring.empty rc in
  (* The private variables should be remove *)
  let tokeep = function
    | MCvar ((_,v),_) -> not (Sstring.mem v priv) 
    | _ -> true in
  let comp = List.filter tokeep comp in
  (* build the code for the adversary *)
  let first = ref true in
  let do_adv (asym, lr, zarg) c = 
    let arg, _ = get_asgn1 (List.hd c) in 
    let varg = ([],"_arg") in
    let c = List.tl c in
    let retc = L.drop (List.length c - List.length lr) c in
    let retv = List.map (fun i -> fst (get_asgn1 i)) retc in
    let vres = ([],"_res") in
    let tres = mk_Prod (List.map (fun v -> v.Vsym.ty) lr) in
    let dres = vres, tres in
    let body = 
      Iasgn([arg], e_pv varg) ::
        c @ [Iasgn([vres], e_tuple (List.map e_pv retv))] in
    let body = 
      if !first then (first := false;List.rev_append init_vc body)
      else body in
     MCfun 
       { f_name = asym_to_string asym;
         f_def = Fbody {
           f_param = [varg, zarg.e_ty];
           f_local = [dres];
           f_res   = Some (vres, Tzc tres);
           f_body  = body}
       } in
  let advname = top_name file ("Fadv_"^ainfo.ac_name) in 
  let fadv = 
    { mod_name = advname;
      mod_param = g.mod_param;
      mod_body = Mod_def (comp @ List.map2 do_adv assum.Ass.ac_acalls cs) } in
  
  add_game file `Top fadv;

  let fa = mod_name fadv.mod_name [mod_name (adv_name file) []] in
  let a = mod_name ainfo.ac_cmd.mod_name [fa] in
  let pr = extract_pr file mem pft.pt_ju in
  let pra = Fpr((a,"main"), mem, [], Fv(([],"res"),None)) in
  let nA = adv_name file in
  let proof_ass fmt () =
    F.fprintf fmt "(* Assumption computational *)@ ";
    F.fprintf fmt 
      "@[<v>intros &m; byequiv (_: @[={glob %s} ==>@ _@]) => //.@ " nA;
    F.fprintf fmt "by proc; inline *; wp => /=; do !(sim;auto).@]" in
  let lemma = 
    add_pr_lemma ~pinfo:pft.pt_info file (mk_cmp pr cmp_eq pra) (Some proof_ass) in
  lemma, pr, cmp_eq, pra

let rec skip_conv pft = 
  match pft.pt_rule with
  | Rconv -> skip_conv (List.hd pft.pt_children)
  | _ -> pft

let skip_swap pft = 
  let rec aux sw pft = 
    match pft.pt_rule with
    | Rswap(p,i) -> aux ((p,i)::sw) (List.hd pft.pt_children)
    | _ -> List.rev sw, pft in
  aux [] pft

(* --------------------------------------------------------------------- *)
(* Certify rindep *)

let bound_rnd_indep file pos ju = 
  let ty,l = 
    match List.rev ju.ju_se.se_gdef with GSamp(_,d) :: _ -> d | _ -> assert false in
  let size, lemma =
    match ty.ty_node with
    | BS lv -> f_2pow (bs_length file lv), lvar_mod file lv ^".Dword.mu_x_def"
    | Bool  -> f_2  , "Bool.Dbool.mu_x_def"
    | G _   -> f_Fq,  assert false (* FIXME *)
    | Fq    -> f_Fq,  "FDistr.mu_x_def_in"
    | _     -> assert false (* FIXME *) in
  let isize = f_rinv (Frofi size) in
  assert (l = []);
  let evs = destr_Land_nofail ju.ju_se.se_ev in
  let ev = List.nth evs pos in
  if is_Eq ev then isize, ev, lemma 
  else assert false 

let extract_rnd_indep file side pos ju pinfo = 
  let g = game file ~pinfo ju.ju_se.se_gdef in
  let pr = extract_pr file mem ju in
  let bound, ev, lemma = bound_rnd_indep file pos ju in
  let proof fmt () =
    F.fprintf fmt "(* Random indep *)@ ";

    if Game.has_assert ju.ju_se.se_gdef then
      F.fprintf fmt "@[<v>intros &m; byphoare (_ : _ ==> %a) => //.@ "
        Printer.pp_form (formula file [g.mod_name] None ev)
    else
      F.fprintf fmt "@[<v>intros &m; byphoare (_ : ) => //.@ ";
      
    if is_Eq ev then
      let e1,e2 = destr_Eq ev in
      let e = if side then e2 else e1 in
      F.fprintf fmt 
        "proc; rnd ((=) (%a));@   conseq (_ : _ ==> true); last by [].@ "
        Printer.pp_form (formula file [g.mod_name] None e);
      F.fprintf fmt "progress.@ ";
      F.fprintf fmt "apply Real.eq_le;apply %s." lemma
    else assert false;
    F.fprintf fmt "@]" in
  let lemma = add_pr_lemma ~pinfo file (mk_cmp pr cmp_le bound) (Some proof) in
  lemma, pr, cmp_le, bound

(* --------------------------------------------------------------------- *)
(* Certify except *)

let extract_except file pos _l pft pft' = 
  let ju = pft.pt_ju in
  let ju' = pft'.pt_ju in
  let pr = extract_pr file mem ju in
  let pr' = extract_pr file mem ju' in
  let g = game file pft.pt_ju.ju_se.se_gdef in 
  let g' = game file pft'.pt_ju.ju_se.se_gdef in
  let vcs = log_oracles file in
  let nvc = List.length vcs in
  let npos = pos + nvc in
  let side, adv =
    let comp = match g.mod_body with 
      | Mod_def cmp -> cmp 
      | _ -> assert false in
    let comp, f = 
      match List.rev comp with 
      | MCfun f :: r -> List.rev r, f
      | _ -> assert false in
   
    let side, x, ex =
      match List.nth ju.ju_se.se_gdef pos, List.nth ju'.ju_se.se_gdef pos with 
      | GSamp(x,(_ty,[])), GSamp(x',(_ty',[e])) -> 
        assert (Vsym.equal x x'); (* FIXME: check ty *)
        `LeftToRight, x, e
      | GSamp(x,(_ty,[e])), GSamp(x',(_ty',[])) ->
        assert (Vsym.equal x x');
        `RightToLeft, x, e
      | _, _ -> assert false in
    let hd,_,tl = Util.split_n npos (f_body f) in
    let a1 = 
      let res = ([], "_res") in
      let dres = res, mk_Fq in
      let ex = expression file ex in
      { f_name = "a1";
        f_def = Fbody {
        f_param = [];
        f_local = [dres];
        f_res   = Some ( res, Tzc mk_Fq);
        f_body  = List.rev_append hd [Iasgn([res],ex)] } } in
    let a2 = 
      let arg = ([], "_arg") in
      let darg = arg, mk_Fq in
      {
        f_name = "a2";
        f_def = Fbody {
        f_param = [darg];
        f_local = [];
        f_res   = None;
        f_body  = Iasgn([pvar [] x], Epv arg)::tl } } in
    let advname = top_name file ("SDadv") in 
    side, { mod_name = advname;
      mod_param = [];
      mod_body = Mod_def (comp @ [MCfun a1; MCfun a2]) } in
  add_game file `Local adv;
  let clone_info = {
    ci_local = true;
    ci_import = true;
    ci_from   = "SDField";
    ci_as     = top_name file "SDField_";
    ci_with   = [];
    ci_proof  = []; 
  } in
  add_local file (Cclone clone_info);
  let eps = f_rinv (Frofi f_Fq) in
  let bound = f_rinv (Frofi f_Fq) in
  let g2 = if side = `LeftToRight then g' else g in


  let _mk_eqs g fv = 
    let mk_eq e = 
      f_eq (formula file [g] (Some "1") e) 
        (formula file [adv.mod_name] (Some "2") e) in
    match Se.elements fv with
    | [] -> f_true
    | e :: es -> List.fold_left (fun f e -> f_and f (mk_eq e)) (mk_eq e) es in
  let fv = e_vars ju.ju_se.se_ev in
  let flocal = flocal_ev ju.ju_se.se_ev in
  let flocal = Vsym.S.fold (fun v s -> Se.add (mk_V v) s) flocal Se.empty in
  let fv = Se.diff fv flocal in
  let _nA = adv_name file in
  let _eqvc = mk_eq_vcs g2 adv (List.map fst vcs) in
  let _form = extract_ev file [] None ju.ju_se in
  let proof fmt () = 
    F.fprintf fmt "intros &m.@ ";
    F.fprintf fmt "pose EV := fun (g:glob %s) (u:unit),@ " adv.mod_name;
    List.iter (fun e -> 
      let v = destr_V e in
      let s = snd (pvar [] v) in
      F.fprintf fmt "  let %s = g.`%s.%s in@ "
        s adv.mod_name (exclude_private s)) (Se.elements fv);
    fixme "undefined"
    (*
    List.iter (function
      | (_,Oracle.RO _) -> assert false
      | (_,Oracle.O o) ->
        let s = snd (log_oracle [] o) in
        F.fprintf fmt "  let %s = g.`%s.%s in@ "
          s adv.mod_name (exclude_private s)) (Event.binding ju.ju_se.se_ev);
    F.fprintf fmt "  @[%a@].@ "Printer.pp_form form;
    F.fprintf fmt "cut H1 := %s.SD1_conseq_abs %s &m EV.@ " 
      clone_info.ci_as adv.mod_name;
    F.fprintf fmt "apply (real_le_trans _ _ _ _ H1)=>{H1}.@ ";
    F.fprintf fmt "apply real_eq_le%s.@ "
      (if side = `LeftToRight then "" 
       else ";rewrite ZooUtil.abs_minusC");
    F.fprintf fmt "congr;congr;simplify EV.@ ";
    F.fprintf fmt 
      "+ byequiv (_ : ={glob %s} ==> _);[ proc;inline *;sim | by [] | by [] ].@ "
      nA;
    F.fprintf fmt 
      "byequiv (_ : ={glob %s} ==> _);[ proc;inline * | by [] | by [] ].@ "
      nA;
    F.fprintf fmt "seq %i %i :(={glob %s} /\\ %a);sim;auto." 
      npos (npos + 1) nA
      Printer.pp_form 
        (f_and eqvc (mk_eqs g2.mod_name 
                       (write_gcmds (Util.take pos ju.ju_se.se_gdef))))
     *)
  in
  let concl = mk_cmp (Fabs (f_rsub pr pr')) cmp_le bound in
    
  
  let lemma = add_pr_lemma ~pinfo:pft.pt_info file concl (Some proof) in
  lemma, eps

(* --------------------------------------------------------------------- *)
(* Certify guess *)
  
let default_proof ?(warning=true) file mem s pft = 
  if warning then F.eprintf "WARNING rule %s not extracted@." s;
  let pr,full,_ = extract_full_pr ~local:`Top file mem pft.pt_ju in
  let lemma = add_pr_lemma ~pinfo:pft.pt_info file (mk_cmp full cmp_eq full) 
    (Some (fun fmt () -> 
      F.fprintf fmt "(* WARNING rule %s not extracted*)@ " s;
      F.fprintf fmt "trivial.")) in
  lemma, pr, cmp_eq, full

let pp_cintros fmt hs =
  match hs with
  | [] -> assert false
  | [h] -> F.fprintf fmt "%s" h
  | hs -> 
    let rec aux fmt hs =
      match hs with
      | [] -> ()
      | [h] ->  F.fprintf fmt "%s" h
      | h::hs -> F.fprintf fmt "[%s %a]" h aux hs in
    F.fprintf fmt "@[<hov>%a@]" aux hs 

let destr_pr pr = 
  match pr with
  | Fpr(f,m,a,ev) -> f,m,a,ev 
  | _ -> assert false 

let build_subst_section file auxname infob secb aA =
  let ms = 
    let ms = 
      List.fold_left (fun ms s ->
        Mstring.add s {mn = Format.sprintf "%s.%s" auxname s;ma = []} ms) 
        Mstring.empty secb.tosubst in
    Mstring.add infob.adv_name 
      {mn = aA ;ma = [adv_mod file]} ms in
  let section = get_section file in
  Mstring.iter (fun _ m -> section.tosubst <- m.mn :: section.tosubst) ms;
  (* FIXME add the ms in tosubst of the current section *)
  let mc = 
    Osym.H.fold (fun o _oi mc -> 
      Mstring.add (q_oracle_i infob o) (Fcnst (q_oracle file o)) mc)
      infob.adv_g.oinfo Mstring.empty in
  ms, mc

let proof_guess 
    file newasym pft auxname infob secb conclusion prb cmpb boundb = 
  (* clone the section GUESS *)
  let info = adv_info file in
  add_restr_info file secb.section_name infob;
  let clone_G = {
    ci_local  = false;   ci_import = false;
    ci_from   = auxname; ci_as     = auxname;
    ci_with   = 
      Osym.H.fold (fun o _oi w -> 
        CWop(q_oracle_i infob o, None, Ecnst (q_oracle file o)) :: w)
        infob.adv_g.oinfo [];
    ci_proof   = 
      Osym.H.fold (fun o _oi p -> 
        let ax = q_oracle_i infob o ^ "_pos" in
        let pr = Format.sprintf "apply %s_pos"  (q_oracle file o) in
        (ax, fun fmt () -> F.fprintf fmt "%s" pr)::p )
        infob.adv_g.oinfo []; } in
  add_top file (Cclone clone_G); 
    (* build the adversary for GUESS *)
  let vs, orcl = fixme "undefined" (*
    match Event.binding pft.pt_ju.ju_se.se_ev with
    | [vs,Oracle.O o] -> vs, o
    | _ -> assert false
    *)
  in 
  let log = log_oracle [] orcl in
  let orcl_name = "o" ^ Osym.to_string orcl in
  let arg = ([],"_arg") in
  let res = ([],"_res") in
  let mO = {mn="O";ma=[]} in
  let wrap_def =
    { f_param = [arg, orcl.Osym.dom];
      f_local = [res,orcl.Osym.codom];
      f_res   = Some (res, Tzc orcl.Osym.codom);
      f_body  = [
        Iasgn([res], expression file (init_res_expr orcl.Osym.codom));
        Iif(e_lt (e_length (e_pv log)) (Ecnst (q_oracle file orcl)),
            [Iasgn([log],e_cons (e_pv arg) (e_pv log));
             Icall([res],(mO,orcl_name),[e_pv arg]);],
            [])
      ]
    } in
  let orcls = 
    Osym.H.fold (fun o _ l ->
      let name = "o" ^ Osym.to_string o in
      let body = 
        if name = orcl_name then Fbody wrap_def
        else Falias (mO,name) in
      MCfun {f_name = name; f_def = body } :: l) infob.adv_g.oinfo [] in
  let guess_def = 
    let i = ([],"__i__") in
    { f_param = [];
      f_local = [res,newasym.Asym.codom; i, mk_Int];
      f_res   = Some (res, Tzc newasym.Asym.codom);
      f_body  = [
        Irnd_int ([i], e_int 0, e_sub (Ecnst (q_oracle file orcl)) (e_int 1));
        Iasgn([res], 
              Eapp (Ostr "oget", [Eapp (Ostr "nth", [e_pv log; e_pv i])]))
      ]
    } in
  let mA = {mn="A";ma=[]} in
  let advs = 
    Asym.H.fold (fun a os l ->
      let name = asym_to_string a in
      let body = 
        if Asym.equal a newasym then Fbody guess_def
        else if List.exists (Osym.equal orcl) os then
          Fbody { f_param = [arg, a.Asym.dom];
                  f_local = [res, a.Asym.codom];
                  f_res   = Some (res, Tzc a.Asym.codom);
                  f_body  = [
                    Iasgn([log], Ecnst "[]");
                    Icall([res],(mA,name),[e_pv arg]) ] }
        else Falias (mA,name) in
      MCfun {f_name = name; f_def = body } :: l) infob.adv_g.ainfo [] in
  let adv_gl = 
    { mod_name  = top_name file "AG";
      mod_param = [("A",info.adv_ty); ("O",info.adv_oty)];
      mod_body  = Mod_def ([ 
        MCvar (log_oracle [] orcl, List orcl.Osym.dom); 
        MCmod {
          mod_name = "O1"; mod_param = [];
          mod_body = Mod_def orcls; };
        MCmod {
          mod_name = "A"; mod_param = [];
          mod_body = Mod_alias({mn = "A"; ma = [{mn="O1";ma = []}]}); } ] @
                              advs) } in
  add_game file `Top adv_gl;
    (* local clone *)    
  let auxname_Loc = auxname^"_Loc" in
  let clone_GL = {
    ci_local  = true; ci_import = true;
    ci_from   = auxname^".Local"; ci_as     = auxname_Loc;
    ci_with   = []; ci_proof  = []; } in
  add_local file (Cclone clone_GL); 
    (* clone Guess theory *)
  let guessL = top_name file "GuessL" in
  let clone_GL = {
    ci_local  = true;
    ci_import = true;
    ci_from   = "Guess";
    ci_as     = guessL;
    ci_with   = [CWtype("output", orcl.Osym.dom);
                 CWop("q",None, Ecnst (q_oracle file orcl))];
    ci_proof  = [("q_pos", fun fmt _ -> F.fprintf fmt "smt")];
  } in
  add_local file (Cclone clone_GL); 
  
    (* build the adversary for  GuessL *)
  let g = game file pft.pt_ju.ju_se.se_gdef in
  let aGL = {
    mod_name = top_name file "AGL";
    mod_param = [];
    mod_body = Mod_def [
      MCmod { mod_name = g.mod_name;
              mod_param = [];
              mod_body = Mod_alias {mn = g.mod_name; 
                                    ma = [{mn=info.adv_name;ma=[]}]}};
      MCfun {
        f_name = "main";
        f_def = Fbody {
          f_param = [];
          f_local = [];
          f_res =Some(log_oracle [g.mod_name] orcl, List orcl.Osym.dom);
          f_body = [Icall([], ({mn=g.mod_name;ma=[]},"main"), [])]
        }
      }
    ]
  } in
  add_game file `Local aGL;
  let ms, mc = build_subst_section file auxname infob secb adv_gl.mod_name in
  let boundb = subst_f ms mc boundb in
  let bound = f_rmul (Frofi (Fcnst (q_oracle file orcl))) boundb in
  let pr = extract_pr file mem pft.pt_ju in
  let concl = (mk_cmp pr cmp_le bound) in
    (* build the proof *)
  let ninstr = List.length pft.pt_ju.ju_se.se_gdef in
  let vcs = log_oracles file in
  let nvc = List.length vcs in
  let nAGL = aGL.mod_name in
  let nG   = g.mod_name in
  let nA   = info.adv_name in
  let logO = snd (log_oracle [] orcl) in
  let qO   = q_oracle file orcl in
  

  let proof fmt () =
    F.fprintf fmt "(* Guess *)@ ";
    F.fprintf fmt "move=> &m.@ ";
    let pp_E fmt ev =
      let fv = ExprUtils.e_vars ev in
      let fv = List.fold_left (fun s v -> Se.remove (mk_V v) s) fv vs in
      let fv = Se.elements fv in
      let f = formula file [] None ev in
      let pp_let_quant fmt vs = 
        List.iteri (fun i v ->
          F.fprintf fmt "let %s = __elem__.`%i in@ "
            (snd (pvar [] v)) (i+1)) vs in
      let pp_let fmt v = 
        let v = Vsym.to_string (destr_V v) in
        F.fprintf fmt "let %s = gl.`%s.%s in@ " v nG (exclude_private v) in
      F.fprintf fmt "(@[<v>fun (gl:glob %s) (__elem__:%a),@   @[<v>%a%a @[<hov>%a@]@]@])"
        nAGL (Printer.pp_type file) orcl.Osym.dom
        (pp_list "" pp_let) fv 
        pp_let_quant vs
        Printer.pp_form f in
    F.fprintf fmt "pose __F__ := %a.@ " pp_E pft.pt_ju.ju_se.se_ev;
    F.fprintf fmt 
      "apply (Real.Trans _ (Pr[%s.main() @@ &%s :any (__F__ (glob %s)) res])).@ " 
      nAGL mem nAGL;
    F.fprintf fmt 
      "+ byequiv (_: _ ==> ={glob %s, glob %s} /\\ res{2} = %s.%s{1}) => //.@ "
      nA nG nG logO;
    F.fprintf fmt "  by proc;inline %s.%s.main;sim.@ " nAGL nG;
    F.fprintf fmt "cut H1 := %s.conclusion %s _ &m __F__.@ " guessL nAGL;
    F.fprintf fmt "+ clear __F__; proc;inline %s(%s).main.@ " nG nA;
    let pos_log = Util.find_at (fun ((_,s),_) -> s = logO) vcs + 1 in
    F.fprintf fmt "  swap %i %i.@ " pos_log (ninstr - 1 + nvc - pos_log);
    F.fprintf fmt "  call (_ : `|%s.%s| <= %s) => /=.@ " nG logO qO;
    F.fprintf fmt "  + proc; sp 1;if => //.@ ";
    F.fprintf fmt "    seq 1 : (`|%s.%s| <= %s);first by auto;progress;smt.@ "
      nG logO qO;
    F.fprintf fmt "    conseq * (_ : _ ==> true) => //.@ ";
    F.fprintf fmt "  wp %i; conseq (_: _ ==> true) => //.@ "
      (nvc - 1 + ninstr - 1); 
    F.fprintf fmt "  progress;simplify List.\"`|_|\";smt.@ ";
    F.fprintf fmt "apply (Real.Trans _ _ _ H1)=> {H1};apply real_mulleMl. clear __F__;smt.@ ";
    F.fprintf fmt "cut H2 := %s.%s (<:%s(%s)) %a &%s.@ "
      auxname_Loc conclusion adv_gl.mod_name nA 
      (pp_list " " (fun fmt _ -> F.fprintf fmt "_")) infob.adv_ll
      mem;
    let advs = Asym.H.fold (fun a os l -> (a,os)::l) infob.adv_g.ainfo [] in
    List.iter (fun (a,os) ->
      if Asym.equal a newasym then
        F.fprintf fmt "+ move=> {__F__} O__; proc;auto;progress;smt.@ "
      else begin 
        let pp_o_ll fmt o = F.fprintf fmt "H%s_ll" (Osym.to_string o) in
        F.fprintf fmt "+ move=> {__F__} O__ %a.@ "
          (pp_list " " pp_o_ll) os;
        if List.exists (Osym.equal orcl) os then begin
          F.fprintf fmt 
            "  proc;call (a%s_ll (<:%s(%s, O__).O1) _);last by auto.@ "
            (Asym.to_string a) adv_gl.mod_name nA;
          List.iter (fun o ->
            if Osym.equal o orcl then
              F.fprintf fmt "  proc;sp 1;if => //;call %a;auto.@ "
                pp_o_ll o 
            else
              F.fprintf fmt "  apply %a.@ " pp_o_ll o) os
        end
        else
          F.fprintf fmt "  apply (a%s_ll (<:%s(%s, O__).O1) _). %a@ "
            (Asym.to_string a) adv_gl.mod_name nA
            (pp_list " " (fun fmt o -> F.fprintf fmt "apply %a." pp_o_ll o))
            os 
      end) advs;
    if cmpb = cmp_eq then begin
      F.fprintf fmt "cut H2' := Real.eq_le _ _ H2.@ ";
      F.fprintf fmt "apply (Real.Trans _ _ _ _ H2')=> {H2' H2}.@ ";
    end else
      F.fprintf fmt "apply (Real.Trans _ _ _ _ H2)=> {H2}.@ ";
    F.fprintf fmt 
      "byequiv (_: _ ==> _) => //;proc;simplify __F__ => { __F__ }.@ ";
    let size1 = nvc + ninstr in
    F.fprintf fmt 
      "inline *. swap{1} %i -1. wp %i %i. rnd.@ "
      (size1 + 2) (size1 + 1) (size1 + 4);
    let gcmd, call = 
      let c = List.rev pft.pt_ju.ju_se.se_gdef in
      List.rev (List.tl c), List.hd c in
    let gv1 = write_gcmds gcmd in
    let wc  = write_gcmds  pft.pt_ju.ju_se.se_gdef in
     (* FIXME : I assume that the call corresponding to orcl is at 
        the last position *)
    let os = (* FIXME: for hybrid equality of glob hybrid *)
      match call with
      | GCall(_, _, _, os) -> os
      | _ -> assert false in
    let eqglob = Feqglob nA in
    let nG' = let (m,_),_,_,_ = destr_pr prb in m.mn in
    let eqlog  = 
      f_eq (Fv(([nG'],logO),Some "2")) (Fv (([adv_gl.mod_name],logO),Some "2")) in
    let eq_gv1 = mk_eq_exprs_p file nG nG' gv1 in
    let eq_wc = mk_eq_exprs_p file nG nG' wc in
    let vcs = List.map (fun ((_,v),_) -> v) vcs in
    let log_pos = (Util.find_at ((=) logO) vcs) + 1 in
    let eq_vcs  = mk_eq_vcs_p [nG] [nG'] vcs in
    F.fprintf fmt "conseq (_ : _ ==> %a) => //.@ "
      Printer.pp_form (f_ands [eqglob; eqlog; eq_wc; eq_vcs]);
    F.fprintf fmt "wp %i %i.@ " size1 (size1 + 2);
    F.fprintf fmt "call (_: %a).@ "
      Printer.pp_form (f_ands [eqlog; eq_gv1; eq_vcs]);
    List.iter (fun (o,vs,_) ->
      if Osym.equal o orcl then begin
        F.fprintf fmt "+ proc;sp 1 1;inline *;if => //.@ ";
        F.fprintf fmt "  rcondt{2} 4;first by auto.@ ";
        F.fprintf fmt 
          "  seq 1 4 : (@[<hov>%a /\\@ _res{1} = _res0{2} /\\@ ={%a}@]);@   first by auto.@ "
          Printer.pp_form (f_ands [eqlog;eq_gv1; eq_vcs])
          (pp_list ", " (fun fmt v -> F.fprintf fmt "%s" (snd (pvar [] v))))
          vs;
        F.fprintf fmt "  conseq * (_: _ ==> ={_res}) => //;sim.@ ";
      end
      else
        F.fprintf fmt "+ conseq* (_: _ ==> %a) => //;sim.@ "
          Printer.pp_form (f_ands [eq_gv1; eq_vcs])) os;
    
    F.fprintf fmt "swap %i %i; wp %i %i.@ " 
      log_pos (ninstr + nvc -2)  (ninstr + nvc -2) (ninstr + nvc -2);
    
    F.fprintf fmt "sim : (%a) => //.@ "
      Printer.pp_form 
      (f_ands [eqglob; eq_gv1; 
               mk_eq_vcs_p [nG] [nG'] (List.filter ((<>) logO) vcs)])
  in
  proof, concl, pr, bound 

(* --------------------------------------------------------------------- *)
(* Certify find *)

let proof_find 
    file newasym pft auxname infob secb conclusion prb cmpb boundb (bd,f) = 
  (* clone the section FIND *)
  let info = adv_info file in
  add_restr_info file secb.section_name infob;
  let clone_G = {
    ci_local  = false;   ci_import = false;
    ci_from   = auxname; ci_as     = auxname;
    ci_with   = 
      Osym.H.fold (fun o _oi w -> 
        CWop(q_oracle_i infob o, None, Ecnst (q_oracle file o)) :: w)
        infob.adv_g.oinfo [];
    ci_proof   = 
      Osym.H.fold (fun o _oi p -> 
        let ax = q_oracle_i infob o ^ "_pos" in
        let pr = Format.sprintf "apply %s_pos"  (q_oracle file o) in
        (ax, fun fmt () -> F.fprintf fmt "%s" pr)::p )
        infob.adv_g.oinfo []; } in
  add_top file (Cclone clone_G); 
    (* build the adversary for FIND *)
  let vs, orcl = fixme "undefined" (*
    match Event.binding pft.pt_ju.ju_se.se_ev with
    | [vs,Oracle.O o] -> vs, o
    | _ -> assert false *)
  in 
  let log = log_oracle [] orcl in
  let orcl_name = "o" ^ Osym.to_string orcl in
  let arg = ([],"_arg") in
  let res = ([],"_res") in
  let mO = {mn="O";ma=[]} in
  let elem = ([],"__elem__") in
  let wrap_def =
    { f_param = [arg, orcl.Osym.dom];
      f_local = [res,orcl.Osym.codom];
      f_res   = Some (res, Tzc orcl.Osym.codom);
      f_body  = [
        Iasgn([res], expression file (init_res_expr orcl.Osym.codom));
        Iif(e_lt (e_length (e_pv log)) (Ecnst (q_oracle file orcl)),
            [Iasgn([log],e_cons (e_pv arg) (e_pv log));
             Icall([res],(mO,orcl_name),[e_pv arg]);],
            [])
      ]
    } in
  let orcls = 
    Osym.H.fold (fun o _ l ->
      let name = "o" ^ Osym.to_string o in
      let body = 
        if name = orcl_name then Fbody wrap_def
        else Falias (mO,name) in
      MCfun {f_name = name; f_def = body } :: l) infob.adv_g.oinfo [] in

  let guess_def = 
    let lets = List.mapi (fun i v -> pvar[] v, (i+1)) vs in
    let eelem = e_pv elem in
    let body = 
      List.fold_right (fun (v,i) e -> Elet([v], Eproj(i,eelem), e)) 
        lets (expression file f) in
    let f = Efun([elem, orcl.Osym.dom], body) in
    { f_param = List.map (fun v -> pvar [] v, v.Vsym.ty) bd;
      f_local = [res,orcl.Osym.dom];
      f_res   = Some (res, Tzc orcl.Osym.dom);
      f_body  = [
        Iasgn([res], 
              Eapp (Ostr "oget", [Eapp (Ostr "find", [f; e_pv log])]))
      ]
    } in
  let mA = {mn="A";ma=[]} in
  let advs = 
    Asym.H.fold (fun a os l ->
      let name = asym_to_string a in
      let body = 
        if Asym.equal a newasym then Fbody guess_def
        else if List.exists (Osym.equal orcl) os then
          Fbody { f_param = [arg, a.Asym.dom];
                  f_local = [res, a.Asym.codom];
                  f_res   = Some (res, Tzc a.Asym.codom);
                  f_body  = [
                    Iasgn([log], Ecnst "[]");
                    Icall([res],(mA,name),[e_pv arg]) ] }
        else Falias (mA,name) in
      MCfun {f_name = name; f_def = body } :: l) infob.adv_g.ainfo [] in
  let adv_gl = 
    { mod_name  = top_name file "AF";
      mod_param = [("A",info.adv_ty); ("O",info.adv_oty)];
      mod_body  = Mod_def ([ 
        MCvar (log_oracle [] orcl, List orcl.Osym.dom); 
        MCmod {
          mod_name = "O1"; mod_param = [];
          mod_body = Mod_def orcls; };
        MCmod {
          mod_name = "A"; mod_param = [];
          mod_body = Mod_alias({mn = "A"; ma = [{mn="O1";ma = []}]}); } ] @
                              advs) } in
  add_game file `Top adv_gl;
    (* local clone *)    
  let auxname_Loc = auxname^"_Loc" in
  let clone_GL = {
    ci_local  = true; ci_import = true;
    ci_from   = auxname^".Local"; ci_as     = auxname_Loc;
    ci_with   = []; ci_proof  = []; } in
  add_local file (Cclone clone_GL); 

  let ms, mc = build_subst_section file auxname infob secb adv_gl.mod_name in
  let boundb = subst_f ms mc boundb in
  let bound = boundb in 
  let pr = extract_pr file mem pft.pt_ju in
  let concl = (mk_cmp pr cmp_le bound) in
  (* build the proof *)
  let ninstr = List.length pft.pt_ju.ju_se.se_gdef in
  let vcs = log_oracles file in
  let nvc = List.length vcs in
  let g = game file pft.pt_ju.ju_se.se_gdef in
  let nG   = g.mod_name in
  let nA   = info.adv_name in
  let logO = snd (log_oracle [] orcl) in
  let proof fmt () =
    F.fprintf fmt "(* Find *)@ ";
    F.fprintf fmt "move=> &m.@ ";
    F.fprintf fmt "cut H1 := %s.%s (<:%s(%s)) %a &%s.@ "
      auxname_Loc conclusion adv_gl.mod_name nA 
      (pp_list " " (fun fmt _ -> F.fprintf fmt "_")) infob.adv_ll
      mem;
    let advs = Asym.H.fold (fun a os l -> (a,os)::l) infob.adv_g.ainfo [] in
    List.iter (fun (a,os) ->
      if Asym.equal a newasym then
        F.fprintf fmt "+ move=> O__; proc;auto;progress;smt.@ "
      else begin 
        let pp_o_ll fmt o = F.fprintf fmt "H%s_ll" (Osym.to_string o) in
        F.fprintf fmt "+ move=> O__ %a.@ "
          (pp_list " " pp_o_ll) os;
        if List.exists (Osym.equal orcl) os then begin
          F.fprintf fmt 
            "  proc;call (a%s_ll (<:%s(%s, O__).O1) _);last by auto.@ "
            (Asym.to_string a) adv_gl.mod_name nA;
          List.iter (fun o ->
            if Osym.equal o orcl then
              F.fprintf fmt "  proc;sp 1;if => //;call %a;auto.@ "
                pp_o_ll o 
            else
              F.fprintf fmt "  apply %a.@ " pp_o_ll o) os
        end
        else
          F.fprintf fmt "  apply (a%s_ll (<:%s(%s, O__).O1) _). %a@ "
            (Asym.to_string a) adv_gl.mod_name nA
            (pp_list " " (fun fmt o -> F.fprintf fmt "apply %a." pp_o_ll o))
            os 
      end) advs;
    if cmpb = cmp_eq then begin
      F.fprintf fmt "cut H1' := Real.eq_le _ _ H1.@ ";
      F.fprintf fmt "apply (Real.Trans _ _ _ _ H1')=> {H1' H1}.@ ";
    end else
      F.fprintf fmt "apply (Real.Trans _ _ _ _ H1)=> {H1}.@ ";
    let size1 = nvc + ninstr in
    F.fprintf fmt 
      "byequiv (_: _ ==> _) => //;proc;inline *;wp %i %i.@ "
      size1 (size1 + 3);
    let wv = write_gcmds pft.pt_ju.ju_se.se_gdef in
    let nG' = let (m,_),_,_,_ = destr_pr prb in m.mn in
    let eqlog  = 
      f_eq (Fv(([nG'],logO),Some "2")) (Fv (([adv_gl.mod_name],logO),Some "2")) in
    let vcs = List.map (fun ((_,v),_) -> v) vcs in
    let log_pos = (Util.find_at ((=) logO) vcs) + 1 in
    let eq_vcs  = mk_eq_vcs_p [nG] [nG'] vcs in
    let eq_wv = mk_eq_exprs_p file nG nG' wv in
    F.fprintf fmt "conseq (_: _ ==> %a)=> //.@ "
      Printer.pp_form (f_ands [eqlog;eq_vcs;eq_wv]);
    F.fprintf fmt "+ progress [-split]; by cut := any_find _ _ H.@ ";
    F.fprintf fmt "wp %i %i.@ " size1 (size1+2);
    let gcmd, call = 
      let c = List.rev pft.pt_ju.ju_se.se_gdef in
      List.rev (List.tl c), List.hd c in
    let gv1 = write_gcmds gcmd in
     (* FIXME : I assume that the call correspondint to orcl is at 
        the last position *)
    let os = (* FIXME: for hybrid equality of glob hybrid *)
      match call with
      | GCall(_, _, _, os) -> os
      | _ -> assert false in
    let eqglob = Feqglob nA in
    let eq_gv1 = mk_eq_exprs_p file nG nG' gv1 in
    F.fprintf fmt "call (_: %a).@ "
      Printer.pp_form (f_ands [eqlog; eq_gv1; eq_vcs]);
    List.iter (fun (o,vs,_) ->
      if Osym.equal o orcl then begin
        F.fprintf fmt "+ proc;sp 1 1;inline *;if => //.@ ";
        F.fprintf fmt "  rcondt{2} 4;first by auto.@ ";
        F.fprintf fmt 
          "  seq 1 4 : (@[<hov>%a /\\@ _res{1} = _res0{2} /\\@ ={%a}@]);@   first by auto.@ "
          Printer.pp_form (f_ands [eqlog;eq_gv1; eq_vcs])
          (pp_list ", " (fun fmt v -> F.fprintf fmt "%s" (snd (pvar [] v))))
          vs;
        F.fprintf fmt "  conseq * (_: _ ==> ={_res}) => //;sim.@ ";
      end
      else
        F.fprintf fmt "+ conseq* (_: _ ==> %a) => //;sim.@ "
          Printer.pp_form (f_ands [eq_gv1; eq_vcs])) os;
    F.fprintf fmt "swap %i %i; wp %i %i.@ " 
      log_pos (ninstr + nvc -2)  (ninstr + nvc -2) (ninstr + nvc -2);
    
    F.fprintf fmt "sim : (%a) => //.@ "
      Printer.pp_form 
      (f_ands [eqglob; eq_gv1; 
               mk_eq_vcs_p [nG] [nG'] (List.filter ((<>) logO) vcs)]);
    F.fprintf fmt "progress;smt." 
  in 
  proof, concl, pr, bound 

(* --------------------------------------------------------------------- *)
(* Certify swap in oracle *)

let proof_swap_oracle opos pft pft' file = 
  let se = pft.pt_ju.ju_se in
  let se' = pft'.pt_ju.ju_se in
  let g = game file se.se_gdef in
  let g' = game file se'.se_gdef in
  let i,seoc = get_se_octxt se opos in
  let lcmd1, lcmd2 = 
    let (n,p,_,t) = opos in
    let opos = (n,p,0,t) in
    let _,_,(_,i,tl),_ = get_se_lcmd se opos in 
    let _,_,(_,i',tl'),_ = get_se_lcmd se' opos in 
    i::tl, i'::tl' in
  let w = write_gcmds seoc.seoc_sec.sec_left in
  let w1 = 
    let (n,_,_,_) = opos in write_gcmds (L.take (n + 1) se.se_gdef) in
  let vcs = log_oracles file in
  let eqvc = mk_eq_vcs g g' (List.map fst vcs) in
  let eqw  = mk_eq_exprs file g g' w in
  let eqw1  = mk_eq_exprs file g g' w1 in
  let eqglob = Feqglob (adv_name file) in
  let eqglob = 
    if has_assert se.se_gdef then f_and (eq_assert g g') eqglob
    else eqglob in

  let skip1 lcmd = 
    let rec aux r lcmd = 
      match lcmd with
      | LBind _::_ -> assert false 
      | LGuard _:: _ | [] -> List.rev r, lcmd 
      | i::lcmd -> aux (i::r) lcmd in
    aux [] lcmd in

  let rec skip i w lcmd1 lcmd2 = 
    match lcmd1, lcmd2 with
    | LBind _::_, _ | _, LBind _::_ -> assert false
    | LGuard _:: _, _ -> i,w,lcmd1,lcmd2
    | _, LGuard _:: _ -> i,w,lcmd1,lcmd2
    | i1::lcmd1, i2::lcmd2 ->
      assert (equal_lcmd i1 i2);
      skip (i+1) (Se.union w (write_lcmd i1)) lcmd1 lcmd2
    | [], [] -> i,w,lcmd1,lcmd2
    | _, _ -> assert false in
 
  let pp_wl = 
      pp_list " " 
        (fun fmt v -> F.fprintf fmt ",%s" (snd (pvar [] (destr_V v)))) in
  let args = List.map mk_V seoc.seoc_oargs in
  let local = 
    Vsym.S.of_list
      (seoc.seoc_oargs @ List.map destr_V (Se.elements (write_lcmds lcmd1))) in

  let proof_if fmt = 
    
    let rec aux_true t wl lcmd1 lcmd2 = 
      match lcmd1, lcmd2 with
      | i1::_, _ when equal_lcmd i1 i ->
        F.fprintf fmt "rcondt{1} 1;[by auto | sim].@ ";
      | _, i2::_ when equal_lcmd i2 i ->
        F.fprintf fmt "rcondt{2} 1;[by auto | sim].@ ";
      | (LGuard _ as i1) :: lcmd1, 
        (LGuard _ as i2) :: lcmd2 when equal_lcmd i1 i2 ->
        F.fprintf fmt "if;[done | | done].@ ";
          aux_true t wl lcmd1 lcmd2  
      | _, _ -> 
        let i,w,lcmd1, lcmd2 = skip 0 Se.empty lcmd1 lcmd2 in
        let wl = Se.elements w @ wl in
        F.fprintf fmt "seq %i %i : (={_res%a} /\\ %a);first by auto.@ "
          i i pp_wl wl Printer.pp_form (f_ands [t;eqvc;eqw]);
        aux_true t wl lcmd1 lcmd2 in

    let rec aux_false t wl lcmd side =
      match lcmd with
      | i1::_ when equal_lcmd i1 i ->
        F.fprintf fmt "by rcondf{%i} 1;auto.@ " side
      | LGuard _ :: lcmd ->
        F.fprintf fmt "if{%i};[ | by auto].@ " side;
        aux_false t wl lcmd side
      | _ ->
        let lc, lcmd = skip1 lcmd in
        let i = List.length lc in
        let i1,i2 = if side = 1 then i,0 else 0,i in
        F.fprintf fmt "seq %i %i : (={_res%a} /\\ %a).@ "
          i1 i2 pp_wl wl Printer.pp_form (f_ands [t;eqvc;eqw]);
        F.fprintf fmt 
          "conseq* (_:_ ==> _) %s(_:true ==> true : =1%%r);first by auto.@ "
          (if side = 1 then "" else "_ ");
        F.fprintf fmt "  @[<v>%a@]@ " pp_cmds (lossless_lcmds file lc);
        aux_false t wl lcmd side in

    let rec aux_hd wl lcmd1 lcmd2 = 
      match lcmd1, lcmd2 with
      | (LGuard t as i1)::lcmd1, _ when equal_lcmd i1 i ->
        let t = formula file [g.mod_name] (Some "1") ~local t in
        F.fprintf fmt "if{1}.@ ";
        F.fprintf fmt "+ @[<v>";
        aux_true t wl lcmd1 lcmd2;
        F.fprintf fmt "@]";
        F.fprintf fmt "@[<v>";
        aux_false (f_not t) wl lcmd2 2;
        F.fprintf fmt "@]";

      | _, (LGuard t as i2)::lcmd2 when equal_lcmd i2 i ->
        let t = formula file [g'.mod_name] (Some "2") ~local t in
        F.fprintf fmt "if{2}.@ ";
        F.fprintf fmt "+ @[<v>";
        aux_true t wl lcmd1 lcmd2;
        F.fprintf fmt "@]";
        F.fprintf fmt "@[<v>";
        aux_false (f_not t) wl lcmd1 1;
        F.fprintf fmt "@]";
      | (LGuard _ as i1) :: lcmd1, 
        (LGuard _ as i2) :: lcmd2 when equal_lcmd i1 i2 ->
        F.fprintf fmt "if;[done | | done].@ ";
        aux_hd wl lcmd1 lcmd2  
      | _, _ -> 
        let i,w,lcmd1, lcmd2 = skip 0 Se.empty lcmd1 lcmd2 in
        let wl = Se.elements w @ wl in
        F.fprintf fmt "seq %i %i : (={_res%a} /\\ %a);first by auto.@ "
          i i pp_wl wl Printer.pp_form (f_ands [eqvc;eqw]);
        aux_hd wl lcmd1 lcmd2
    in
    aux_hd args lcmd1 lcmd2
  in

  let proof_asgn fmt = 
    let pp_seq i wl =
      if i <> 0 then
        F.fprintf fmt "seq %i %i : (={_res%a} /\\ %a);first by auto.@ "
          i i pp_wl wl Printer.pp_form (f_ands [eqvc;eqw]) in

    let pp_swap side i = 
      if i <> 0 then
        F.fprintf fmt "swap{%i} 1 %i.@ " side i in

    let rec aux_swap side wl k lcmd1 lcmd2 = 
      match lcmd1, lcmd2 with 
      | i1::_, _ when equal_lcmd i1 i ->
        assert (side = 2);
        pp_swap side k;
        F.fprintf fmt "by sim."
      | _,i2::_ when equal_lcmd i2 i ->
        assert (side = 1);
        pp_swap side k;
        F.fprintf fmt "by sim."
      | (LGuard _ as i1) :: lcmd1, (LGuard _ as i2) :: lcmd2 -> 
        assert (equal_lcmd i1 i2);
        pp_swap side k;
        pp_seq k wl;
        let oside = if side = 1 then 2 else 1 in
        F.fprintf fmt "if{%i}.@ " oside;
        F.fprintf fmt "+ @[<v>";
        F.fprintf fmt "rcondt{%i} 2;first by auto.@ " side;
        aux_swap side wl 0 lcmd1 lcmd2;
        F.fprintf fmt "@]@ ";
        F.fprintf fmt "rcondf{%i} 2;first by auto.@ " side;
        F.fprintf fmt 
          "conseq * (_: _ ==> _) (_: _ ==> _ : = 1%%r);first by auto.@ ";
        pp_cmds fmt (lossless_lcmds file [i])
      | LBind _:: _, _ | _, LBind _::_ -> assert false
      | i1 :: lcmd1, i2 :: lcmd2 ->
        assert (equal_lcmd i1 i2);
        let wl = Se.elements (write_lcmd i1) @ wl in
        aux_swap side wl (k+1) lcmd1 lcmd2 
      | _, _ -> assert false in


    let rec aux_hd k wl lcmd1 lcmd2 =
      match lcmd1, lcmd2 with
      | (LGuard _ as i1) :: lcmd1, (LGuard _ as i2) :: lcmd2 -> 
        assert (equal_lcmd i1 i2);
        pp_seq k wl;
        F.fprintf fmt "if;[done | | done]@ ";
        aux_hd 0 wl lcmd1 lcmd2 
      | i1::lcmd1, _ when equal_lcmd i1 i -> 
        pp_seq k wl;
        aux_swap 1 wl 0 lcmd1 lcmd2
      | _, i2::lcmd2 when equal_lcmd i2 i ->
        pp_seq k wl;
        aux_swap 2 wl 0 lcmd1 lcmd2
      | LBind _:: _, _ | _, LBind _::_ -> assert false
      | i1 :: lcmd1, i2 :: lcmd2 ->
        assert (equal_lcmd i1 i2);
        let wl = Se.elements (write_lcmd i1) @ wl in
        aux_hd (k+1) wl lcmd1 lcmd2 
      | _, _ -> assert false
    in
    aux_hd 0 args lcmd1 lcmd2 in

  let proof_o = 
    match i with
    | LGuard _ -> proof_if 
    | _ -> proof_asgn in
  let proof fmt () = 
    F.fprintf fmt "byequiv (_:_ ==> _)=> //;proc.@ ";
    let len = List.length vcs + List.length seoc.seoc_sec.sec_left + 1 in
    F.fprintf fmt "seq %i %i : (%a);last by sim.@ "
      len len 
      Printer.pp_form (f_ands [eqglob; eqvc;eqw1]);
      

    F.fprintf fmt "call (_:%a).@ " Printer.pp_form (f_ands [eqvc;eqw]);
    List.iter (fun _ -> F.fprintf fmt "+ by sim.@ ") seoc.seoc_oleft;
    F.fprintf fmt "+ @[<v>proc;sp 1 1;if;[done | | done].@ ";
    F.fprintf fmt "seq 1 1 : (={_res%a} /\\ %a);first by auto.@ "
      pp_wl args Printer.pp_form (f_ands [eqvc;eqw]);
    proof_o fmt; 
    F.fprintf fmt "@]@ ";
    List.iter (fun _ -> F.fprintf fmt "+ by sim.@ ") seoc.seoc_oright;
    (* iter oracle *)
    F.fprintf fmt "by conseq (_: _ ==> %a)=> //;sim."
      Printer.pp_form (f_ands [eqglob; eqvc;eqw])
  in proof
    
let rec extract_proof file pft = 
  match pft.pt_rule with
  | Rassert(p,e) -> 
    let pft2 = List.hd (List.tl pft.pt_children) in
    let lemma1, cmp1, bound1 = 
      extract_assert file pft p e in
    extract_proof_trans "assert" file lemma1 cmp1 bound1 pft pft2  pft.pt_info

  | Rtrans    -> 
    pp_debug "rule transitivity@.";
    let pft1 = List.hd pft.pt_children in (* dist *)
    let pft2 = List.hd (List.tl pft.pt_children) in
    let lemma1, _, cmp1, bound1 = extract_proof file pft1 in
    extract_proof_trans "transitivity" file lemma1 cmp1 bound1 pft pft2 pft.pt_info

  | Rdist_sym -> 
    pp_debug "dist_sym@.";
    let pft1 = List.hd pft.pt_children in
    let lemma1, _, cmp1, bound1 = extract_proof file pft1 in
    let pr,full,_ = extract_full_pr file mem pft.pt_ju in
    let proof fmt () = 
      F.fprintf fmt "move=> &m;rewrite ZooUtil.abs_minusC;apply (%s &m)." lemma1 in
    let lemma2 = add_pr_lemma ~pinfo:pft.pt_info file (mk_cmp full cmp1 bound1) (Some proof) in
    lemma2, pr, cmp1, bound1

  | Rdist_eq  -> 
    pp_debug "dist_eq@.";
    let pr,full,_ = extract_full_pr file mem pft.pt_ju in
    let proof fmt () = 
      F.fprintf fmt "move=> &m;apply ZooUtil.abs_minus_xx." in
    let lemma = add_pr_lemma ~pinfo:pft.pt_info file (mk_cmp full cmp_eq f_r0) (Some proof) in
    lemma, pr, cmp_eq, f_r0

  | Rhybrid   -> 
(*    let pft' = List.hd pft.pt_children in
    let _pr = extract_full_pr file mem pft'.pt_ju in *)
    default_proof file mem "hybrid" pft
  | Rswap_main _ -> default_proof file mem "swap_main" pft

  | Rassm_dec (ranges,dir,_subst,assum) ->
    pp_debug "assm_dec@.";
    let pft' = List.hd pft.pt_children in
    let lemma1, _pr, abs = extract_assum file ranges dir assum pft pft' in
    extract_proof_trans "decisional assumption" file lemma1 cmp_eq abs pft pft' pft.pt_info

  | Rconv -> 
    pp_debug "conv@.";
    extract_conv file pft [] pft

  | Rctxt_ev (i,_) ->
    pp_debug "ctxt_ev@.";
    let pft' = List.hd pft.pt_children in
    let ev = pft.pt_ju.ju_se.se_ev in
    let evs = destr_Land_nofail ev in
    let hs = List.mapi (fun i _ -> Format.sprintf "H%i" i) evs in
    let proof _file fmt () = 
      F.fprintf fmt "rewrite Pr [mu_sub]; last by done.@ ";
      F.fprintf fmt "by intros &hr %a;rewrite H%i //;smt." pp_cintros hs i in
    extract_proof_sb1_le "Ctxt_ev" file pft pft' proof

  | Rremove_ev _ ->
    pp_debug "remove_ev@.";
    let pft' = List.hd  pft.pt_children in
    let proof _file fmt () = 
      F.fprintf fmt "@[<v>rewrite Pr [mu_sub];[ | by []].@ ";
      (* pp_impl_quant fmt pft.pt_ju.ju_se.se_ev; *)
      F.fprintf fmt "@]" in
    extract_proof_sb1_le "Remove_ev" file pft pft' proof


  | Rmerge_ev _ -> 
    pp_debug "merge_ev@.";
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "Merge_ev" file pft pft' pft.pt_info (pr_admit "merge_ev")

  | Rrnd (pos,_,inv1,inv2) ->
    pp_debug "rnd@.";
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "Rnd" file pft pft' pft.pt_info
      (pr_random (pos,inv1,inv2) pft.pt_ju pft'.pt_ju)

  | Rrnd_orcl (pos, inv1, inv2) ->
    pp_debug "rnd orcl@.";
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "rnd_orcl" file pft pft' pft.pt_info
      (pr_random_orcl (pos,inv1,inv2) pft.pt_ju pft'.pt_ju)

  | Rswap _ ->
    pp_debug "swap@.";
    let sw1, pft' = skip_swap pft in
    begin match pft'.pt_rule with
    | Rconv -> extract_conv file pft sw1 pft'
    | _ ->
      (* FIXME *)
      extract_proof_sb1 "Swap" file pft pft' pft.pt_info (pr_swap sw1 pft.pt_ju pft'.pt_ju)
    end
  | Rswap_orcl (opos,_) ->
    pp_debug "swap oracle@.";
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "Swap Oracle" file pft pft' pft.pt_info
      (proof_swap_oracle opos pft pft')

  | Rrnd_indep (side, pos) ->
    pp_debug "rnd_indep@.";
    extract_rnd_indep file side pos pft.pt_ju pft.pt_info
       
  | Rassm_comp (ranges,_subst, assum) ->
    pp_debug "assm_comp@.";
    extract_assum_comp file ranges assum pft

  | Rexc (pos,l)   -> 
    pp_debug "except@.";
    let pft' = List.hd pft.pt_children in
    let lemma2, eps = extract_except file pos l pft pft' in
    extract_proof_trans "Excepted" file lemma2 cmp_le eps pft pft' pft.pt_info

  | Radd_test _ -> 
    assert false 

  | Rexc_orcl _ -> 
    pp_debug "except oracle@.";
    default_proof file mem "exc_orl" pft

  | Rrw_orcl (op,dir)  -> 
    pp_debug "rewrite oracle@.";
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "Rw_orcl" file pft pft' pft.pt_info
      (pr_rw_orcl (op,dir) pft.pt_ju pft'.pt_ju)


  | Rbad     _  -> 
    pp_debug "bad@.";
    default_proof file mem "bad" pft
  | Radmit _    -> 
    pp_debug "admit@.";
    default_proof ~warning:false file mem "admit" pft

  | Rfalse_ev   -> 
    fixme "undefined" (*
    pp_debug "false_ev @.";
    let ju = pft.pt_ju in
    let pr = extract_pr file mem ju in
    let bound = f_r0 in
    let ev = ju.ju_se.se_ev in
    let proof fmt () = 
      match (Event.binding ev) with
      | [] -> 
        F.fprintf fmt "@[<v>by intros &m; rewrite Pr [mu_false].@]"
      | [_,_] ->
        let prf = let f,m,a,_ = destr_pr pr in Fpr(f,m,a,Fcnst "false") in
        F.fprintf fmt "@[<v>move=> &m.@ ";
        F.fprintf fmt "cut -> : @[<hov>%a =@ %a@];[ | by rewrite Pr [mu_false]].@ "
          Printer.pp_form pr Printer.pp_form prf;
        F.fprintf fmt "rewrite Pr [mu_eq] /List.%s //;smt.@]"
          (if (Event.quant ev) = Expr.All then "all" else "any");
      | _ -> assert false (* Not implemented *) in
    let lemma = add_pr_lemma ~pinfo:pft.pt_info file (mk_cmp pr cmp_eq bound) (Some proof) in
    lemma, pr, cmp_eq, bound
    *)

  | Rcase_ev (_flip, _e) -> fixme "undefined"
    (*
    pp_debug "case_ev@."; 
    let pft1 = List.nth pft.pt_children (if flip then 1 else 0) in
    let pft2 = List.nth pft.pt_children (if flip then 0 else 1) in
    let (lemma1, pr1, cmp1, bound1) = extract_proof file pft1 in
    let (lemma2, pr2, cmp2, bound2) = extract_proof file pft2 in
    let pr = extract_pr file mem pft.pt_ju in
    let cmp = cmp_le in
    let bound = f_radd bound1 bound2 in
    let g = find_game file pft.pt_ju.ju_se.se_gdef in
  
    let f,m,a,ev1 = destr_pr pr1 and _,_,_,ev2 = destr_pr pr2 in
    let pr_or = Fpr(f,m,a,f_or ev1 ev2) in
    let flocal = flocal_ev pft.pt_ju.ju_se.se_ev in
    let ev = formula ~flocal file [g.mod_name] (Some "hr") e in
    let jev =  pft.pt_ju.ju_se.se_ev in
    let has_assert = Game.has_assert pft.pt_ju.ju_se.se_gdef in
    let vs = match (Event.binding jev) with
      | [vs,_] -> vs
      | [] -> []
      | _ -> assert false in

    let proof fmt () = 
      F.fprintf fmt "(* Case event *)";
      F.fprintf fmt "move => &m.@ ";
      F.fprintf fmt "apply (Real.Trans _ (%a)).@ " Printer.pp_form pr_or;
      let rw_list = 
        if (Event.binding jev) = [] then ""
        else if (Event.quant jev) = Expr.All then " /List.all" 
        else " /List.any" in
      F.fprintf fmt "+ @[<v>rewrite Pr[mu_sub]%s;[ move=> &hr | by []].@ " rw_list;
      let pp_v fmt v = F.fprintf fmt "%s" (snd (pvar [] v)) in
      if (Event.binding jev) = [] then
        F.fprintf fmt "by case (%a) => Hc He;[left | right];move: Hc He.@ "
          Printer.pp_form ev
      else if (Event.quant jev) = Expr.All then 
        F.fprintf fmt "@[<hov 2>by move=> %s;case (%a)=> Hc;@ [left|right];%s@ move=> [%a];move: (He (%a)) Hc.@]@ "
          (if has_assert then "[He _]" else "He") 
          Printer.pp_form ev 
          (if has_assert then "(split;[ done | ]);" else "")
          (pp_list " " pp_v) vs (pp_list "," pp_v) vs
      else begin
        if has_assert then F.fprintf fmt "move=> [HWa He];move:He.@ ";
        F.fprintf fmt "@[<hov 2>by move=> [[%a]];case (%a)=> Hc He;[left | right];%sexists (%a);move: Hc He.@]@ "
          (pp_list " " pp_v) vs Printer.pp_form ev 
          (if has_assert then "(split;[ done | ]);" else "")
          (pp_list "," pp_v) vs
      end;
      F.fprintf fmt "@]";
      F.fprintf fmt "rewrite Pr[mu_or];apply le_trans_sub;@ ";
      F.fprintf fmt "  [ split;[ | move=> ____ {____}];by byphoare (_:_ ==> _);auto | ].@ ";

      let aux fmt (cmp,lemma) =
        if cmp = cmp_eq then
          F.fprintf fmt 
            "by cut H1 := %s &m; cut H := Real.eq_le _ _ H1." lemma
          else
            F.fprintf fmt "by cut H:= %s &m." lemma in
      F.fprintf fmt "apply Real.addleM.@ ";
      F.fprintf fmt "+ %a@ " aux (cmp1,lemma1);
      F.fprintf fmt "%a" aux (cmp2,lemma2) in

    let lemma3 = add_pr_lemma ~pinfo:pft.pt_info file (mk_cmp pr cmp bound) (Some proof) in
    lemma3, pr, cmp, bound
    *)

  | Rsplit_ev _i -> 
    pp_debug "split_ev@.";
    let pft' = List.hd pft.pt_children in
    let proof _file fmt () = 
      F.fprintf fmt "(* split_ev *)@ ";
      if not (is_Quant pft.pt_ju.ju_se.se_ev) then
        F.fprintf fmt "by rewrite Pr [mu_eq]."
      else 
        (F.fprintf fmt "@[<v>rewrite Pr [mu_eq];[ | by []].@ ";
         F.fprintf fmt "move=> &hr;by %a.@]" 
           (pp_congr_quant ~_semi:false) pft.pt_ju.ju_se.se_ev)

    in
    extract_proof_sb1 "split_ev" file pft pft' pft.pt_info proof

  | Rrw_ev (i, dir) ->
    pp_debug "rewrite ev@."; 
    let pft' = List.hd pft.pt_children in
    let is_not = 
      let ev = pft.pt_ju.ju_se.se_ev in
      let evs = destr_Land_nofail ev in
      let _,b,_ = Util.split_n i evs in
      is_Not b in
 
    let pp_branch pft fmt dir = 
      let ev = pft.pt_ju.ju_se.se_ev in
      let evs = destr_Land_nofail ev in
      let his = List.mapi (fun i _ -> Format.sprintf "H%i" i) evs in
      let hi = Format.sprintf "H%i" i in
      let his' = List.filter (fun s -> s <> hi) his in
      if is_not then
        F.fprintf fmt "by move=> %a;move: %s %a; rewrite -neqF=> %s."
          pp_cintros his hi
          (pp_list " " (fun fmt -> F.fprintf fmt "%s")) his'
          (if dir then "<-" else "->")
      else
        F.fprintf fmt "by move=> %a;move: %a;rewrite %sH%i." 
          pp_cintros his 
          (pp_list " " (fun fmt -> F.fprintf fmt "%s")) his'
          (if dir then "-" else "")
        i in
      
    let proof _file fmt () =
      let dir1, dir2 = if dir = LeftToRight then true, false else false, true in
      F.fprintf fmt "@[<v>rewrite Pr [mu_eq];[move=> &hr | by done].@ ";
      (* pp_congr_quant ~semi:true fmt pft.pt_ju.ju_se.se_ev; *)
      F.fprintf fmt "split.@ ";
      F.fprintf fmt "+ @[<v>%a@]@ " (pp_branch pft) dir1;
      F.fprintf fmt "%a@]" (pp_branch pft') dir2 in
    extract_proof_sb1 "Rw_ev" file pft pft' pft.pt_info proof

  | Rguard (opos, tnew) -> 
    assert (tnew <> None);
    let pftb = List.hd pft.pt_children in 
    let auxname = init_section file "GUARD" pftb in
    let lemmab, prb, cmpb, boundb = extract_proof file pftb in
    let conclusion = top_name file "conclusion" in
    let _gb = get_game file pftb.pt_ju.ju_se.se_gdef in
    let body = forall_mem (mk_cmp prb cmpb boundb) in
    let proof fmt () = 
      F.fprintf fmt "apply %s." lemmab in
    add_local file (Clemma(false, conclusion,body, Some proof));
    let infob = adv_info file in
    let secb = get_section file in
    end_section file;
    let info = adv_info file in
    let pft' = List.hd (List.tl pft.pt_children) in
    (* building the proof *)
    let pr  = extract_pr file mem pft.pt_ju in
    let pr' = extract_pr file mem pft'.pt_ju in
    let clone_G = {
      ci_local  = false;   ci_import = false;
      ci_from   = auxname; ci_as     = auxname;
      ci_with   = 
        Osym.H.fold (fun o _oi w -> 
          CWop(q_oracle_i infob o, None, Ecnst (q_oracle file o)) :: w)
          infob.adv_g.oinfo [];
      ci_proof   = 
        Osym.H.fold (fun o _oi p -> 
          let ax = q_oracle_i infob o ^ "_pos" in
          let pr = Format.sprintf "apply %s_pos"  (q_oracle file o) in
          (ax, fun fmt () -> F.fprintf fmt "%s" pr)::p )
          infob.adv_g.oinfo []; } in
    add_top file (Cclone clone_G); 
  (* build the adversary for GUARD_Loc *)
    let arg = ([],"_arg") in
    let res = ([],"_res") in
    let mO = {mn="O";ma=[]} in
    let orcls = 
      Osym.H.fold (fun o _ l ->
        let name = "o" ^ Osym.to_string o in
        let body = 
          if Osym.H.mem infob.adv_g.oinfo o then Falias (mO, name)
          else Fbody {
            f_param = [arg,o.Osym.dom];
            f_local = [res,o.Osym.codom];
            f_res   = Some(res,Tzc o.Osym.codom);
            f_body  = [Iasgn([res],Ecnst "witness")];
          } in
        MCfun {f_name = name; f_def = body } :: l) info.adv_g.oinfo [] in
    let advs = 
      Asym.H.fold (fun a _ l ->
        let name = asym_to_string a in
        MCfun {f_name = name; f_def = Falias({mn="A";ma=[]},name); } :: l) 
        infob.adv_g.ainfo [] in
    let adv_gl = 
      { mod_name = top_name file "ABad";
        mod_param = [("A",info.adv_ty); ("O",F.sprintf "%s.%s" auxname infob.adv_oty)];
        mod_body = Mod_def ([
          MCmod {
            mod_name = "O1"; mod_param = [];
            mod_body = Mod_def orcls; };
          MCmod {
            mod_name = "A"; mod_param = [];
            mod_body = Mod_alias({mn = "A"; ma = [{mn="O1";ma = []}]}); } ] @
          advs) } in
    add_game file `Top adv_gl;

    (* clone the Local *)
    let auxname_Loc = auxname^"_Loc" in
    let clone_GL = {
      ci_local  = true; ci_import = true;
      ci_from   = auxname^".Local"; ci_as     = auxname_Loc;
      ci_with   = []; ci_proof  = []; } in
    add_local file (Cclone clone_GL); 
    add_restr_info file secb.section_name infob;
  
    let ms, mc = build_subst_section file auxname infob secb adv_gl.mod_name in
    let boundb = subst_f ms mc boundb in
    let concl1 = mk_cmp (Fabs (f_rsub pr pr')) cmp_le boundb in
    let nA   = info.adv_name in
    let se'_bad = 
      { pft'.pt_ju.ju_se with
        se_ev = pftb.pt_ju.ju_se.se_ev } in
    let pr'_bad = extract_pr_se file mem se'_bad in
    let wc = write_gcmds pftb.pt_ju.ju_se.se_gdef in
    let nsize2 = List.length pftb.pt_ju.ju_se.se_gdef in
    let vcs2 = List.map (fun ((_,v),_) -> v) (log_oracles_i infob) in
    let vcs1 = List.map fst (log_oracles file) in
    let nG' = let (m,_),_,_,_ = destr_pr pr' in m.mn in
    let nGb = let (m,_),_,_,_ = destr_pr prb in m.mn in
    let g  = find_game file pft.pt_ju.ju_se.se_gdef in
    let g'  = find_game file pft'.pt_ju.ju_se.se_gdef in
    let bad_ev = pftb.pt_ju.ju_se in
    let ev     = pft.pt_ju.ju_se in
    let bad1 = extract_ev file [g.mod_name] (Some "1") bad_ev in
    let bad1_nomem = extract_ev file [g.mod_name] None bad_ev in
    let bad2 = extract_ev file [g'.mod_name] (Some "2") bad_ev in
    let bad2_nomem = extract_ev file [g'.mod_name] None bad_ev in
    let ev1 = extract_ev file [g.mod_name] (Some "1") ev in
    let ev2 = extract_ev file [g'.mod_name] (Some "2") ev in

    let lossless2 = 
      let _, seoc = get_se_octxt pft'.pt_ju.ju_se opos in
      pr_lossless g' file f_true 0 seoc.seoc_sec.sec_right in
    let c1_head, c1,c2, _call = 
      let (n,_,_,_) = opos in 
      let call, sctxt = get_se_ctxt pft.pt_ju.ju_se n in 
      List.rev sctxt.sec_left, 
      List.rev (call::sctxt.sec_left), sctxt.sec_right, call in
    let lossless1 = pr_lossless g file f_true 0 c2 in
    let wc1 = write_gcmds c1 in
    let wc1_hd = write_gcmds c1_head in
    let eqglob = Feqglob nA in
    let _, seoc = get_se_octxt_len pft.pt_ju.ju_se opos 0 in
    assert (seoc.seoc_oright = [] && seoc.seoc_oleft = []);
    let bad_t =
      let ev =  pftb.pt_ju.ju_se.se_ev in 
      let local = fixme "undefined" (*
        match (Event.binding ev) with
        | [vs,_] ->
          List.fold_left (fun s v -> Vsym.S.add v s) 
            Vsym.S.empty vs
        | _ -> assert false
        *)
      in
      formula file [g'.mod_name] (Some "2") ~local ev in

    let lossless_tl = 
      lossless_lcmds file seoc.seoc_cright in
    let lossless_o1 =
      let c = List.rev_append seoc.seoc_cleft seoc.seoc_cright in
      lossless_lcmds file c in
    let lossless_o2 = 
      let _, seoc = get_se_octxt_len pft'.pt_ju.ju_se opos 0 in
      let c = List.rev_append seoc.seoc_cleft seoc.seoc_cright in
      lossless_lcmds file c in
    let proof1 fmt () = 
      F.fprintf fmt "(* Upto bad *)@ ";
      F.fprintf fmt "move=> &m.@ ";
      let advs = Asym.H.fold (fun a os l -> (a,os)::l) infob.adv_g.ainfo [] in
      F.fprintf fmt "cut H1 := %s.%s (<:%s(%s)) %a &%s.@ "
        auxname_Loc conclusion adv_gl.mod_name nA 
        (pp_list " " (fun fmt _ -> F.fprintf fmt "_")) advs
        mem;
      let pp_o_ll fmt o = F.fprintf fmt "H%s_ll" (Osym.to_string o) in
      List.iter (fun (a,os) ->
        F.fprintf fmt 
          "+ move=> O %a; apply (a%s_ll (<: %s(%s,O).O1) %a).@ "
          (pp_list " " pp_o_ll) os
          (Asym.to_string a) adv_gl.mod_name nA 
          (pp_list " " pp_o_ll) os) advs;
      F.fprintf fmt "apply (Real.Trans _ _ _ _ H1) => {H1}.@ ";
    
      F.fprintf fmt "apply (Real.Trans _ %a).@ " Printer.pp_form pr'_bad;
      F.fprintf fmt 
        "+ cut Hequiv : equiv [@[<hov 2>%s(%s).main ~ %s(%s).main :@ ={glob %s} ==>@ %a@]].@ "
        g.mod_name nA g'.mod_name nA nA 
        Printer.pp_form (f_and (f_iff bad1 bad2) (f_imp (f_not bad2) (f_iff ev1 ev2)));
      F.fprintf fmt "  + @[<v>(* upto bad *)@ proc;seq %i %i : (%a).@ "
        (List.length vcs1 + nsize2) (List.length vcs1 + nsize2)
        Printer.pp_form 
        (f_and 
           (f_iff bad1 bad2) 
           (f_imp (f_not bad2) 
              (f_ands [eqglob; mk_eq_exprs file g g' wc1;
                       mk_eq_vcs g g' vcs1])));
      F.fprintf fmt "+ @[<v>";
      F.fprintf fmt "seq %i %i : (%a);first by sim.@ "
        (List.length c1 - 1 + List.length vcs1) 
        (List.length c1 - 1 + List.length vcs1) 
        Printer.pp_form (f_ands [eqglob;mk_eq_exprs file g g' wc1_hd;
                                 mk_eq_vcs g g' vcs1]);
      F.fprintf fmt "call (_:@[<v>%a,@ %a,@ %a@]).@ "
        Printer.pp_form bad2_nomem
        Printer.pp_form (f_ands [mk_eq_exprs file g g' wc1_hd;
                                 mk_eq_vcs g g' vcs1])
        Printer.pp_form bad1;
      F.fprintf fmt "+ apply a%s_ll.@ " (Asym.to_string seoc.seoc_asym);
      (* equiv *)
      F.fprintf fmt "+ @[<v>proc;sp 1 1;if;[done | | by auto].@ "; 
      F.fprintf fmt "exists* %s.%s{2}; elim* => __log__.@ " 
         g'.mod_name (snd (log_oracle [] seoc.seoc_osym));
      F.fprintf fmt 
        "seq 1 1 : (@[<hov 2>={_res%a} /\\@ %s.%s{2} = (%a){2}::__log__ /\\@ %a@]);first by auto.@ "
        (pp_list "" (fun fmt v -> F.fprintf fmt ",%s" (snd (pvar [] v))))
        seoc.seoc_oargs
        g'.mod_name (snd (log_oracle [] seoc.seoc_osym))
        (pp_list "," (fun fmt v -> F.fprintf fmt "%s" (snd (pvar [] v))))
        seoc.seoc_oargs 
        Printer.pp_form (f_ands [mk_eq_exprs file g g' wc1_hd;
                                 mk_eq_vcs g g' vcs1]);
      F.fprintf fmt "conseq* (_: _ ==> %a => ={_res}).@ "
        Printer.pp_form (f_not bad_t);
      F.fprintf fmt "+ @[<v>progress[-split]. rewrite !any_cons /=; smt.@ ";
      List.iter (fun _ -> F.fprintf fmt "if;[done | | done].@ ") 
        seoc.seoc_cleft;
      F.fprintf fmt "if{2};first by conseq (_: _ ==> ={_res});[ auto | sim].@ ";
      F.fprintf fmt 
        "conseq* (_ : _ ==> _) (_: true ==> true : = 1%%r);first by progress;smt.@ ";
      F.fprintf fmt "%a@]@]@ "
        pp_cmds lossless_tl;

      F.fprintf fmt "+ @[<v>move=> _ _;proc;sp 1;if;[ | by auto].@ ";
      F.fprintf fmt "@[<hov 2>seq 1 : true 1%%r 1%%r 0%%r _@ (%a);@ last 2 by auto.@]@ "
        Printer.pp_form bad1_nomem;
      F.fprintf fmt "+ by auto;progress;rewrite any_cons;right.@ ";
      F.fprintf fmt "+ by auto.@ ";
      F.fprintf fmt "conseq * (_: _ ==> true : = 1%%r);first by auto.@ ";
      pp_cmds fmt lossless_o1;
      F.fprintf fmt "@]@ ";
      F.fprintf fmt "+ @[<v>move=> _;proc;sp 1;if;[ | by auto].@ ";
      F.fprintf fmt "conseq* (_: _ ==> %a);first by auto.@ "
        Printer.pp_form bad2_nomem;
      F.fprintf fmt "@[<hov 2>seq 1 : true 1%%r 1%%r 0%%r _@ (%a);last 2 by auto@].@ "
        Printer.pp_form bad2_nomem;
      F.fprintf fmt "+ by auto;progress;rewrite any_cons;right.@ ";
      F.fprintf fmt "+ by auto.@ ";
      F.fprintf fmt "conseq * (_: _ ==> true : = 1%%r);first by auto.@ ";
      pp_cmds fmt lossless_o2;
      F.fprintf fmt "@]@ ";
      F.fprintf fmt "+ skip;progress [-split];split;first by done.@ "; 
      F.fprintf fmt "  by progress [-split];elimIF.";
      F.fprintf fmt "@]@ ";
      F.fprintf fmt "case (%a).@ " Printer.pp_form bad2;
      F.fprintf fmt "conseq * (_: _ ==> true).@ ";
      F.fprintf fmt "move=> &m1 &m2 [[H1 H2] H3];rewrite H1 H3 => //.@ "; 
      F.fprintf fmt "seq %i 0 : true.@ " (List.length c2);
      F.fprintf fmt "conseq (_: _ ==> _) (_: true ==> true: = 1%%r).@ ";
      F.fprintf fmt "%a@ " pp_cmds lossless1;
      F.fprintf fmt "seq 0 %i : true;last by auto.@ " (List.length c2);
      F.fprintf fmt "conseq (_: _ ==> _) _ (_: true ==> true: = 1%%r).@ ";
      F.fprintf fmt "%a@ " pp_cmds lossless2;
      F.fprintf fmt "conseq * (_: _ ==> %a).@ "
        Printer.pp_form (f_iff ev1 ev2);
      F.fprintf fmt 
        "move => &m1 &m2 [[H1 H2] H3];rewrite H1;move: (H2 H3) => //.@ ";
      F.fprintf fmt "by sim;move=> &m1 &m2 [[H1 H2] H3];move:(H2 H3).";
      F.fprintf fmt "@]@ ";
      F.fprintf fmt "  @[<v>";
      F.fprintf fmt "rewrite Pr [mu_split (%a)]; rewrite ZooUtil.abs_minusC.@ "
        Printer.pp_form bad1_nomem;
      F.fprintf fmt "rewrite Pr [mu_split (%a)]; rewrite ZooUtil.abs_minusC.@ "
        Printer.pp_form bad2_nomem; 
      F.fprintf fmt "apply ZooUtil.upto2_abs. smt. smt.@ ";
      F.fprintf fmt 
        "byequiv Hequiv=> //;move=> _ _;apply ZooUtil.upto2_imp_bad.@ ";
      F.fprintf fmt "rewrite Pr [mu_sub]=> //.@ ";
      F.fprintf fmt 
        "byequiv Hequiv=> //;move=> _ _;apply ZooUtil.upto2_notbad.";
      F.fprintf fmt "@]@ ";
      F.fprintf fmt "byequiv (_: _ ==> _)=> //;proc.@ ";
      F.fprintf fmt "seq %i %i : (%a);first by sim.@ "
        (List.length vcs1 + nsize2) (List.length vcs2 + nsize2) 
        Printer.pp_form (f_ands [mk_eq_vcs_p [nG'] [nGb] vcs2;
                                 mk_eq_exprs_p file nG' nGb wc]);
      F.fprintf fmt "conseq* (_:_ ==> true) (_: true ==> true : = 1%%r) => //.@ ";
      pp_cmds fmt lossless2 in
        


    let lemma1 = add_pr_lemma file concl1 (Some proof1) in

    extract_proof_trans "Guard" file lemma1 cmp_le boundb pft pft'  pft.pt_info


  | Rguess newasym  -> 
    let pftb = List.hd pft.pt_children in 
    let auxname = init_section file "GUESS" pftb in
    let lemmab, prb, cmpb, boundb = extract_proof file pftb in
    let conclusion = top_name file "conclusion" in
    let _gb = get_game file pftb.pt_ju.ju_se.se_gdef in
    let body = forall_mem (mk_cmp prb cmpb boundb) in
    let proof fmt () = 
      F.fprintf fmt "apply %s." lemmab in
    add_local file (Clemma(false, conclusion,body, Some proof));
    let infob = adv_info file in
    let secb = get_section file in
    end_section file;
    let proof, concl, pr, bound = 
      proof_guess file newasym pft auxname infob secb 
        conclusion prb cmpb boundb in

    let lemma = add_pr_lemma file concl (Some proof) in
    (lemma, pr, cmp_le, bound)    
  | Rfind (newasym, fct)  -> 
    let pftb = List.hd pft.pt_children in 
    let auxname = init_section file "FIND" pftb in
    let lemmab, prb, cmpb, boundb = extract_proof file pftb in
    let conclusion = top_name file "conclusion" in
    let _gb = get_game file pftb.pt_ju.ju_se.se_gdef in
    let body = forall_mem (mk_cmp prb cmpb boundb) in
    let proof fmt () = 
      F.fprintf fmt "apply %s." lemmab in
    add_local file (Clemma(false, conclusion,body, Some proof));
    let infob = adv_info file in
    let secb = get_section file in
    end_section file;
    let proof, concl, pr, bound =
      proof_find file newasym pft auxname infob secb 
        conclusion prb cmpb boundb fct in 
    let lemma = add_pr_lemma ~pinfo:pft.pt_info file concl (Some proof) in
    (lemma, pr, cmp_le, bound) 

  | Rcheck_hash_args _
  | Rswap_quant_ev _
  | RbadOracle _
  | Rinjective_ctxt_ev _
  | Runwrap_quant_ev _ -> assert false


and extract_conv file pft sw1 pft1 =
  let pft2 = skip_conv pft1 in
  let sw2, pft' = skip_swap pft2 in 
  extract_proof_sb1 "Conv" file pft pft' pft.pt_info
    (pr_conv sw1 pft.pt_ju pft1.pt_ju pft2.pt_ju pft'.pt_ju sw2)
    (* (fun _ fmt () -> F.fprintf fmt "admit.") *)


and extract_assert file pft _p e = 
  let pft1 = List.hd pft.pt_children in 
  let pft2 = List.hd (List.tl pft.pt_children) in
  let lemma1, _, cmp1, bound1 = extract_proof file pft1 in
  let g   = game file pft.pt_ju.ju_se.se_gdef in 
  let g'  = game file pft2.pt_ju.ju_se.se_gdef in
  let pr  = extract_pr file mem pft.pt_ju in
  let pr2 = extract_pr file mem pft2.pt_ju in
  let concl = mk_cmp (Fabs (f_rsub pr pr2)) cmp_le bound1 in
  let tacs = auto_sim g g' pft2.pt_ju.ju_se.se_gdef [Tac Auto] in
      
  let proof fmt () = 
    F.fprintf fmt "@[<v>move=> &m.@ ";
    if cmp1 = cmp_eq then 
      F.fprintf fmt "rewrite -(%s &m).@ " lemma1
    else
      F.fprintf fmt "cut := %s &m;apply real_le_trans.@ " lemma1;
    F.fprintf fmt "rewrite Pr [mu_split (!(@[<hov>%a@]))].@ "
      Printer.pp_form (formula file [g.mod_name] None e);
    F.fprintf fmt 
      "apply abs_add_minus;[smt | | by apply eq_le; rewrite Pr [mu_eq] ].@ ";
    F.fprintf fmt "byequiv (_ : _ ==> _); [ proc | by [] | by [] ].@ ";
    pp_cmds fmt tacs; 
    F.fprintf fmt "@]" in
  let lemma2 = add_pr_lemma file concl (Some proof) in
  lemma2, cmp_le, bound1

(* We have pft' proved by lemma1 :  pr' <= bound  or |pr' - pr1| < bound
   We have lemma2 : pr = pr'  proved by proof2
   We build a proof of pft : pr <= bound  or |pr - pr1| < bound
*) 
and extract_proof_sb1 msg file pft pft' pinfo proof2 = 
  let (lemma1, _pr',cmp,bound) = extract_proof file pft' in
  let pr,full,kind = extract_full_pr file mem pft.pt_ju in
  let proof2 = proof2 file in
  let proof3 fmt () = 
    F.fprintf fmt "@[<v>";
    F.fprintf fmt "(* %s *)@ " msg;
    F.fprintf fmt "move=> &m.@ ";
    F.fprintf fmt "cut H := %s &m.@ " lemma1;
    let s1, s3 = if kind = `ABS then "dist", " _ " else "bound", " " in
    let s2 = if cmp = cmp_eq then "eq" else "le" in
    F.fprintf fmt "apply (%s_eq_%s_trans _ _ _%s_ H);move=> {H}.@ " s1 s2 s3;
    proof2 fmt ();
    F.fprintf fmt "@]" in
  let lemma3 = 
    add_pr_lemma ~pinfo file (mk_cmp full cmp bound) (Some proof3) in
  lemma3, pr, cmp, bound

and extract_proof_trans msg file lemma1 cmp1 bound1 pft pft' pinfo = 
  (*  lemma1 : forall &m, |pr - pr'| cmp1 bound1
        1/ pft' : pr' cmp2 bound2  
           pft  : pr <= bound1 + bound2  
        2/ pft' : |pr' - pr2| cmp2 bound2  
           pft  : |pr - pr2 | <= bound1 + bound2    
      Remark/TODO: we can replace <= with = under some conditions
  *)
  let lemma2, _pr', cmp2, bound2 = extract_proof file pft' in
  let pr, full, abs = extract_full_pr file mem pft.pt_ju in
  let bound = f_radd bound1 bound2 in
  let concl =  mk_cmp full cmp_le bound in

  let proof fmt () = 
    F.fprintf fmt "@[<v>";
    F.fprintf fmt "(* %s *)@ " msg;
    F.fprintf fmt "move=> &m.@ ";
    if cmp1 = cmp_eq then
      F.fprintf fmt "cut H1' := %s &m; cut H1 := real_eq_le _ _ H1'.@ " lemma1 
    else 
      F.fprintf fmt "cut H1 := %s &m.@ " lemma1;
    if cmp2 = cmp_eq then
      F.fprintf fmt "cut H2' := %s &m; cut H2 := real_eq_le _ _ H2'.@ " lemma2
    else 
      F.fprintf fmt "cut H2 := %s &m.@ " lemma2;
    if abs = `ABS then
      F.fprintf fmt "apply (dist_le_trans _ _ _ _ _ H1 H2)."
    else 
      F.fprintf fmt "apply (bound_le_trans _ _ _ _ H1 H2).";
    F.fprintf fmt "@]"
  in
    
  let lemma3 = add_pr_lemma ~pinfo file concl (Some proof) in

  lemma3, pr, cmp_le, bound

and extract_proof_sb1_le msg file pft pft' proof = 
  let (lemma1, pr',cmp,bound) = extract_proof file pft' in
  let pr = extract_pr file mem pft.pt_ju in
  let proof = proof file in
  let lemma2 = 
    add_pr_lemma file (mk_cmp pr cmp_le pr') 
      (Some proof) in
  let proof fmt () =
    F.fprintf fmt "(* %s *)@ " msg;
    F.fprintf fmt "intros &m; cut H1 := %s &m.@ " lemma2;
    F.fprintf fmt "apply (real_le_trans _ _ _ H1).@ ";
    F.fprintf fmt "by %s (%s &m)." 
      (if cmp = cmp_eq then "rewrite" else "apply") lemma1 in
  let lemma3 = 
    add_pr_lemma ~pinfo:pft.pt_info file (mk_cmp pr cmp_le bound) 
      (Some proof) in
  lemma3, pr, cmp_le, bound

let extract_file ts = 
  let pt = get_proof_tree ts in
  let pft = Rules.simplify_proof_tree pt |> Rules.decorate_proof_tree in
  let file = init_file ts in
  let name = top_name file "conclusion" in
  ignore (init_section file "MAIN" pft);
  let _,full,_ = extract_full_pr ~local:`Global file mem pft.pt_ju in
  let lemma, _pr, cmp, bound = extract_proof file pft in
  let body = forall_mem (mk_cmp full cmp bound) in
  let proof fmt () = 
    F.fprintf fmt "apply %s." lemma in    
  add_local file (Clemma(false, name,body, Some proof));
  end_section file;
  file

let extract ts filename = 
  pp_debug "start extraction info file %s@." filename;
  let file = extract_file ts in
  let out = open_out filename in
  let fmt = F.formatter_of_out_channel out in
  Printer.pp_file fmt file; 
  close_out out






















