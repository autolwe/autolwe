(* * Tactic engine: transformations of theory and proof states. *)

(* ** Imports and abbreviations *)
open Abbrevs
open Expr
open ExprUtils
open Type
open Util
open Nondet
open Syms
open TheoryTypes
open TheoryState
open Rules
open CoreTypes
open RewriteRules
open AssumptionRules
open RandomRules
open RindepRules
open CrushRules
open CaseRules
open Game

module Ht = Hashtbl
module PT = ParserTypes
module PU = ParserUtil
module CR = CoreRules
module T = Tactic

let mk_log level = mk_logger "Engine.Engine" level "Engine.ml"
let log_i = mk_log Bolt.Level.INFO

(* ** Include state
 * ----------------------------------------------------------------------- *)

let included = ref []

(* ** Utility functions
 * ----------------------------------------------------------------------- *)

(* compute diff between the two given proof-trees *)
let diff_step ops nps =
  match ops with
  | Some ops ->
    let get_pt ps =
      CR.get_proof (prove_by_admit "" ps) |> simplify_proof_tree
    in
    fsprintf "@\n  @[%a@]"
      (pp_list "@\n" (pp_proof_tree pp_unit ~hide_admit:true false))
      (diff_proof_tree (get_pt ops,get_pt nps))
  | None -> ""

(* pretty-print judgment *)
let pp_jus i fmt jus =
  match jus with
  | [] -> F.printf "No remaining goals, proof completed.@\n"
  | jus ->
    let n = L.length jus in
    let goal_num = if n = 1 then "" else F.sprintf " (of %i)" n in
    let pp_goal i ju =
      F.fprintf fmt "goal %i%s: %a@\n@\n" (i + 1) goal_num pp_ju ju
    in
    L.iteri pp_goal (L.take i jus)


let gpos_of_offset ju i =
  if i < 0 then L.length ju.ju_se.se_gdef + i + 1 else i

let epos_of_offset ju i =
  let ev = ju.ju_se.se_ev in
  if i < 0 && is_Land ev
  then L.length (destr_Land ev) + i + 1
  else i

let find_gvar ju s =
  let test = function
    | GLet(vs,_) | GSamp(vs,_) -> s = Id.name vs.VarSym.id
    | GAssert _ | GMSet _ -> false
    | GCall(vss,_,_,_) -> L.exists (fun vs -> s = Id.name vs.VarSym.id) vss
  in
  try find_at test ju.ju_se.se_gdef
  with Not_found -> tacerror "variable not found in game %s" s

let gpos_of_apos ju ap =
  match ap with
  | PT.AbsPos i -> i
  | PT.Var s    -> find_gvar ju s
  | PT.Pos i when i >= 0 -> (gpos_of_offset ju i) - 1
  | PT.Pos i -> (gpos_of_offset ju i)

let interval ju (i1,i2) =
  let i1 = O.map_default (gpos_of_apos ju) 0 i1 in
  let i2 =
    O.map_default_delayed (gpos_of_apos ju) (fun _ -> L.length ju.ju_se.se_gdef - 1) i2
  in
  i1, i2

let t_move inter delta ju =
  let (i1,i2) = interval ju inter in
  if i2 < i1 then tacerror "move: empty interval [%i .. %i]" i1 i2;
  let delta =
    match delta with
    | PT.Pos i -> i
    | PT.Var s ->
      let p = find_gvar ju s in
      if p <= i1 then p - i1
      else if p >= i2 then p - i2
      else tacerror "move: invalid position %s" s
    | PT.AbsPos p ->
      if p <= i1 then p - i1
      else if p >= i2 then p - i2
      else tacerror "move: invalid position %i" p
  in
  let li = list_from_to i1 (i2+1) in
  let lt = L.map (fun i -> T.t_move i delta) li in
  if delta < 0 then Rules.t_seq_fold lt ju
  else Rules.t_seq_fold (L.rev lt) ju

let ranges ju l =
  let l = L.map (interval ju) l in
  if l = [] then None else Some l
    
let parse_gdef vmap ts pgd =
  match pgd with
  | PT.Gname gn ->
    if not (Mstring.mem gn ts.ts_game_defs) then
      tacerror "undefined game: %s" gn;
    Mstring.find gn ts.ts_game_defs
  | PT.CmdList pgd ->
    PU.gdef_of_parse_gdef vmap ts pgd

let parse_se vmap ts pgd pev =
  let gd = parse_gdef vmap ts pgd in
  let ev = PU.expr_of_parse_expr vmap ts Unqual pev in
  let se = { se_gdef = gd; se_ev = ev } in
  Wf.wf_se Wf.NoCheckDivZero se;
  se

(* ** Tactic handling
 * ----------------------------------------------------------------------- *)

let handle_tactic ts tac =
  let ps = get_proof_state ts in
  let ju = match ps.CR.subgoals with
    | ju::_ -> ju
    | []    -> tacerror "cannot apply tactic: there is no goal"
  in
  let apply ?adecls r =
    try
      let ts = O.map_default (fun ad -> { ts with ts_adecls = ad }) ts adecls in
      let pss = T.apply_first r ps in
      begin match pull pss with
      | Left None      -> tacerror "tactic failed"
      | Left (Some s)  -> tacerror "%s" (Lazy.force s)
      | Right(nps,pss) ->
        let ops = Some ps in
        let ts' = { ts with ts_ps = ActiveProof(nps,[],pss,ops) } in
        (ts', lazy (diff_step ops nps))
      end
    with
    | Wf.Wf_div_zero es ->
      tacerror "Wf: Cannot prove that %a nonzero" (pp_list "," pp_expr) es
    | Wf.Wf_var_undef(v,e,def_vars) ->
      tacerror "Wf: Var %a undefined in %a, not in %a"
        VarSym.pp v pp_expr e
        (pp_list "," VarSym.pp) (VarSym.S.elements def_vars)
  in
  let rec interp_tac tac ju =
    let vmap_g = GameUtils.vmap_of_globals ju.ju_se.se_gdef in
    let e_pos = epos_of_offset ju in
    let get_pos = gpos_of_apos ju in

    let parse_e se = PU.expr_of_parse_expr vmap_g ts Unqual se in

    let parse_ev se =
      let vmap_se = GameUtils.vmap_of_se ju.ju_se in
      PU.expr_of_parse_expr vmap_se ts Unqual se
    in

    let mk_new_var sv ty =
      if (Ht.mem vmap_g (Unqual,sv)) then
        tacerror "Variable %s is already used" sv;
      VarSym.mk sv ty
    in
    match tac with
    | PT.Rnorm(do_strong)      -> t_norm ~fail_eq:false ~strong:do_strong ju
    | PT.Rnorm_nounfold        -> t_norm_nounfold ju
    | PT.Rlet_unfold([])       -> t_unfold_only ju
    | PT.Rlet_unfold(l)        ->
      let l = L.rev l in
      let lt = L.map (fun i ju -> t_let_unfold (gpos_of_apos ju i) ju) l in
      Rules.t_seq_fold lt ju

    | PT.Rmove(i,j)            -> t_move i j ju
    | PT.Rdist_eq              -> Rules.t_dist_eq ju
    | PT.Rdist_sym             -> T.t_dist_sym ju
    | PT.Rremove_ev(is)        -> T.t_remove_ev is ju
    | PT.Rsplit_ev(i)          -> T.t_split_ev (e_pos i) ju
    | PT.Rsplit_ineq(i)        -> SimpRules.t_split_ineq (e_pos i) ju
    | PT.Rrewrite_ev(i,d)      -> T.t_rw_ev (e_pos i) d ju
    | PT.Rcrush(finish,mi)     -> t_crush finish mi ts ps ju
    | PT.Rensure(oi,is_in,pe)   ->
      let e = parse_e pe in
      let oi = BatOption.map get_pos oi in
      Rules.t_occurs is_in e oi ju

      (* FIXME: all tactics interpreted wrt. the same theory state,
                OK for tactics that do not change the theory state. *)
    | PT.Rseq tacs ->
      t_seq_fold (L.map interp_tac tacs) ju

    | PT.Rcase_ev(Some(se)) ->
      T.t_case_ev (parse_ev se) ju

    | PT.Rsubst(i,e1,e2,mupto) ->
      t_subst (O.map_default get_pos 0 i) (parse_e e1) (parse_e e2)
              (O.map get_pos mupto) ju

    | PT.Rrename(v1,v2) ->
      let v1 = Ht.find vmap_g (Unqual,v1) in
      let v2 = mk_new_var v2 v1.VarSym.ty in
      t_rename v1 v2 ju

    | PT.Rcase_ev(None) ->
      t_case_ev_maybe ju

    | PT.Rexcept(Some(i),Some(ses)) ->
      T.t_except (get_pos i) (L.map (parse_e) ses) ju

    | PT.Rexcept(i,ses) ->
      t_rexcept_maybe (O.map get_pos i) ses ju

    | PT.Rmove_oracle(op,j)    -> T.t_move_oracle op j ju
    | PT.Rrewrite_orcl(op,dir) -> T.t_rewrite_oracle op dir ju

    | PT.Rfalse_ev             -> T.t_false_ev ju
    | PT.Rindep(exact)         -> t_random_indep ts exact ju

    | PT.Rnorm_unknown(is) ->
      let vs = L.map (fun s -> mk_V (Ht.find vmap_g (Unqual,s))) is in
      t_norm_unknown ts vs ju

    | PT.Rlet_abs(Some(i),sv,Some(se),mupto,no_norm) ->
      let e = parse_e se in
      let v = mk_new_var sv e.e_ty in
      t_let_abstract (get_pos i) v e (O.map get_pos mupto) (not no_norm) ju

    | PT.Rlet_abs_orcl(opos,sv,se,len,no_norm) ->
       let qual = Qual (PU.get_oname_from_opos ju.ju_se opos) in
       let vmap_o = GameUtils.vmap_in_orcl ju.ju_se opos in
       let e = PU.expr_of_parse_expr vmap_o ts qual se in
       let v = PU.create_var vmap_o ts qual sv e.e_ty in
       (*let v = mk_new_var sv e.e_ty in*)
       t_let_abstract_oracle opos v e len (not no_norm) ju

    | PT.Rlet_abs_ded(keep_going,i,sv,se,mupto) ->
      let e = parse_e se in
      let v = mk_new_var sv e.e_ty in
      t_abstract_deduce ~keep_going ts (get_pos i) v e (O.map get_pos mupto) ju

    | PT.Rassert(i,Some se) ->
      let e = parse_e se in
      T.t_assert (get_pos i) e ju

    | PT.Rassert(i,None) ->
      let t_remove_assert ju =
        let se = ju.ju_se in
        match get_se_ctxt se (get_pos i) with
        | GAssert(e), sec ->
          let se_new = set_se_ctxt [] sec in
          (T.core_tactic (CR.ct_trans se_new)
           @>> [ T.core_tactic CR.ct_dist_sym @> T.core_tactic (CR.ct_assert (get_pos i) e)
                 @>> [ T.t_id; Rules.t_dist_eq]
               ; T.t_id ]) ju
        | _ ->
          tacerror "no assert at given position %i" (get_pos i)
      in
      t_remove_assert ju

    | PT.Rmove_to_main(i_j_k,vs)  -> 
      T.core_tactic (CR.ct_move_main i_j_k vs) ju 

    | PT.Rmove_to_orcl(p,(i,j,k),sv) ->
      let ci = get_pos p in
      if (ci + 1<>i) then
        tacerror "move_to_main: variable in main must directly precede oracle";
      if (k<>0) then
        tacerror "move_to_main: can only move variable to start of oracle";
      let t_move_to_orcl ju =
        log_i (lazy (fsprintf "i=%i j=%i k=%i" i j k));
        let se = ju.ju_se in
        assert (ci < i);
        let op = (i,j,k,Oishyb OHeq) in
        let _, seoc =  get_se_octxt_len se op 0 in
        let oname = Id.name seoc.seoc_osym.OrclSym.id in
        match split_n ci (L.rev seoc.seoc_sec.sec_left) with
        | cleft, GSamp(vsm,d), cright ->
          log_i (lazy (fsprintf "cleft=%a cright=%a"
                         (pp_gdef ~nonum:false) cleft (pp_gdef ~nonum:false) cright));
          let vmap = Hashtbl.create 17 in
          let vso = PU.create_var vmap ts (Qual oname) sv vsm.VarSym.ty in
          let subst e = e_replace (mk_V vsm) (mk_V vso) e in
          let seoc =
            { seoc with
              seoc_return = subst seoc.seoc_return;
              seoc_sec =
                { sec_left = L.rev (L.rev_append cleft cright);
                  sec_right = L.map (map_gcmd_exp subst) seoc.seoc_sec.sec_right;
                  sec_ev = subst seoc.seoc_sec.sec_ev; } }
          in
          let lcright = L.map (map_lcmd_exp subst) seoc.seoc_cright in
          let se = set_se_octxt [LSamp(vso,d)] { seoc with seoc_cright = lcright } in
          (T.t_trans se @>> [ T.t_dist_sym
                               @> T.t_move_main (i-1,j,k) "rr" @> t_dist_eq
                             ; T.t_id]) ju
        | _ -> tacerror "cannot move instruction to oracle, given position not a sampling"
      in
      t_move_to_orcl ju

    | PT.Rlet_abs(None,sv,None,mupto,no_norm) ->
      let v = mk_new_var sv ju.ju_se.se_ev.e_ty in
      let max = L.length ju.ju_se.se_gdef in
      t_let_abstract max v ju.ju_se.se_ev (O.map get_pos mupto) (not no_norm) ju

    | PT.Rlet_abs(_,_,_,_,_) ->
      tacerror "No placeholders or placeholders for both position and event"

    | PT.Rconv(Some sgd,sev) ->
      let vmap2 = Hashtbl.create 134 in
      let gd2 = parse_gdef vmap2 ts sgd in
      let ev2 = PU.ev_of_parse_ev vmap2 ts sev in
      T.t_conv true { se_gdef = gd2; se_ev = ev2 } ju

    | PT.Rconv(None,sev) ->
      let ev2 = PU.ev_of_parse_ev vmap_g ts sev in
      T.t_conv true { se_gdef = ju.ju_se.se_gdef; se_ev = ev2 } ju

    | PT.Rmatunfold(Some which, i, p) ->
      T.t_matunfold which i p ju

    | PT.Rmatunfold(None, i, p) ->
      T.t_matunfold true i p ju

    | PT.Rmatfold(Some which, i, j, m) -> T.t_matfold which i j m ju

    | PT.Rmatfold(None, i, j, m) -> T.t_matfold true i j m ju

    | PT.Rtrans(sgd,sev) ->
      let vmap2 = Hashtbl.create 134 in
      let gd2 = parse_gdef vmap2 ts sgd in
      let ev2 = PU.ev_of_parse_ev vmap2 ts sev in
      T.t_trans { se_gdef = gd2; se_ev = ev2 } ju

    | PT.Rtrans_diff(dcmds) ->
      let vmap = Hashtbl.copy vmap_g in
      let rec app_diff dcmds ju =
        let get_pos = gpos_of_apos ju in
        let se = ju.ju_se in
        match dcmds with
        | [] -> ju.ju_se
        | PT.Drename(v1,v2,mupto)::dcmds ->
          let v1 = Ht.find vmap (Unqual,v1) in
          let v2 = mk_new_var v2 v1.VarSym.ty in
          let maxlen = L.length se.se_gdef in
          let mupto = O.map (fun p -> succ (get_pos p)) mupto in
          let rn_len = O.default maxlen mupto in
          let a_cmds, sec = get_se_ctxt_len se ~pos:0 ~len:rn_len in
          let sigma v = if VarSym.equal v v1 then v2 else v in
          let a_cmds = subst_v_gdef sigma a_cmds in
          let ev = if mupto=None then subst_v_expr sigma sec.sec_ev else sec.sec_ev in
          app_diff dcmds { ju with ju_se = (set_se_ctxt a_cmds { sec with sec_ev = ev }) }
        | PT.Dsubst(p,e1,e2)::dcmds ->
          let p = get_pos p in
          let e1 = PU.expr_of_parse_expr vmap ts Unqual e1 in
          let e2 = PU.expr_of_parse_expr vmap ts Unqual e2 in
          let subst a = e_replace e1 e2 a in
          let l,r = cut_n p se.se_gdef in
          let new_se =
            { se_gdef = L.rev_append l (map_gdef_exp subst r);
              se_ev   = subst se.se_ev }
          in
          app_diff dcmds { ju with ju_se = new_se }
        | PT.Dinsert(p,gcmds)::dcmds ->
          let i = get_pos p in
          let _, sec = get_se_ctxt_len se ~pos:i ~len:0 in
          let gcmds = PU.gdef_of_parse_gdef vmap ts gcmds in
          app_diff dcmds { ju with ju_se = (set_se_ctxt gcmds sec) }
      in
      let t_diff ju =
        T.t_trans (app_diff dcmds ju) ju
      in
      t_diff ju

    | PT.Rassm_dec(exact,maname,mdir,mrngs,msvs) ->
      t_assm_dec ts exact maname mdir (ranges ju mrngs) msvs ju

    | PT.Rassm_dec_o(maname,mdir,ren,rngs) ->
      t_assm_dec_o ts maname mdir ren rngs ju

    | PT.Rnorm_solve(se) ->
      let e = parse_e se in
      RewriteRules.t_norm_solve e ju

    | PT.Rexcept_orcl(op,pes) ->
      let vmap = GameUtils.vmap_in_orcl ju.ju_se op in
      let es = L.map (PU.expr_of_parse_expr vmap ts Unqual) pes in
      T.t_except_oracle op es ju

    | PT.Rctxt_ev (mj,Some(sv,_mt,e)) ->
      let j = match mj with
        | Some j -> j
        | None -> tacerror "position placeholder not allowed if context is given"
      in
      let ev = ju.ju_se.se_ev in
      let b =
        match ev.e_node with
        | Nary(Land,es) when j < L.length es ->
          L.nth es j
        | _ when j = 0 -> ev
        | _ -> tacerror "rctxt_ev: bad index"
      in
      let ty =
        if is_Eq b then (fst (destr_Eq b)).e_ty
        (* else if is_Exists b then
          let (e1,_,_) = destr_Exists b in e1.e_ty *)
        else tacerror "rctxt_ev: bad event"
      in
      let vmap = GameUtils.vmap_of_globals ju.ju_se.se_gdef in
      let v1 = PU.create_var vmap ts Unqual sv ty in
      let e1 = PU.expr_of_parse_expr vmap ts Unqual e in
      let c = v1, e1 in
      T.t_ctxt_ev j c ju

    | PT.Rctxt_ev (mj,None) ->
      SimpRules.t_ctx_ev_maybe mj ju

    | PT.Rsimp must_finish ->
      SimpRules.t_simp must_finish 20 ju

    | PT.Rassm_comp(exact,maname,mrngs) ->
      t_assm_comp ts exact maname (ranges ju mrngs) ju

    | PT.Rrnd(exact,mi,mctxt1,mctxt2,mgen) ->
      let mgen = O.map parse_e mgen in
      t_rnd_maybe ts exact (O.map get_pos mi) mctxt1 mctxt2 mgen ju

    | PT.Rrnd_exp(exact,ids) ->
      let to_tac (i,mi2) =
        let v = Ht.find vmap_g (Unqual,i) in
        let ename =
          let li = String.lowercase i in
          O.default (if li<>i then li else "e_"^i) mi2
        in
        let gname = destr_G_exn v.VarSym.ty in
        let e = PT.Exp(PT.CGen (Groupvar.name gname), PT.V(Unqual,ename)) in
        PT.Rrnd(exact,Some (PT.Var i), Some (ename,Some PT.Fq,e),None,None)
      in
      t_seq_fold (L.map (fun i -> interp_tac (to_tac i)) ids) ju

    | PT.Rrnd_orcl(mopos,mctxt1,mctxt2) ->
      t_rnd_oracle_maybe ts mopos mctxt1 mctxt2 ju

    | PT.Rhybrid((i,j),(lcmds,eret)) ->
      let se = ju.ju_se in
      let opos = (i,j,0,Onothyb) in
      let vmap = GameUtils.vmap_in_orcl se opos in
      let _, seoc = get_se_octxt se opos in
      let oname = Id.name seoc.seoc_osym.OrclSym.id in
      let lcmds = L.map (PU.lcmd_of_parse_lcmd vmap ts ~oname) lcmds in
      let eret = PU.expr_of_parse_expr vmap ts (Qual oname) eret in
      T.t_hybrid i j lcmds eret ju

    | PT.Radd_test(_) | PT.Deduce(_) | PT.FieldExprs(_) | PT.Rguard _ ->
      tacerror "add_test and debugging tactics cannot be combined with ';'"

    | PT.Rbad(1,Some _ap,_vsx) -> fixme "undefined" (*
       let p = gpos_of_apos ju ap in
       let gen_vsx e = if (Ht.mem vmap_g (Unqual,_vsx)) then
                         Ht.find vmap_g (Unqual,_vsx) else
                         PU.create_var vmap_g ts Unqual _vsx e.Expr.e_ty in
      CR.t_bad UpToBad p gen_vsx ju *)
    | PT.Rbad(2,Some _ap,_vsx) -> fixme "undefined" (*
       let p = gpos_of_apos ju ap in
       let gen_vsx e = if (Ht.mem vmap_g (Unqual,_vsx)) then
                         Ht.find vmap_g (Unqual,_vsx) else
                         PU.create_var vmap_g ts Unqual _vsx e.Expr.e_ty in
      CR.t_bad CaseDist p gen_vsx ju *)

    | PT.Rsep_dom(ms1,ms2) ->
      begin try
        let ms1 = Mstring.find ms1 ts.ts_fmapdecls in
        let ms2 = Mstring.find ms2 ts.ts_fmapdecls in
        if not (   equal_ty ms1.MapSym.dom ms1.MapSym.dom
                && equal_ty (mk_Prod []) ms2.MapSym.codom) then
          tacerror "sep_dom: invalid arguments.";
        T.t_sep_dom ms1 ms2 ju
      with Not_found ->
        assert false
      end

    | PT.Rcheck_hash_args(_opos) -> fixme "undefined" (*
       let gen_o_lkup o  = Mstring.find (Fsym.to_string o) ts.ts_lkupdecls in
       CR.t_check_hash_args opos gen_o_lkup ju *)

    | PT.Rbad _ -> tacerror "Wrong RBad tactic call in Tactic.ml";

    | PT.Rguess(aname, fvs) ->
      if (Mstring.mem aname ts.ts_adecls) then
        tacerror "rguess: adversary with same name already declared";
      let ev = ju.ju_se.se_ev in
      let vs =
        match destr_Quant ev with
        | (Exists,(vs,_o),_e) -> vs
        | _ ->  tacerror "rguess: invalid binding"
      in
      let asym = AdvSym.mk aname (mk_Prod []) (ty_prod_vs vs) in
      if not (L.length fvs = L.length vs) then
        tacerror "Error, 'guess' rule requires %i variable(s), but got %i"
                 (L.length vs) (L.length fvs);
      let vmap = GameUtils.vmap_of_globals ju.ju_se.se_gdef in
      let fvs =
        L.map2 (fun v v' -> PU.create_var vmap ts Unqual v v'.VarSym.ty)
          fvs vs
      in
      T.t_guess asym fvs ju

    | PT.Rfind((bd,body),arg,aname,fvs) ->
      if (Mstring.mem aname ts.ts_adecls) then
        tacerror "rguess: adversary with same name already declared";
      let ev = ju.ju_se.se_ev in
      let vs =
        match destr_Quant ev with
        | (Exists,(vs,_),_) -> vs
        | _ ->  tacerror "rfind: invalid binding"
      in
      let arg = parse_e arg in
      let asym = AdvSym.mk aname (arg.e_ty) (ty_prod_vs vs) in
      if not (L.length fvs = L.length vs) then
        tacerror "Error, 'find' rule requires here %i variable(s), but got %i"
          (L.length vs) (L.length fvs);
      let vmap = GameUtils.vmap_of_globals ju.ju_se.se_gdef in
      let fvs =
        L.map2 (fun v v' -> PU.create_var vmap ts Unqual v v'.VarSym.ty)
          fvs vs in
      (* typing of f *)
      let f =
        let vmap_se = GameUtils.vmap_of_se ju.ju_se in
        let bd =
          L.map2 (fun v e -> PU.create_var vmap_se ts Unqual v e.e_ty)
            bd (destr_Tuple_nofail arg) in
        let body =
          PU.expr_of_parse_expr vmap_se ts Unqual body in
        bd,body in

      T.t_find f arg asym fvs ju
  in

  let vmap_g = GameUtils.vmap_of_globals ju.ju_se.se_gdef in
  match tac with
  | PT.Radd_test(Some(opos),Some(t),Some(aname),Some(fvs)) ->
    (* create symbol for new adversary *)
    let se = ju.ju_se in
    let _, seoc = get_se_octxt se opos in
    let vmap = GameUtils.vmap_in_orcl se opos in
    let oasym = seoc.seoc_asym in
    let oname = Id.name seoc.seoc_osym.OrclSym.id in
    let t = PU.expr_of_parse_expr vmap ts (Qual oname) t in
    let oty = seoc.seoc_osym.OrclSym.dom in
    let destr_prod ty = match ty.ty_node with
      | Prod(tys) -> tys
      | _ -> [ty]
    in
    if (Mstring.mem aname ts.ts_adecls) then
      tacerror "radd_test: adversary with same name already declared";
    let asym = AdvSym.mk aname oasym.AdvSym.dom oty in
    let adecls = Mstring.add aname asym ts.ts_adecls in
    let tys = destr_prod oty in
    (* create variables for returned values *)
    if not (L.length fvs = L.length seoc.seoc_oargs) then
      tacerror "number of given variables does not match type";
    let fvs =
      match fvs with
      | [fv] -> [ PU.create_var vmap ts Unqual fv oty ]
      | _    -> L.map2 (fun v ty -> PU.create_var vmap ts Unqual v ty) fvs tys
    in
    apply ~adecls (T.t_add_test opos t asym fvs)

  | PT.Radd_test(None,None,None,None) ->
    apply t_guard_maybe

  | PT.Radd_test(_,_,_,_) ->
    tacerror "radd_test expects either all values or only placeholders"

  | PT.Deduce(ppt,pes,pe) ->
    let es = L.map (PU.expr_of_parse_expr vmap_g ts Unqual) pes in
    let e = PU.expr_of_parse_expr vmap_g ts Unqual pe in
    log_i (lazy (fsprintf "deduce %a |- %a@\n" (pp_list "," pp_expr) es pp_expr e));
    (try
        let frame =
          L.mapi
            (fun i e -> (e, I (mk_V (VarSym.mk ("x"^(string_of_int i)) e.e_ty))))
            es
        in
        let recipe = Deduc.invert ~ppt_inverter:ppt ts frame e in
        let msg = fsprintf "Found %a@\n" pp_inverter recipe in
        log_i (lazy msg);
        (ts,lazy msg)
      with
        Not_found ->
        tacerror "Not found@\n")

  | PT.FieldExprs(pes) ->
    let es = L.map (PU.expr_of_parse_expr vmap_g ts Unqual) pes in
    let ses = ref Se.empty in
    Game.iter_se_exp ~iexc:true
      (fun e' -> e_iter_ty_maximal mk_Fq
        (fun fe -> if L.exists (fun e -> e_exists (equal_expr e) fe) es
                   then ses := Se.add fe !ses) e')
      ju.ju_se;
    let res = (lazy (fsprintf "field expressions with %a: @\n@[<hov 2>  %a@]"
                      (pp_list ", " pp_expr) es
                      (pp_list ",@\n" pp_expr) (Se.elements !ses)))
    in
    log_i res;
    (ts,res)

  (* remaining tactics that can be nested with seq *)
  | PT.Rguard(opos, t) ->
    (* create symbol for new adversary *)
    let se = ju.ju_se in
    let seoc =
      if t = None then snd (get_se_octxt se opos)
      else snd (get_se_octxt_len se opos 0)
    in
    let vmap = GameUtils.vmap_in_orcl se opos in
    let oname = Id.name seoc.seoc_osym.OrclSym.id in
    let t = O.map (PU.expr_of_parse_expr vmap ts (Qual oname)) t in
    apply (T.t_guard opos t)

  | _ ->
    apply (interp_tac tac)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Instruction handling} *)

let rec handle_instr verbose ts instr =
  match instr with

  (* FIXME: do not ignore *)
  | PT.BoundDecl(_b,_i) -> (ts,fsprintf "not implemented yet")

  | PT.FunDecl(s,t1,t2) ->
    if Mstring.mem s ts.ts_constdecls then
      tacerror "operator with same name already declared.";
    let dom, codom = (PU.ty_of_parse_ty ts t1, PU.ty_of_parse_ty ts t2) in
    let hs = FunSym.mk s dom codom in
    let ts_fundecls = Mstring.add s hs ts.ts_constdecls in
    let ts = { ts with ts_constdecls = ts_fundecls } in
    (ts, fsprintf "Declared operator %s" s)
    
  | PT.FMDecl(s,t1,t2) ->
    let dom, codom = (PU.ty_of_parse_ty ts t1, PU.ty_of_parse_ty ts t2) in
    begin try
      let hs = Mstring.find s ts.ts_fmapdecls in
      if not (equal_ty hs.MapSym.dom dom && equal_ty hs.MapSym.codom codom) then
        tacerror "Finite map with same name already declared.";
      (ts, fsprintf "Finite map %s with identical type already declared." s)
    with Not_found ->
      let hs = MapSym.mk s dom codom in
      let ts_fmapdecls = Mstring.add s hs ts.ts_fmapdecls in
      let ts = { ts with ts_fmapdecls = ts_fmapdecls } in
      (ts, fsprintf "Declared finite map %s" s)
    end

  | PT.RODecl(s,t1,t2) | PT.RFDecl(s,t1,t2) ->
    let dom, codom = (PU.ty_of_parse_ty ts t1, PU.ty_of_parse_ty ts t2) in
    begin try
      let hs = Mstring.find s ts.ts_rodecls in
      if not (equal_ty hs.RoSym.dom dom && equal_ty hs.RoSym.codom codom) then
        tacerror "random oracle with same name already declared.";
      (ts, fsprintf "Random oracle %s with identical type already declared." s)
    with Not_found ->
      let hs = RoSym.mk s dom codom in
      let ts_rodecls = Mstring.add s hs ts.ts_rodecls in
      let ts = { ts with ts_rodecls = ts_rodecls } in
      (ts, fsprintf "Declared random oracle %s" s)
    end

  | PT.TyDecl(s) ->
    if Mstring.mem s ts.ts_tydecls then
      tacerror "Type with the same name already declared.";
    let tsym = Tysym.mk s in 
    let ts = { ts with ts_tydecls = Mstring.add s tsym ts.ts_tydecls } in
    (ts, fsprintf "Declared type %s" s)


  | PT.EMDecl(s,g1,g2,g3) ->
    if Mstring.mem s ts.ts_emdecls then
      tacerror "Bilinear map with same name already declared.";
    let es = EmapSym.mk s (create_groupvar ts g1) (create_groupvar ts g2) (create_groupvar ts g3) in
    let ts = { ts with ts_emdecls = Mstring.add s es ts.ts_emdecls } in
    (ts, "Declared bilinear map.")

  | PT.ODecl(s,t1,t2) ->
    if Mstring.mem s ts.ts_odecls then
      tacerror "Oracle with same name already declared.";
    let os = OrclSym.mk s (PU.ty_of_parse_ty ts t1) (PU.ty_of_parse_ty ts t2) in
    let ts = { ts with ts_odecls = Mstring.add s os ts.ts_odecls } in
    (ts, Util.fsprintf "Declared oracle: %a" OrclSym.pp_long os)

  | PT.ADecl(s,t1,t2) ->
    if Mstring.mem s ts.ts_adecls then
      tacerror "adversary with same name already declared.";
    let asym = AdvSym.mk s (PU.ty_of_parse_ty ts t1) (PU.ty_of_parse_ty ts t2) in
    let ts = { ts with ts_adecls = Mstring.add s asym ts.ts_adecls } in
    (ts, Util.fsprintf "Declared adversary: %a" AdvSym.pp_long asym)

  | PT.AssmDec(s,inf,g0,g1,symvs) ->
    let vmap1 = Ht.create 137 in
    let vmap2 = Ht.create 137 in 
    let g0 = PU.gdef_of_parse_gdef vmap1 ts g0 in
    let g1 = PU.gdef_of_parse_gdef vmap2 ts g1 in
    (* create the var map of the two games *)
    let vmap1 = GameUtils.create_vmap (game_vars g0) in
    let vmap2 = GameUtils.create_vmap (game_vars g1) in
    let vmap, sigma = GameUtils.merge_vmap vmap1 vmap2 in
    let g1 = subst_v_gdef sigma g1 in
    let parse_var s =
      try  Ht.find vmap (Unqual,s)
      with Not_found -> tacerror "unknown variable %s" s
    in
    let symvs = L.map (L.map parse_var) symvs in
    if Mstring.mem s ts.ts_assms_dec then
      tacerror "assumption with the same name already exists";
    let ts = {
      ts with
        ts_assms_dec =
        Mstring.add s (Assumption.mk_assm_dec s inf g0 g1 symvs) ts.ts_assms_dec
    }
    in
    (ts, "Declared decisional assumption.")

  | PT.AssmComp(s,inf,at,g,ev,symvs) ->
    let vmap = Ht.create 137 in
    let g = PU.gdef_of_parse_gdef vmap ts g in
    let parse_var s =
      try  Ht.find vmap (Unqual,s)
      with Not_found -> tacerror "unknown variable %s" s
    in
    let symvs = L.map (L.map parse_var) symvs in
    let ev = PU.ev_of_parse_ev vmap ts ev in
    let assm = Assumption.mk_assm_comp s inf at g ev symvs in
    if Mstring.mem s ts.ts_assms_comp then
      tacerror "assumption with the same name already exists";
    let ts = { ts with ts_assms_comp = Mstring.add s assm ts.ts_assms_comp } in
    (ts, "Declared computational assumption.")

  | PT.GameDef(s,gd) ->
    let vmap = Ht.create 137 in
    let gd = parse_gdef vmap ts gd in
    if Mstring.mem s ts.ts_assms_comp then
      tacerror "game with the same name already exists";
    let ts = {ts with ts_game_defs = Mstring.add s gd ts.ts_game_defs } in
    (ts, fsprintf "Defined game: %s := @\n%a" s (pp_gdef ~nonum:false) gd)

  | PT.JudgAdv(gd,e) | PT.JudgSucc(gd,e)->
    let vmap = Ht.create 137 in
    let se = parse_se vmap ts gd e in
    let pt = match instr with PT.JudgAdv _ -> Pr_Adv | _ -> Pr_Succ in
    let ju = { ju_se = se; ju_pr = pt } in
    let ps = first (T.t_id ju) in
    ({ ts with ts_ps = ActiveProof(ps,[],mempty,None) }
    , "Started proof of judgment.")

  | PT.JudgDist(gd1,e1,gd2,e2) ->
    let vmap1 = Ht.create 137 in
    let se1 = parse_se vmap1 ts gd1 e1 in
    let vmap2 = Ht.create 137 in
    let se2 = parse_se vmap2 ts gd2 e2 in
    let ju = { ju_se = se1; ju_pr = Pr_Dist se2 } in
    let ps = first (T.t_id ju) in
    ({ ts with ts_ps = ActiveProof(ps,[],mempty,None) }
    , "Started proof of judgment.")

  | PT.Apply(tac) ->
    let (ts,s) = handle_tactic ts tac in
    (ts, "Applied tactic"^(if verbose then ":"^Lazy.force s else "."))

  | PT.Back ->
    begin match ts.ts_ps with
    | ActiveProof(_,uback,back,ops) ->
      begin match pull back with
      | Left _ -> tacerror "Cannot backtrack"
      | Right(ps',pss) ->
        let ts' =
          { ts with ts_ps = ActiveProof(ps',(get_proof_state ts)::uback,pss,ops) }
        in
        (ts', "Backtracked to next alternative:"^diff_step ops ps')
      end
    | _ -> tacerror "last: no goals"
    end

  | PT.UndoBack(false) ->
    begin match ts.ts_ps with
    | ActiveProof(_,uback,back,ops) ->
      begin match uback with
      | [] -> tacerror "Cannot undo backtrack"
      | ps'::pss ->
        ({ ts with
           ts_ps = ActiveProof(ps',pss,mplus (ret (get_proof_state ts)) back,ops) }
        , "Backtracked to previous alternative:"^diff_step ops ps')
      end
    | _ -> tacerror "last: no goals"
    end

  | PT.UndoBack(true) ->
    begin match ts.ts_ps with
    | ActiveProof(_,uback,back,ops) ->
      begin match L.rev uback with
      | [] -> tacerror "Cannot undo backtrack"
      | ps'::pss ->
        let back' = mplus (mconcat pss) (mplus (ret (get_proof_state ts)) back) in
        ({ ts with
           ts_ps = ActiveProof(ps',[],back',ops) }
        , "Backtracked to first alternative:"^diff_step ops ps')
      end
    | _ -> tacerror "last: no goals"
    end

  | PT.Last ->
    begin match ts.ts_ps with
    | ActiveProof(ps,uback,back,ops) ->
      ({ ts with ts_ps = ActiveProof(T.move_first_last ps,uback,back,ops) }
      , "Delayed current goal")
    | _ -> tacerror "last: no goals"
    end

  | PT.Admit ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_,_,_) ->
      ({ts with ts_ps =
          ActiveProof(first (T.apply_first (T.t_admit "") ps),[],mempty,Some(ps))}
      , "Admit goal.")
    | _ -> tacerror "admit: no goals"
    end

  | PT.PrintGoals(s) ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_uback,_back,_) ->
      let msg = fsprintf "@[<v>Proof state %s:@\n%a@]" s (pp_jus 100) ps.CR.subgoals in
      (ts, msg)
    | BeforeProof    -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Theory closed.")
    end

  | PT.PrintProof(verbose,mfile) ->
    begin match ts.ts_ps with
    | BeforeProof -> (ts, "No proof started yet.")
    | ActiveProof _ | ClosedTheory _ ->
      let pt =
        match ts.ts_ps with
        | BeforeProof -> assert false
        | ClosedTheory pt          -> pt
        | ActiveProof  (ps,_,_,_)  -> CR.get_proof (prove_by_admit "" ps)
      in
      let pt = simplify_proof_tree pt |> decorate_proof_tree in
      let buf = Buffer.create 1024 in
      let fbuf = F.formatter_of_buffer buf in
      F.pp_set_margin fbuf 240;
      F.fprintf fbuf "%a" (pp_proof_tree pp_path verbose) pt;
      (match mfile with
       | Some filename ->
         let out = open_out filename in
         let fmt = F.formatter_of_out_channel out in
         F.pp_set_margin fmt 240;
         F.fprintf fmt "%a" (pp_proof_tree pp_path verbose) pt;
         close_out out
       | None -> ());
      (ts, Buffer.contents buf)
    end

  | PT.PrintGoal(s) ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_uback,_back,_) ->
      let msg = fsprintf "Current goal in state %s:%a@."
        s
        (pp_jus 100)
        (L.take 1 ps.CR.subgoals)
      in
      (ts, msg)
    | BeforeProof -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Proof finished.")
    end

  | PT.Restart ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_uback,_back,_) ->
      let prf = CR.get_proof (prove_by_admit "" ps) in
      let ps = first (T.t_id prf.CR.pt_ju) in
      ({ts with ts_ps = ActiveProof(ps,[],mempty,None) }, "Restarted proof.")
    | BeforeProof    -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Proof finished.")
    end

  | PT.Qed ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_uback,_back,_) ->
      if ps.CR.subgoals = [] then
        ({ts with ts_ps = ClosedTheory (ps.CR.validation [])}, "Finished proof.")
      else
        tacerror "Cannot finish proof, open goals."
    | BeforeProof    -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Proof finished.")
    end

  | PT.Extract _filename ->
    (*  Extraction.extract ts filename;
        (ts, "EasyCrypt proof script extracted into file: "^filename) *)
    (ts,"Extraction currently disabled")

  | PT.PrintGame filename ->
    let ps = get_proof_state ts in
    let ju = match ps.CR.subgoals with
      | ju::_ -> ju
      | []    -> tacerror "cannot print game: there is no goal"
    in
    output_file filename (fsprintf "%a" pp_se_nonum ju.ju_se);
    (ts, "Current game printed into file: "^filename)

  | PT.PrintGames(fn1,fn2) ->
    let ps = get_proof_state ts in
    let se1,se2 = match ps.CR.subgoals with
      | ju::_ ->
        begin match ju.ju_pr with
        | Pr_Dist se2 -> (ju.ju_se,se2)
        | _ -> tacerror "cannot print game: judgment of wrong type"
        end
      | [] -> tacerror "cannot print games: there is no goal"
    in
    ExprUtils.pp_sort_expensive := true;
    ExprUtils.pp_number_tuples := true;
    output_file fn1 (fsprintf "%a" pp_se_nonum se1);
    output_file fn2 (fsprintf "%a" pp_se_nonum se2);
    ExprUtils.pp_sort_expensive := false;
    ExprUtils.pp_number_tuples := false;
    (ts, F.sprintf "Current games printed into files: %s and %s" fn1 fn2)

  | PT.Debug cmd ->
    begin match cmd with
    | "cases" ->
      CaseRules.print_cases ts
    | "alternatives" ->
      begin match ts.ts_ps with
      | ActiveProof(_,_,back,_) ->
        (ts, F.sprintf "There are %i alternatives left." (L.length (run (-1) back)))
      | BeforeProof  -> (ts, "No proof started yet.")
      | ClosedTheory _ -> (ts, "Proof finished.")
      end

    | _ ->
      tacerror "Unknown debug command."
    end

  | PT.Include(fn) ->
    if L.mem fn !included then (ts,"file already included earlier")
    else (
      let s = input_file (fn^".zc") in
      included := fn::!included;
      let pt = Parse.theory s in
      handle_instrs true ts pt
    )

and handle_instrs verbose ts instrs =
  L.fold_left (fun (ts,s) instr ->
    let (ts',s') = handle_instr verbose ts instr in
    (ts',s^"\n"^s'))
    (ts,"")
    instrs

let eval_theory s =
  let pt = Parse.theory s in
  let empty_ts = mk_ts () in
  L.fold_left
    (fun ts i ->
      let (ts', s) = handle_instr false ts i in
      print_endline s;
      ts')
    empty_ts
    pt
