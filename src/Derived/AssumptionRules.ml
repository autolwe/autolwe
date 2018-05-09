(* * Derived tactics for dealing with assumptions. *)

(* ** Imports and abbreviations *)
open Abbrevs
open Util
open Nondet
open Type
open Assumption
open Syms
open Expr
open ExprUtils
open Game
open TheoryTypes
open Rules
open CoreTypes
open RewriteRules

module Ht = Hashtbl
module CR = CoreRules
module T = Tactic
module PU = ParserUtil

let mk_log level = mk_logger "Derive.AssumptionRules" level "AssumptionRules.ml"
let log_i = mk_log Bolt.Level.INFO
let log_t = mk_log Bolt.Level.TRACE
let log_d = mk_log Bolt.Level.DEBUG

(* ** Decisional assumptions
 * ----------------------------------------------------------------------- *)
  
let assumption_vars assm =
  let addv se v = Se.add (mk_V v) se in
  let se = 
    Se.union (write_gcmds assm.ad_prefix1) (write_gcmds assm.ad_prefix2) in
  let add_do se (_, vs, ((b1,_),(b2,_)), _) = 
    let se = List.fold_left addv se vs in
    let se = Se.union se (write_lcmds b1) in
    Se.union se (write_lcmds b2) in
  let add_ac se ad_ac = 
    let se = List.fold_left addv se ad_ac.ad_ac_lv in
    List.fold_left add_do se ad_ac.ad_ac_orcls in
  let se = 
    List.fold_left add_ac se assm.ad_acalls in
  sv_of_se se 
    

let t_assm_dec_o ts name dir ren (rngs:ParserTypes.range_o list) ju =
  let rn = "assumption_decisional" in
  let assm =
    try Mstring.find name ts.ts_assms_dec
    with Not_found -> tacerror "%s: error no assumption %s" rn name
  in
  let assm_vars = assumption_vars assm in
  (* create the renaming *)
  let addv mvar v = 
    let q = map_qual OrclSym.to_string v.VarSym.qual in
    let x = Id.name v.VarSym.id in
    Hashtbl.add mvar (q,x) v in
  let avars = Hashtbl.create 10 in
  VarSym.S.iter (addv avars) assm_vars;
  let gvars = Hashtbl.create 10 in
  VarSym.S.iter (addv gvars) (game_vars ju.ju_se.se_gdef);
  let find_var fail mvar qx = 
    try Hashtbl.find mvar qx 
    with Not_found when fail -> 
      let pp_qx fmt (q,x) = 
        match q with
        | Unqual -> Format.fprintf fmt "%s" x
        | Qual q -> Format.fprintf fmt "%s.%s" q x in
      tacerror "%s: unknown variable %a" rn pp_qx qx
  in
  let mk_o o = 
    try Mstring.find o ts.ts_odecls 
    with Not_found ->
      tacerror "%s: unknown oracle %s" rn o in
  let add_ren ren (qx, qx') = 
    let x = find_var true avars qx in
    let x' = 
      try find_var false gvars qx' 
      with Not_found ->
        let q',x' = qx' in
        let q' = map_qual mk_o q' in
        VarSym.mk_qual x' q' x.VarSym.ty in
    VarSym.M.add x x' ren in
  let ren = List.fold_left add_ren VarSym.M.empty ren in

  let mk_rng (i,j,ros) = 
    let mk_ro ro = 
      match ro with
      | ParserTypes.RO_main(i,j,o) -> 
        RO_rng(i-1,j-1,mk_o o)
      | ParserTypes.RO_in_o (i,os) ->
        let tbl = Hashtbl.create 10 in
        let dok (k,otype,r) =
          let dor (i,j,o) = (i-1,j-1,mk_o o) in
          Hashtbl.add tbl (k-1,otype) (List.map dor r) in
        List.iter dok os;
        let f k ot = try Hashtbl.find tbl (k,ot) with Not_found -> [] in
        RO_orcl (i-1, f) in
    { r_start = i-1;
      r_end   = j-1;
      r_orcl  = List.map mk_ro ros;} in
  let rngs = List.map mk_rng rngs in
  T.t_assm_dec dir ren rngs assm ju

let t_assm_dec_exact ts massm_name mdir mrngs mvnames ju =
  let rn = "assumption_decisional" in
  let fail_opt mo s = fail_opt mo (rn^": "^s) in
  let se = ju.ju_se in
  let dir = fail_opt mdir "requires direction" in
  let assm_name = fail_opt massm_name "requires assumption" in
  let assm =
    try Mstring.find assm_name ts.ts_assms_dec
    with Not_found -> tacerror "%s: error no assumption %s" rn assm_name
  in
  let rngs = fail_opt mrngs "requires ranges" in
  let vneeded = needed_vars_dec dir assm in
  let acalls  = assm.ad_acalls in
  let vnames = match mvnames with
    | Some names                      -> names
    | None when L.length vneeded <> 0 -> tacerror "exact required vnames"
    | None                            -> []
  in
  if L.length vneeded <> L.length vnames then
    tacerror "%s: wrong number of variables" rn;
  if L.length acalls <> L.length rngs then tacerror "%s: Wrong number of ranges" rn;
  (* initial renaming with mappings from needed variables to given variables *)
  let ren =
    List.fold_left2
      (fun s v x -> let v' = VarSym.mk x v.VarSym.ty in VarSym.M.add v v' s)
      VarSym.M.empty vneeded vnames
  in
  let get_dir c1 c2 = if dir = LeftToRight then c1 else c2 in
  let pref = get_dir assm.ad_prefix1 assm.ad_prefix2 in
  let pref_len = L.length pref in
  let pref_ju = L.take pref_len se.se_gdef in
  if L.length pref_ju <> pref_len then tacerror "%s: bad prefix" rn;
  (* extend renaming with mappings for random samplings in prefix *)
  let ren =
    List.fold_left2
      (fun ren i1 i2 ->
        match i1, i2 with
        | GSamp(x1,_), GSamp(x2,_) when Type.equal_ty x1.VarSym.ty x2.VarSym.ty ->
          VarSym.M.add x1 x2 ren
        | _ -> tacerror "%s: can not infer renaming" rn)
      ren pref pref_ju
  in
  (* extend renaming with mappings for variables binding return values *)
  let ren =
    List.fold_left2
      (fun ren  (_,j) ad_ac ->
        let vres = ad_ac.ad_ac_lv in
        let nvres = L.length vres in
        let vres_ju =
          L.take nvres (L.drop (j + 1 - nvres) se.se_gdef)
          |> L.map (function GLet (x,_) -> x | c -> 
             Format.eprintf "error on %a@." (Game.pp_gcmd ~nonum:false) c;
             assert false)
        in
        if L.length vres <> L.length vres_ju then
          tacerror "%s: return type does not match" rn;
        L.fold_left2
          (fun rn vs vs_ju -> VarSym.M.add vs vs_ju rn)
          ren vres vres_ju)
      ren rngs assm.ad_acalls
  in
  let rngs = 
    List.map (fun (r_start, r_end) -> {r_start; r_end; r_orcl = []}) rngs in
  let conv_common_prefix ju =
    let se = ju.ju_se in
    let a_rn = inst_dec ren assm in
    let pref = get_dir a_rn.ad_prefix1 a_rn.ad_prefix2 in
    let assm_terms =
      L.map2 (fun ad_ac rng -> 
          let e1,e2 = ad_ac.ad_ac_args in
          let i = rng.r_start in
          (i,get_dir e1 e2)) a_rn.ad_acalls rngs
    in
    let grest =
      L.mapi
        (fun i c ->
          match c with
          | GLet(v,e') ->
            let e = try L.assoc (i + pref_len) assm_terms with Not_found -> e' in
            GLet(v,e)
          | _ -> c)
        (L.drop pref_len se.se_gdef)
    in
    (   T.t_ensure_progress (T.t_conv true { se with se_gdef=pref@grest })
     @> T.t_assm_dec dir ren rngs assm) ju
  in
  (T.t_assm_dec dir ren rngs assm @|| conv_common_prefix) ju

(** Compute substitution and perform let abstraction. *)
let t_assm_dec_aux ts assm dir subst assm_samps vnames ju =
  guard (L.length assm.ad_acalls = 1)  >>= fun _ ->
  let (arg_e) = match assm.ad_acalls with
    | [ {ad_ac_args = (ae_left, ae_right)} ] ->
      if dir=LeftToRight then ae_left else ae_right
    | _ -> assert false
  in
  let se = ju.ju_se in
  let gdef_samps = L.take (L.length assm_samps) (samplings se.se_gdef) in

  (* subst renames assm into judgment *)
  guard (list_eq_for_all2
           (fun (_,(_,(t1,_))) (_,(_,(t2,_))) -> equal_ty t1 t2)
           assm_samps gdef_samps) >>= fun _ ->
  let ren =
    L.fold_left2
      (fun s (_,(vs1,_)) (_,(vs2,_)) -> VarSym.M.add vs1 vs2 s)
      subst
      assm_samps
      gdef_samps
  in
  log_i (lazy (fsprintf "ren %a" pp_ren ren));

  let arg_e = Game.subst_v_expr (fun vs -> VarSym.M.find vs ren) arg_e in
  let arg_v = VarSym.mk (CR.mk_name ~name:"arg" ju.ju_se) arg_e.e_ty in
  let pref_len = L.length assm_samps in
  if is_Quant ju.ju_se.se_ev then
    tacerror "t_assm_dec: no quantifier allowed";
  let ev = ju.ju_se.se_ev in
  let ev_v =
    VarSym.mk (CR.mk_name ~name:"re" ju.ju_se) ev.e_ty in
  let max = L.length ju.ju_se.se_gdef in
  try
    ((*  t_print "after swapping, before unknown" *)
     (* @> t_print "after unknown" *)
      t_let_abstract max ev_v ev None false
      @> t_abstract_deduce ~keep_going:false ts (L.length assm_samps) arg_v arg_e None
      @> t_print log_i "after abstract* "
      @> (fun ju ->
            let rngs = [pref_len, L.length ju.ju_se.se_gdef - 1] in
            t_assm_dec_exact ts (Some assm.ad_name) (Some dir) (Some rngs) (Some vnames) ju))
      ju
  with
    Invalid_rule s -> log_i (lazy s); mempty

(** We known which samplings in the assumption are equivalent, so we
    extract the corresponding samplings in the judgment and make sure
    that equivalent samplings are order *)
let ordered_eqclass samp_assm match_samps eq_class =
  let eq_class_pos =
    samp_assm
    |> L.mapi (fun i (_,(vs,_)) -> if L.mem vs eq_class then Some i else None)
    |> cat_Some
  in
  let match_samp_pos =
    L.map (fun i -> fst (L.nth match_samps i)) eq_class_pos
  in
  L.sort compare match_samp_pos =  match_samp_pos

let match_samps symvars assm_samps_typed gdef_samps_typed =
  let rec go acc asts gsts =
    match asts,gsts with
    | [], [] ->
      ret acc
    | (t,asamps)::asts, (t',gsamps)::gsts ->
      assert (equal_ty t t');
      pick_set_exact (L.length asamps) (mconcat gsamps) >>= fun match_samps ->
      permutations match_samps >>= fun match_samps ->
      let ordered eq_class = ordered_eqclass asamps match_samps eq_class in
      guard (L.for_all ordered symvars) >>= fun _ ->
      let old_new_pos =
        L.map (fun (sg,ss) -> (fst sg, fst ss)) (L.combine match_samps asamps)
      in
      go (acc@old_new_pos) asts gsts
    | _ ->
      assert false
  in
  let matches =
    Nondet.run (-1) (go [] assm_samps_typed gdef_samps_typed)
  in
  let m1, m2 =
    L.partition (fun old_new_pos -> L.for_all (fun (op,np) -> op = np) old_new_pos) matches
  in
  Nondet.mconcat (m1 @ m2)


(** Fuzzy matching with given assumption, compute sequence of swap
    applications that make assumption applicable. Compute let abstraction
    of argument in next step. *)
let t_assm_dec_auto ts assm dir subst ju vnames =
  let se = ju.ju_se in
  log_t (lazy "###############################");
  log_t (lazy (fsprintf "t_assm_dec_auto dir=%s ad=%s" (string_of_dir dir) assm.ad_name));

  (* extract samplings and lets from assumption and judgment *)
  let assm_cmds  = if dir=LeftToRight then assm.ad_prefix1 else assm.ad_prefix2 in
  let assm_samps = samplings assm_cmds in
  let assm_lets  = lets assm_cmds in
  let gdef_samps = samplings se.se_gdef in
  log_t (lazy (fsprintf "@[assm samps:@\n%a@]" (pp_list "@\n" pp_samp) assm_samps));
  log_t (lazy (fsprintf "@[assm lets:@\n%a@]" (pp_list "@\n" pp_let)  assm_lets));
  log_t (lazy (fsprintf "@[gdef samplings:@\n%a@]" (pp_list "@\n" pp_samp) gdef_samps));

  (* compute matchings between samplings in assumption and judgment (match up types) *)
  let ty_of_samp (_,(_,(t,_))) = t in
  let assm_samp_types = L.sort_uniq compare_ty (L.map ty_of_samp assm_samps) in
  let assm_samps_typed =
    L.map
      (fun ty -> (ty, L.filter (fun s -> equal_ty (ty_of_samp s) ty) assm_samps))
      assm_samp_types
  in
  let gdef_samps_typed =
    L.map
      (fun ty -> (ty, L.filter (fun s -> equal_ty (ty_of_samp s) ty) gdef_samps))
      assm_samp_types
  in
  match_samps assm.ad_symvars assm_samps_typed gdef_samps_typed >>= fun old_new_pos ->
  (* FIXME: for now, we assume variables are already correctly ordered *)

  log_t (lazy (fsprintf "@[match samps:@\n[%a]@]"
                 (pp_list ", " (pp_pair pp_int pp_int)) old_new_pos));
  let moves =
       parallel_moves old_new_pos
    |> L.filter_map (fun (old_pos,delta) ->
                       if delta = 0 then None else Some (T.core_tactic (CR.ct_move old_pos delta)))
  in
  (t_seq_fold moves @> t_assm_dec_aux ts assm dir subst assm_samps vnames) ju

(** Supports placeholders for which all possible values are tried *)
let t_assm_dec_non_exact
    ?i_assms:(iassms=Sstring.empty) ts massm_name mdir _mrngs mvnames ju =
  let se = ju.ju_se in
  (* use assumption with given name or try all decisional assumptions *)
  (match massm_name with
   | Some aname ->
     begin try ret (Mstring.find aname ts.ts_assms_dec)
     with Not_found -> tacerror "error no assumption %s" aname
     end
   | None ->
     mconcat (Mstring.fold (fun _aname assm acc -> assm::acc) ts.ts_assms_dec [])
  ) >>= fun assm ->
  guard (not (Sstring.mem assm.ad_name iassms)) >>= fun _ ->
  (* use given direction or try both directions *)
  (O.map_default ret (mconcat [LeftToRight; RightToLeft]) mdir)
  >>= fun dir ->
  (* generate substitution for all required new variable names
     generating new variable names if not enough are provided *)
  let needed = needed_vars_dec dir assm in
  let given_vnames = O.default [] mvnames in
  let required = max 0 (L.length needed - L.length given_vnames) in
  (* FIXME: prevent variable clashes here *)
  let generated_vnames =
    L.map (fun _ -> CR.mk_name se) (list_from_to 0 required)
  in
  let ren =
    L.fold_left2
      (fun sigma v x -> VarSym.M.add v (VarSym.mk x v.VarSym.ty) sigma)
      VarSym.M.empty
      needed
      (given_vnames@generated_vnames)
  in
  (t_unfold_only @> (fun ju -> t_assm_dec_auto ts assm dir ren ju (given_vnames@generated_vnames))) ju

let t_assm_dec
  ?i_assms:(iassms=Sstring.empty) ts exact massm_name mdir mrngs mvnames ju =
  if exact then
    t_assm_dec_exact ts massm_name mdir mrngs mvnames ju
  else
    t_assm_dec_non_exact ~i_assms:iassms ts massm_name mdir mrngs mvnames ju

(* ** Computational assumptions
 * ----------------------------------------------------------------------- *)

let e_eqs e =
  let comm_eq e =
    guard (is_Eq e) >>= fun _ ->
    ret e
  in
  if is_Land e then (
    mconcat (destr_Land e) >>= fun cj ->
    comm_eq cj
  ) else (
    comm_eq e
  )

let match_expr (vars : VarSym.t list) pat e =
  let vars_set = VarSym.S.of_list vars in
  let sigma = VarSym.H.create 17 in
  let ensure c =
    if not c then raise Not_found
  in
  let inst v (e : expr) =
    try
      let e' = VarSym.H.find sigma v in
      ensure (equal_expr e e')
    with
      Not_found -> VarSym.H.add sigma v e
  in
  let rec pmatchl es1 es2 =
    ensure (L.length es1 = L.length es2);
    L.iter2 pmatch es1 es2
  and pmatch p e =
    match p.e_node, e.e_node with
    | V(vs1),_
      when VarSym.S.mem vs1 vars_set  -> inst vs1 e
    | V(vs1),        V(vs2)         -> ensure (VarSym.equal vs1 vs2)
    (* | H(hs1,e1),     H(hs2,e2)      -> ensure (Fsym.equal hs1 hs2); pmatch e1 e2 *)
    | Tuple(es1),    Tuple(es2)     -> pmatchl es1 es2
    | Proj(i1,e1),   Proj(i2,e2)    -> ensure (i1 = i2); pmatch e1 e2
    | Cnst(c1),      Cnst(c2)       -> ensure (c1 = c2)
    | App(op1,es1),  App(op2,es2)   -> ensure (op1 = op2); pmatchl es1 es2
    | Nary(nop1,es1),Nary(nop2,es2) -> ensure (nop1 = nop2); pmatchl es1 es2
    | _                             -> raise Not_found
  in
  try
    pmatch pat e;
    let bvars = VarSym.H.fold (fun k _ acc -> VarSym.S.add k acc) sigma VarSym.S.empty in
    if VarSym.S.equal vars_set bvars then
      ret (L.map (fun v -> (v,VarSym.H.find sigma v)) vars)
    else
      mempty
  with
    Not_found ->
      mempty

let assm_acall assm =
  match assm.ac_acalls with
  | [(_,vs,e)] -> ret (vs,e)
  | _ -> mempty

let match_exprs_assm ju assm =
  let jev = ju.ju_se.se_ev in
  let aev = assm.ac_event in
  assm_acall assm >>= fun (avs,_) ->
  let eavs = L.map mk_V avs in
  (* we first collect all equalities in aev and jev *)
  e_eqs aev >>= fun aeq ->
  guard (not (Se.is_empty (Se.inter (Se.of_list eavs) (e_vars aeq)))) >>= fun _ ->
  e_eqs jev >>= fun jeq ->
  ret (aeq,jeq)

let tries = ref 0

let conj_type e =
  if is_Eq e then (
    let (a,_) = destr_Eq e in
    Some (true,a.e_ty)
  ) else if is_Not e then (
      let e = destr_Not e in
      if is_Eq e then (
        let (a,_) = destr_Eq e in
        Some (false,a.e_ty)
      ) else (
        None
      )
  ) else (
    None
  )

let t_assm_comp_match ?icases:(icases=Se.empty) ts before_t_assm assm subst mev_e ju =
  let assm = inst_comp subst assm in
  assm_acall assm >>= fun (avars,aarg) ->
  (match mev_e with
  | Some e -> ret e
  | None   ->
    match_exprs_assm ju assm >>= fun (pat,e) ->
    log_t (lazy (fsprintf "assm_comp_match: %a %a" pp_expr e pp_expr pat));
    match_expr avars pat e
  ) >>= fun ev_mapping ->
  let sassm = Assumption.inst_comp subst assm in
  log_t (lazy (fsprintf "matching %a" (pp_list "," (pp_pair VarSym.pp pp_expr)) ev_mapping));
  let ev_me = me_of_list (L.map (fun (v,e) -> (mk_V v,e)) ev_mapping) in
  let sassm_ev = e_subst ev_me sassm.ac_event in
  let assm_se =
    { se_gdef = sassm.ac_prefix;
      se_ev = sassm_ev  }
  in
  let assm_se = norm_se ~norm:(fun x -> x) assm_se in
  let conjs = destr_Land assm_se.se_ev in
  let ineq = L.hd (L.filter is_Not conjs) in
  let nineq = NormUtils.norm_expr_nice (mk_Not ineq) in
  guard (not (Se.mem nineq icases)) >>= fun _ ->
  let assm_len = L.length assm.ac_prefix in
  let ev_mapping' =
    L.map
      (fun (v,e) -> (VarSym.mk ((Id.name v.VarSym.id)^"__") v.VarSym.ty, e))
      ev_mapping
  in
  let subst =
    L.fold_left2
      (fun s (vs1,_) (vs2,_) -> VarSym.M.add vs1 vs2 s)
      subst
      ev_mapping
      ev_mapping'
  in
  (* let get_bind bindings = match bindings with [(vs,_)] -> vs | _ -> tacerror "fail" in *)
  let argv = VarSym.mk "arg" aarg.e_ty in
  let assm_tac_only =
       t_print log_i ("%%% step 1")
   @> (fun ju ->
          let last = Some (L.length ju.ju_se.se_gdef - 1) in
          t_abstract_deduce ~keep_going:false ts assm_len argv aarg last ju)
    @> t_print log_i ("%%% step 2")
    @> (fun ju ->
          let ev = ju.ju_se.se_ev in
          if is_Exists ev then (
            let ((vs,_os),ev) = destr_Exists ev in
            let asym = AdvSym.mk "CC" argv.VarSym.ty (mk_Prod (L.map (fun v -> v.VarSym.ty) vs))  in
            let v = VarSym.mk "f_arg" aarg.e_ty in
            T.core_tactic (CR.ct_find ([v],e_replace aarg (mk_V v) ev) aarg asym vs) ju
          ) else (
            T.t_id ju
          )
        )
    @> t_print log_i ("%%% step 3")
    @> (t_seq_fold
          (L.map
             (fun (v,e) ju -> t_let_abstract (L.length ju.ju_se.se_gdef) v e None false ju)
                ev_mapping'))
    @> t_print log_i ("%%% step 4")
    @> (fun ju ->
          let argv = VarSym.mk "arg__" aarg.e_ty in
          let last = Some (L.length ju.ju_se.se_gdef - 1) in
          t_abstract_deduce ~keep_going:false ts assm_len argv aarg last ju)
    @> t_print log_i ("%%% step 5")
    @> (fun ju -> T.t_assm_comp assm [assm_len,L.length ju.ju_se.se_gdef - 1] subst ju)
  in
  let assm_tac =
    (    T.core_tactic (CR.ct_case_ev ~flip:true nineq)
     @>> [ before_t_assm
           @> assm_tac_only
         ; T.t_id])
  in
  let sconjs = destr_Land sassm_ev in
  let sineq = L.hd (L.filter is_Not sconjs) in
  let snineq = NormUtils.abbrev_ggen sineq in
  if is_Land ju.ju_se.se_ev &&
     L.exists (fun e ->
       equal_expr (NormUtils.abbrev_ggen e) snineq) (destr_Land ju.ju_se.se_ev)
  then (
    log_i (lazy "return None");
    log_i (lazy (fsprintf "%a" pp_ju ju));
    log_i (lazy (fsprintf "%a" (pp_list "," (pp_pair VarSym.pp VarSym.pp)) (VarSym.M.bindings subst)));
    assm_tac_only ju >>= fun ps -> ret (None,ps)
  ) else (
    log_i (lazy "return Some");
    T.t_id ju >>= fun ps -> ret (Some assm_tac,ps)
  )

let t_assm_comp_aux ?icases:(icases=Se.empty) ts before_t_assm assm mev_e ju =
  let se = ju.ju_se in
  let assm_cmds = assm.ac_prefix in
  let samp_assm = samplings assm_cmds in
  let samp_gdef = samplings se.se_gdef |> L.take (L.length samp_assm) in
  guard
    (list_eq_for_all2 (fun (_,(_,(t1,_))) (_,(_,(t2,_))) -> equal_ty t1 t2)
       samp_assm samp_gdef)
  >>= fun _ ->
  let subst =
    L.fold_left2
      (fun s (_,(vs1,_)) (_,(vs2,_)) -> VarSym.M.add vs1 vs2 s)
      VarSym.M.empty
      samp_assm
      samp_gdef
  in
  log_t (lazy (fsprintf "subst %a"
    (pp_list "," (pp_pair VarSym.pp VarSym.pp)) (VarSym.M.bindings subst)));
  incr tries;
  try
    T.t_id ju >>= fun ps ->
    T.rapply_all
      (t_assm_comp_match ~icases ts (before_t_assm) assm subst mev_e) ps
  with
    Invalid_rule s -> log_d (lazy s); mempty

let t_assm_comp_auto ?icases:(icases=Se.empty) ts assm _mrngs ju =
  let se = ju.ju_se in
  tries := 0;
  log_t (lazy (fsprintf "###############################"));
  log_t (lazy (fsprintf "t_assm_comp assm=%s" assm.ac_name));
  let mev_e = None in
  let assm_cmds = assm.ac_prefix in
  let samp_assm = samplings assm_cmds in
  let lets_assm = lets assm_cmds in
  let samp_gdef = samplings se.se_gdef in
  log_t (lazy (fsprintf "@[assm:@\n%a@]" (pp_list "@\n" pp_samp) samp_assm));
  log_t (lazy (fsprintf "@[assm:@\n%a@]" (pp_list "@\n" pp_let)  lets_assm));
  log_t (lazy (fsprintf "@[gdef:@\n%a@\n%!@]" (pp_list "@\n" pp_samp) samp_gdef));
  let assm_samp_num = L.length samp_assm in
  (* FIXME: do not assume samplings in assumption occur first and are from Fq *)
  let samp_gdef = L.filter (fun (_,(_,(ty,_))) -> equal_ty ty mk_Fq) samp_gdef in
  pick_set_exact assm_samp_num (mconcat samp_gdef) >>= fun match_samps ->
  permutations match_samps >>= fun match_samps ->
  (* try all type-preserving bijections between random samplings in
     the assumption and the considered game *)
  let ordered eq_class = ordered_eqclass samp_assm match_samps eq_class in
  guard (L.for_all ordered assm.ac_symvars) >>= fun _ ->

  let old_new_pos = L.mapi (fun i x -> (fst x,i)) match_samps in
  let moves =
       parallel_moves old_new_pos
    |> L.filter_map
        (fun (old_p,delta) ->
          if delta = 0 then None else Some (T.t_move old_p delta))
  in
  (* let priv_exprs = L.map (fun (_,(v,_)) -> mk_V v) match_samps in *)
  let excepts =
    L.filter_map
      (fun (i,(_,(_,es))) -> if es<>[] then Some (T.t_except i []) else None)
      match_samps
  in
  (* FIXME: use case_ev and rfalse to handle case with missing events *)
  assert (not (is_Quant assm.ac_event));
  (*
  if (se.se_ev.ev_binding <> []) then
    tacerror " t_assm_comp_auto: quantifier not allowed";
  *)
  let aev = assm.ac_event in
  let ev = se.se_ev in
  let remove_events =
    if not (is_Land aev && is_Land ev) then ( [] )
    else (
      let ctypes = L.map conj_type (destr_Land aev) in
      destr_Land ev
      |> L.mapi (fun i e -> (i,conj_type e))
      |> L.filter (fun (_,ct) -> not (L.mem ct ctypes))
      |> L.map fst
    )
  in
  let before_t_assm =
    T.t_remove_ev remove_events
    (* @> t_norm_unknown ts priv_exprs *)
    @> t_seq_fold excepts
    @> t_seq_fold moves
  in
  guard (not (is_Land aev && not (is_Land ev))) >>= fun _ ->
  before_t_assm ju >>= fun ps ->
  T.rapply_all
    (t_assm_comp_aux ~icases ts before_t_assm assm mev_e) ps >>= fun (ot,ps) ->
  match ot with
  | Some t -> t ju
  | None   -> ret ps

let t_assm_comp_no_exact ?icases:(icases=Se.empty) ts maname mrngs ju =
  (match maname with
  | Some aname ->
    begin try ret (Mstring.find aname ts.ts_assms_comp)
    with Not_found -> tacerror "error no assumption %s" aname
    end
  | None ->
    mconcat (Mstring.fold (fun _aname assm acc -> assm::acc) ts.ts_assms_comp [])
  ) >>= fun assm ->
  (* try all assumptions *)
  (t_norm @> t_assm_comp_auto ~icases ts assm mrngs) ju

let t_assm_comp_exact ts maname mrngs ju =
  let se = ju.ju_se in
  let aname =
     match maname with
     | Some an -> an
     | None ->
      tacerror "assumption_computational: assumption name required for exact"
  in
  let rngs =
    match mrngs with
    | Some rngs -> rngs
    | None ->
      tacerror "assumption_computational: adversary call ranges required for exact"
  in
  let assm =
    try Mstring.find aname ts.ts_assms_comp
    with Not_found -> tacerror "error no assumption %s" aname
  in
  let c = assm.ac_prefix in
  let jc = L.take (L.length c) se.se_gdef in

  (* initial renaming derived from samplings *)
  let ren =
    L.fold_left2 (fun s i1 i2 ->
      match i1, i2 with
      | GSamp(x1,_), GSamp(x2,_)
        when Type.equal_ty x1.VarSym.ty x2.VarSym.ty ->
        VarSym.M.add x1 x2 s
      | _ ->
        tacerror "assumption_computational: cannot infer substitution")
      VarSym.M.empty c jc
  in

  (* extend renaming with mappings for variables binding return values *)
  let ren =
    List.fold_left2
      (fun rn  (_,j) (_asym,vres,_) ->
        let nvres = L.length vres in
        let vres_ju =
          L.take nvres (L.drop (j + 1 - nvres) se.se_gdef)
          |> L.map (function GLet (x,_) -> x | _ -> assert false)
        in
        L.fold_left2 (fun rn vs vs_ju -> VarSym.M.add vs vs_ju rn) rn vres vres_ju)
      ren rngs assm.ac_acalls
  in

  let conv_event ju =
    let se = ju.ju_se in
    let a_rn = inst_comp ren assm in
    (   T.t_conv true { se with se_ev=a_rn.ac_event }
     @> T.t_assm_comp assm rngs ren) ju
  in

  log_t (lazy (fsprintf "t_assm_comp_exact ren: %a" pp_ren ren));
  (T.t_assm_comp assm rngs ren @|| conv_event) ju

let t_assm_comp ?icases:(icases=Se.empty) ts exact maname mrngs ju =
  if exact then
    t_assm_comp_exact ts maname mrngs ju
  else
    t_assm_comp_no_exact ~icases ts maname mrngs ju
