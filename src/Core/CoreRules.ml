(* * Core rules of the logic. *)

(* ** Imports and abbreviations *)
open Abbrevs
open Util
open Syms
open Type
open Expr
open ExprUtils
open Game
open Wf
open Assumption
open CoreTypes

let mk_log level = mk_logger "Core.CoreRules" level "CoreRules.ml"
let _log_t = mk_log Bolt.Level.TRACE
let _log_d = mk_log Bolt.Level.DEBUG
let log_i = mk_log Bolt.Level.INFO

(* ** Types for proofs and tactics
 * ----------------------------------------------------------------------- *)

(** Proof tree. *)
type 'info iproof_tree = {
  pt_children : ('info iproof_tree) list;
  pt_rule     : rule_name;
  pt_ju       : judgment;
  pt_info     : 'info
}

type proof_tree = unit iproof_tree

(** Replace subproofs with (possibly) different proofs of the same facts. *)
let pt_replace_children pt pts info =
  let equal_fact pt1 pt2 = equal_judgment pt1.pt_ju pt2.pt_ju in
  assert (Util.list_eq_for_all2 equal_fact pt.pt_children pts);
  { pt with pt_children = pts; pt_info = info }

(** A [goal] is just a [judgment] (for now). *)
type goal = judgment

(** A validation is a proof tree with holes.
    It returns a proof tree given proof trees for the holes. *)
type validation = proof_tree list -> proof_tree

(** A proof state consists of the remaining goals and the validation. *)
type proof_state = {
  subgoals   : goal list;
  validation : validation
}

(** A tactic takes a goal and returns a proof state. *)
type core_tactic = goal -> (proof_state,string lazy_t) BatResult.t

(* ** General purpose functions
 * ----------------------------------------------------------------------- *)

(** Create a variable name that is fresh in the given security experiment *)
let mk_name ?(name="r__") se =
  let vars = vars_all_gdef se.se_gdef in
  let name_of_int i = name^(string_of_int i) in
  let names =
    VarSym.S.fold
      (fun vs se -> Sstring.add (Id.name vs.VarSym.id) se) vars Sstring.empty
  in
  if Sstring.mem name names then
    let rec go n =
      let name = name_of_int n in
      if Sstring.mem name  names then go (n+1) else name
    in
    go 1
  else name

(** Get proof from proof state with no open goals. *)
let get_proof ps =
  if ps.subgoals <> [] then tacerror "get_proof: open subgoals remaining";
  ps.validation []

(** Prove goal [g] by rule [ru] which yields a rule name and subgoals. *)
let prove_by ru g =
  let open BatResult in
  try
    let (rn,subgoals) = ru g in
    Monad.return
      { subgoals = subgoals;
        validation = fun pts ->
          assert (L.length pts = L.length subgoals);
          assert (L.for_all2 (fun pt g -> equal_judgment pt.pt_ju g) pts subgoals);
          { pt_ju       = g;
            pt_rule     = rn;
            pt_children = pts;
            pt_info     = ();
          }
      }
  with
  | Invalid_rule s ->
    Bad (lazy s)
  | Wf.Wf_div_zero es ->
    Bad (lazy (fsprintf "Failed divzero check: %a" (pp_list "," pp_expr) es))
  | Wf.Wf_var_undef(vs,e,def_vars) ->
    Bad (lazy (fsprintf "Variable undefined: %a in %a not in %a"
                 VarSym.pp vs pp_expr e (pp_list "," VarSym.pp) (VarSym.S.elements def_vars)))

(** Given a list of proof states and a validation, create a new proof state
    with the combined subgoals and a combined validation. *)
let merge_proof_states pss validation =
  let rec validation' accu pss pts =
    match pss with
    | [] ->
      assert (pts = []);
      validation (L.rev accu)
    | ps::pss ->
      let hd, tl = Util.cut_n (L.length ps.subgoals) pts in
      validation' (ps.validation (L.rev hd) :: accu) pss tl
  in
  { subgoals   = conc_map (fun ps -> ps.subgoals) pss;
    validation = validation' [] pss }

(* ** Core rules: Helper functions
 * ----------------------------------------------------------------------- *)

let ensure_gdef_eq rn a b =
  if not (equal_gdef a b) then
    tacerror "@[<v>%s: games not equal,@ @[<v>%a@]@ \n \n @[<v>%a@]@]"
      rn (pp_gdef ~nonum:false) a (pp_gdef ~nonum:false) b

let ensure_event_eq rn e1 e2 =
  if not (equal_expr e1 e2) then
    tacerror "%s: events not equal, @\n@[<hov 2>  %a vs @ %a@]"
      rn pp_expr e1 pp_expr e2

let ensure_ren_inj rn ren =
  if not (ren_injective ren) then
    tacerror "%s: renaming not bijective" rn

let ensure_not_use rn used_vars forbidden_vars gdef =
  if not (se_disjoint used_vars forbidden_vars) then
    tacerror "%s: judgment uses private variables: %a in @\n@[<hv 2>%a@]" rn
      (pp_list "," pp_expr) (Se.elements (Se.inter used_vars forbidden_vars))
      (pp_gdef ~nonum:false) gdef

let ensure_ppt rn gdef =
  if not (is_ppt_gcmds gdef) then
    tacerror "%s: %a is not ppt" rn (pp_gdef ~nonum:false) gdef

let ensure_not_use_le rn used_vars forbidden_vars ldef lres =
  if not (se_disjoint used_vars forbidden_vars) then
    tacerror "%s: judgment uses private variables: %a in @\n@[<hv 2>%a@]" rn
      (pp_list "," pp_expr) (Se.elements (Se.inter used_vars forbidden_vars))
      (pp_lcomp ~nonum:false ~qual:Unqual) (lres, ldef)

let ensure_ppt_le rn ldef lres =
  if not (is_ppt_lcmds ldef && is_ppt lres) then
    tacerror "%s: %a is not ppt" rn (pp_lcomp ~nonum:false ~qual:Unqual) 
             (lres,ldef)

let ensure_not_use_l rn used_vars forbidden_vars ldef =
  if not (se_disjoint used_vars forbidden_vars) then
    tacerror "%s: judgment uses private variables: %a in @\n@[<v>%a@]" rn
      (pp_list "," pp_expr) (Se.elements (Se.inter used_vars forbidden_vars))
      (pp_list "@ " (pp_lcmd ~qual:Unqual)) ldef

let ensure_ppt_l rn ldef  =
  if not (is_ppt_lcmds ldef) then
    tacerror "%s: @[<v>%a@] is not ppt" rn 
       (pp_list "@ " (pp_lcmd ~qual:Unqual)) ldef

let ensure_pr_Adv rn ju =
  if ju.ju_pr <> Pr_Adv then
    tacerror "%s: Adv judgment expected" rn

let ensure_pr_Succ_or_Adv rn ju =
  if ju.ju_pr <> Pr_Succ && ju.ju_pr <> Pr_Adv then
    tacerror "%s: Succ or Adv judgment expected" rn

(* ** Core rules: Lossless bridging rules
 * ----------------------------------------------------------------------- *)

(* *** Conversion
 * ----------------------------------------------------------------------- *)

let rename_if_required rn se1 se2 =
  try
    let ren = unif_se se1 se2 in
    log_i (lazy "found unifier");
    if VarSym.M.is_empty ren then se1
    else (
     ensure_ren_inj rn ren;
     let se1 = subst_v_se (fun vs -> try VarSym.M.find vs ren with Not_found -> vs) se1 in
     log_i (lazy "applied unifier");
     se1
    )
  with
    Not_found -> tacerror "no unifier found"

let check_convertible rn do_norm_terms se1 se2 =
  (* check well-formedness without DivZero and then unfold *)
  wf_se NoCheckDivZero se1;
  wf_se NoCheckDivZero se2;
  let se     = norm_se ~norm:id se1 in
  let new_se = norm_se ~norm:id se2  in
  (* perform renaming if required *)
  let se = rename_if_required rn se new_se in
  (* check DivZero for unfolded+renamed and normalize (if requested) *)
  if not do_norm_terms then (
    ensure_gdef_eq  rn se.se_gdef new_se.se_gdef;
    ensure_event_eq rn se.se_ev   new_se.se_ev;
  ) else (
      wf_se CheckDivZero se;
      wf_se CheckDivZero new_se;
      let norm_rw = map_se_exp Norm.norm_expr_strong in
      let se, new_se = (norm_rw se, norm_rw new_se) in
      ensure_gdef_eq  rn se.se_gdef new_se.se_gdef;
      ensure_event_eq rn se.se_ev   new_se.se_ev
  )

let r_conv do_norm_terms new_se0 ju =
  check_convertible "conv" do_norm_terms ju.ju_se new_se0;
  Rconv, [{ ju with ju_se = new_se0 }]

let ct_conv do_norm_terms new_se = prove_by (r_conv do_norm_terms new_se)

let ensure_ty_unfold wh ty = if wh then
    match ty.ty_node with
    | Mat (a, MDPlus(b,c)) -> ()
    | List (l, t1) ->
            begin match t1.ty_node with
            | Mat (a, MDPlus (b,c)) -> ()
            | _ -> tacerror "bad mat"
            end
    | _ -> tacerror "bad mat: got %a" pp_ty ty
else
    match ty.ty_node with
    | Mat (MDPlus(a,b),c) -> ()
    | List (l, t1) ->
            begin match t1.ty_node with
            | Mat (MDPlus(a,b), c) -> ()
            | _ -> tacerror "bad mat"
            end
    | _ -> tacerror "bad mat: got %a" pp_ty ty

let split_ty_unfold wh ty = if wh then
    match ty.ty_node with
    | Mat (a, MDPlus(b,c)) -> (mk_Mat a b, mk_Mat a c)
    | List (l, t1) ->
            begin match t1.ty_node with
            | Mat (a, MDPlus (b,c)) -> (mk_List l (mk_Mat a b), mk_List l (mk_Mat a c))
            | _ -> tacerror "bad mat"
            end
    | _ -> assert false
else
    match ty.ty_node with
    | Mat (MDPlus(a,b),c) -> (mk_Mat a c, mk_Mat b c)
    | List (l, t1) ->
            begin match t1.ty_node with
            | Mat (MDPlus(a,b), c) -> (mk_List l (mk_Mat a c), mk_List l (mk_Mat b c))
            | _ -> tacerror "bad mat"
            end
    | _ -> assert false

let ensure_ty_fold wh ty1 ty2 = if wh then
    match ty1.ty_node, ty2.ty_node with
    | Mat(a, b), Mat(c,d) when mdim_equal a c -> ()
    | List(l, t1), List(l',t2) when mdim_equal l l' ->
            begin match t1.ty_node, t2.ty_node with
            | Mat (a,b), Mat(c,d) when mdim_equal a c -> ()
            | _ -> tacerror "bad mats"
            end
    | _,_ -> tacerror "bad mats: %a, %a" pp_ty ty1 pp_ty ty2
else
    match ty1.ty_node, ty2.ty_node with
    | Mat(a,b), Mat(c,d) when mdim_equal b d -> ()
    | List(l, t1), List(l', t2) when mdim_equal l l' ->
            begin match t1.ty_node, t2.ty_node with
            | Mat (a,b), Mat (c,d) when mdim_equal b d -> ()
            | _ -> tacerror "bad mats"
            end
    | _,_ -> tacerror "bad mats: %a, %a" pp_ty ty1 pp_ty ty2

let ty_fold wh ty1 ty2 = if wh then
    match ty1.ty_node, ty2.ty_node with
    | Mat(a,b), Mat(_c,d) -> mk_Mat a (MDPlus(b,d))
    | List(l, t1), List(_, t2) ->
            begin match t1.ty_node, t2.ty_node with
            | Mat (a,b), Mat(c,d) -> mk_List l (mk_Mat a (MDPlus (b,d)))
            | _ -> assert false
            end
    | _,_ -> assert false
else
    match ty1.ty_node, ty2.ty_node with
    | Mat(a,_), Mat(c,d) -> mk_Mat (MDPlus (a,c)) d
    | List(l, t1), List(_, t2) ->
            begin match t1.ty_node, t2.ty_node with
            | Mat (a,_), Mat(c,d) -> mk_List l (mk_Mat (MDPlus (a,c)) d)
            | _ -> assert false
            end
    | _,_ -> assert false


let r_matfold (m : string option) wh i j ju  = 
    if i >= j then tacerror "first must be earlier";
    let se = ju.ju_se in
    match (get_se_ctxt se i), (get_se_ctxt se j) with
    | (GSamp(a, (ty1, exc1)), sec1), (GSamp(b, (ty2, exc2)), _) ->
      if exc1 <> [] || exc2 <> [] then tacerror "excepted distribution not
      allowed";
      let _ = ensure_ty_fold wh ty1 ty2 in
      let ab_ty = ty_fold wh ty1 ty2 in
      let sab = 
          VarSym.mk (mk_name 
          ~name:(match m with | Some (n) -> n | None -> "AB") se)
          ab_ty in
      let ab = mk_V sab in
      let subst e = if wh then 
          let e1 = e_replace (mk_V a) (mk_SplitLeft ab) e in
          e_replace (mk_V b) (mk_SplitRight ab) e1
      else
          let e1 = e_replace (mk_V a) (mk_Trans (mk_SplitLeft (mk_Trans
          ab))) e in
          e_replace (mk_V b) (mk_Trans (mk_SplitRight (mk_Trans ab)))
          e1
      in
      let se = set_se_ctxt [ GSamp(sab, (ab.e_ty, [])) ] sec1 in (* set a samp to
      AB samp*)
      let (_, sec) = get_se_ctxt se j in
      let se = set_se_ctxt [] sec in
      let se = map_se_exp subst se in
      Rmatfold(wh,i,j), [ {ju with ju_se = se} ]
    | _,_ -> tacerror "not good samp"


let ct_matfold m wh i j  = prove_by (r_matfold m wh i j)

let r_matunfold (p : (string * string) option) wh i ju  = 
    let se = ju.ju_se in
    match get_se_ctxt se i with
    | GSamp(ab, (ty, exc)), sec ->
      if exc <> [] then tacerror "excepted distribution not allowed";
      let _ = ensure_ty_unfold wh ty in (*if wh then ab is
      Matrix_{z,x+y}; if not wh then ab is Matrix_{x+y,z} *)
      let (a_ty, b_ty) = split_ty_unfold wh ty in
      let (sa_n, sb_n) = 
          (match p with | Some (n1, n2) -> (n1, n2) | None -> ("A", "B")) in
      let sa = VarSym.mk (mk_name ~name:sa_n se) a_ty in
      let sb = VarSym.mk (mk_name ~name:sb_n se) b_ty in
      let a = mk_V sa in
      let b = mk_V sb in
      let subst = if wh then fun e -> e_replace (mk_V ab) (mk_Concat a b) e
                  else fun e -> e_replace (mk_V ab) (mk_Trans (mk_Concat
                  (mk_Trans a) (mk_Trans b))) e in
      let se = set_se_ctxt [ GSamp(sa, (a.e_ty, [])); GSamp(sb, (b.e_ty, [])) ] sec in
      let se = map_se_exp subst se in
      Rmatunfold(wh,i), [ {ju with ju_se = se } ] 
    | _ -> tacerror "not good samp" 
      

let ct_matunfold p wh i = prove_by (r_matunfold p wh i)

(* *** Instruction movement.
 * ----------------------------------------------------------------------- *)

let ensure_disjoint rn read write i c =
  let i = [i] in
  let ir = read i in
  let iw = write i in
  let cr = read c in
  let cw = write c in
  if not (se_disjoint iw cw && se_disjoint ir cw && se_disjoint cr iw) then
    tacerror "%s: can not move" rn

let move i delta ju =
  if delta = 0 then ju
  else (
    let se = ju.ju_se in
    let instr,{sec_left=hd; sec_right=tl; sec_ev=e} = get_se_ctxt se i in
    let c1,c2,c3 =
      if delta < 0 then
        let hhd, thd = cut_n (-delta) hd in
        thd, hhd, tl
      else
        let htl, ttl = cut_n delta tl in
        hd, L.rev htl, ttl
    in
    ensure_disjoint "move" read_gcmds write_gcmds instr c2;
    if is_call instr && has_call c2 then tacerror "move : can not move";
    let c2,c3 =
      if delta > 0 then c2,instr::c3 else instr::c2,c3
    in
    let seoc = {sec_left=c1; sec_right=c3; sec_ev=e} in
    { ju with ju_se = set_se_ctxt c2 seoc }
  )

let r_move i delta ju = Rmove(i, delta), [move i delta ju]

let ct_move i delta = prove_by (r_move i delta)

(* *** Instruction moving for Oracle.
 * ----------------------------------------------------------------------- *)

let move_oracle i delta ju =
  if delta = 0 then ju
  else (
    let se = ju.ju_se in
    let i, seoc = get_se_octxt se i in
    let c1_rev,c2,c3 =
      if delta < 0 then
        let hhd,thd = cut_n (-delta) seoc.seoc_cleft in
        thd,hhd,seoc.seoc_cright
      else
        let htl, ttl = cut_n delta seoc.seoc_cright in
        seoc.seoc_cleft, L.rev htl, ttl
    in
    ensure_disjoint "move_oracle" read_lcmds write_lcmds i c2;
    let c2, c3 =
      if delta > 0 then c2, i::c3 else i::c2, c3
    in
    let seoc = { seoc with seoc_cleft = c1_rev; seoc_cright = c3} in
    { ju with ju_se = set_se_octxt c2 seoc }
  )

let r_move_oracle i delta ju =
  Rmove_orcl(i,delta), [move_oracle i delta ju]

let ct_move_oracle i delta = prove_by (r_move_oracle i delta)

(* *** Random sampling.
 * ----------------------------------------------------------------------- *)

let ensure_bijection ?partial:(partial=false) se c1 c2 rs = (* c1 = inverse, c2 = direct *)
  (* v : t
     c1 : t' -> t
     c2 : t  -> t' *)
  let dty1,cty1 = ctxt_ty c1 in
  let dty2,cty2 = ctxt_ty c2 in
  let t = rs.VarSym.ty in
  let t' = dty1 in
  if not (equal_ty cty1 t) then
    tacerror "rnd: c1 has type %a -> %a while %a -> %a is expected"
      pp_ty dty1 pp_ty cty1 pp_ty t' pp_ty t;
  if not (equal_ty dty2 t && equal_ty cty2 t') then
    tacerror "rnd: c2 has type %a -> %a while %a -> %a is expected"
      pp_ty dty2 pp_ty cty2 pp_ty t pp_ty t';

  let v  = mk_V rs in
  let v' = mk_V (VarSym.mk (mk_name ~name:"v__" se) t') in
  let f1 = (inst_ctxt c2 (inst_ctxt c1 v')) in
  let f2 = (inst_ctxt c1 (inst_ctxt c2 v)) in
  if not (Norm.equalmod_expr (inst_ctxt c2 (inst_ctxt c1 v')) v' &&
            (partial || Norm.equalmod_expr (inst_ctxt c1 (inst_ctxt c2 v)) v)) then
    tacerror "contexts %a and %a are not bijective: w/ %a, %a, %a, %a"
      pp_ctxt c1 pp_ctxt c2 pp_expr f1 pp_expr v' pp_expr f2 pp_expr v


let r_rnd p c1 c2 ju =
  let se = ju.ju_se in
  match get_se_ctxt se p with
  | GSamp(rvs,(_,exc)), sec ->
    if exc <> [] then tacerror "rnd: excepted distribution not allowed";
    let new_ty = (fst c1).VarSym.ty in
    ensure_bijection se c1 c2 rvs;
    (* check second context first such that divZero does not clobber undef *)
    let wfs = wf_gdef NoCheckDivZero (L.rev sec.sec_left) in
    wf_expr CheckDivZero (ensure_varname_fresh wfs (fst c2)) (snd c2);
    wf_expr CheckDivZero (ensure_varname_fresh wfs (fst c1)) (snd c1);
    let rv = mk_V rvs in
    let nrvs =
      if equal_ty rvs.VarSym.ty new_ty then rvs
      else VarSym.mk (mk_name ~name:(Id.name (fst c1).VarSym.id) se) new_ty in
    let nrv = mk_V nrvs in
    let vslet = VarSym.mk (mk_name ~name:"u__" se) rv.e_ty in
    let cmds = [ GSamp(nrvs,(new_ty, [])); GLet(vslet, inst_ctxt c1 nrv) ] in
    let subst e = e_replace rv (mk_V vslet) e in
    let sec = { sec with
                sec_right = map_gdef_exp subst sec.sec_right;
                sec_ev    = subst sec.sec_ev }
    in
    Rrnd(p,nrvs,c1,c2), [ { ju with ju_se = set_se_ctxt cmds sec } ]
  | _ ->
    tacerror "rnd: position given is not a sampling"

let ct_rnd p c1 c2 = prove_by (r_rnd p c1 c2)

(* *** Random sampling in oracle.
 * ----------------------------------------------------------------------- *)

let r_rnd_oracle p c1 c2 ju =
  let se = ju.ju_se in
  match get_se_octxt se p with
  | LSamp(rvs,(_,exc)), seoc ->
    if exc <> [] then tacerror "rnd_oracle: excepted distribution not allowed";
    let new_ty = (fst c1).VarSym.ty in
    ensure_bijection se c1 c2 rvs;
    (* check second context first such that divZero does not clobber undef *)
    let wfs = wf_gdef CheckDivZero (L.rev seoc.seoc_sec.sec_left) in
    let wfs = ensure_varnames_fresh wfs seoc.seoc_oargs in
    let wfs = wf_lcmds CheckDivZero wfs None (L.rev seoc.seoc_cleft) in
    wf_expr CheckDivZero (ensure_varname_fresh wfs (fst c2)) (snd c2);
    wf_expr CheckDivZero (ensure_varname_fresh wfs (fst c1)) (snd c1);
    let rv = mk_V rvs in
    let qual = Qual seoc.seoc_osym in
    let nrvs =
      if equal_ty rvs.VarSym.ty new_ty then rvs
      else VarSym.mk_qual (mk_name ~name:(Id.name (fst c1).VarSym.id) se) qual new_ty
    in
    let nrv = mk_V nrvs in
    let vslet = VarSym.mk_qual (mk_name ~name:"u__" se) qual rv.e_ty in
    let cmds = [ LSamp(nrvs,(new_ty, [])); LLet(vslet, inst_ctxt c1 nrv) ] in
    let subst e = e_replace rv (mk_V vslet) e in
    let sec =
      { seoc.seoc_sec with
        sec_right = map_gdef_exp subst seoc.seoc_sec.sec_right;
        sec_ev    = subst seoc.seoc_sec.sec_ev }
    in
    let seoc =
      { seoc with
        seoc_return = subst seoc.seoc_return;
        seoc_cright = L.map (map_lcmd_exp subst) seoc.seoc_cright;
        seoc_sec = sec }
    in
    Rrnd_orcl(p,c1,c2), [ { ju with ju_se = set_se_octxt cmds seoc } ]
  | _ -> tacerror "rnd_oracle: position given is not a sampling"

let ct_rnd_oracle p c1 c2 = prove_by (r_rnd_oracle p c1 c2)

(* *** Use finite_map sX : T -> () for domain of another map 
 * ----------------------------------------------------------------------- *)

let r_sep_dom ms1 ms2 ju =
  let se = ju.ju_se in
  let neq_ms1 ms = not (MapSym.equal ms1 ms) in
  let se =
    map_se_finmap se
      ~f_in_dom:(fun ms k ->
                   if neq_ms1 ms then Expr.mk_MapIndom ms k
                   else Expr.mk_MapIndom ms2 k)
      ~f_lookup:(fun ms k -> Expr.mk_MapLookup ms k)
      ~f_GMSet:(fun ms ek e ->
                  if neq_ms1 ms then [GMSet(ms,ek,e)]
                  else [GMSet(ms,ek,e); GMSet(ms2,ek,mk_Tuple [])])
      ~f_LMSet:(fun ms ek e ->
                  if neq_ms1 ms then [LMSet(ms,ek,e)]
                  else [LMSet(ms,ek,e); LMSet(ms2,ek,mk_Tuple [])])
  in
  let ju = { ju with ju_se = se } in
  Rsep_dom(ms1,ms2), [ ju ]

let ct_sep_dom ms1 ms2 = prove_by (r_sep_dom ms1 ms2)

(* *** Copy condition implied by event to assert.
 * ----------------------------------------------------------------------- *)

let r_assert p e ju =
  let se = ju.ju_se in
  assert (not (is_Quant se.se_ev));
  let cmd, sec = get_se_ctxt se p in
  assert (equal_ty e.e_ty mk_Bool);
  (* check that e well-defined at desired position, exploits
     uniqueness of variables, i.e., v defined => v remains unchanged *)
  let wfs = wf_gdef NoCheckDivZero (L.rev sec.sec_left) in
  wf_expr CheckDivZero wfs e;
  let cmds = [ GAssert(e); cmd ] in
  let ju1 =
    { ju_pr = Pr_Succ;
      ju_se = { se with
                se_ev = mk_Land [ mk_Not e; se.se_ev ] } }
  in
  let ju2 = { ju with ju_se = set_se_ctxt cmds sec } in
  Rassert(p,e), [ ju1; ju2 ]

let ct_assert p e = prove_by (r_assert p e)

(* *** Rewrite oracle using test.
 * ----------------------------------------------------------------------- *)

let r_rewrite_oracle op dir ju =
  let se = ju.ju_se in
  match get_se_octxt se op with
  | LGuard(t) as lc, seoc ->
    let (a,b) =
      match t.e_node with
      | App(Eq,[u;v]) -> if dir = LeftToRight then (u,v) else (v,u)
      | _ -> tacerror "rewrite_oracle: can only rewrite equalities"
    in
    let subst e = e_replace a b e in
    let seoc =
      { seoc with
        seoc_cright = L.map (map_lcmd_exp subst) seoc.seoc_cright;
        seoc_return = subst seoc.seoc_return }
    in
    Rrw_orcl(op,dir), [ { ju with ju_se = set_se_octxt [lc] seoc } ]
  | _ ->
    tacerror "rewrite_oracle: invalid position"

let ct_rewrite_oracle op dir = prove_by (r_rewrite_oracle op dir)

(* *** Merge conjuncts in event with equalities.
 * ----------------------------------------------------------------------- *)

let merge_base_event ev1 ev2 =
  match ev1.e_node, ev2.e_node with
  | App (Eq,[e11;e12]), App(Eq,[e21;e22]) ->
    mk_Eq (mk_Tuple [e11;e21]) (mk_Tuple [e12;e22])
  | _, _ -> failwith "merge_ev: cannot merge the given events"

let r_merge_ev i j ju =
  let se = ju.ju_se in
  let i,j = if i <= j then i, j else j, i in
  let evs = destr_Land_nofail se.se_ev in
  let l,b1,r = Util.split_n i evs in
  let l',b2,r =
    if i = j then [], b1, r
    else Util.split_n (j - i - 1) r
  in
  let ev = merge_base_event b1 b2 in
  let evs = L.rev_append l (L.rev_append l' (ev::r)) in
  let new_se = { se with se_ev = mk_Land evs } in
  Rmerge_ev(i,j), [ { ju with ju_se = new_se } ]

let ct_merge_ev i j = prove_by (r_merge_ev i j)

(* *** Split (in)equality on tuples into multiple inequalities.
 * ----------------------------------------------------------------------- *)

let r_split_ev i ju =
  let rn = "split_ev" in
  let se = ju.ju_se in
  let ev = se.se_ev in
  let evs = destr_Land_nofail ev in
  if i < 0 || i >= L.length evs then
    tacerror "%s: invalid event position %i" rn i;
  let l,b,r = Util.split_n i evs in
  let b =
    if not (is_Eq b)
      then tacerror "rsplit_ev: bad event, expected equality";
    let (e1,e2) = destr_Eq b in
    if not (is_Tuple e1 && is_Tuple e2)
      then tacerror "rsplit_ev: bad event, expected tuples, %a and %a" pp_expr e1 pp_expr e2;
    let es1, es2 = destr_Tuple e1, destr_Tuple e2 in
    if not (L.length es1 = L.length es2)
      then tacerror "rsplit_ev: bad event, got tuples of diffe lengths, %a and %a"
             pp_expr e1 pp_expr e2;
    L.map (fun (e1,e2) -> mk_Eq e1 e2) (L.combine es1 es2)
  in
  let evs = l@b@r in
  let new_se = { se with se_ev = mk_Land evs } in
  Rsplit_ev(i), [ { ju with ju_se = new_se } ]

let ct_split_ev i = prove_by (r_split_ev i)

(* *** Use equality conjunct to rewrite other conjuncts
 * ----------------------------------------------------------------------- *)

let r_rw_ev i d ju =
  let rn = "rewrite_ev" in
  let se = ju.ju_se in
  let ev = se.se_ev in
  let evs = destr_Land_nofail ev in
  if i < 0 || i >= L.length evs then
    tacerror "%s: invalid event position %i" rn i;
  let l,b,r = Util.split_n i evs in
  let u,v =
    if is_Eq b then (
      let u,v = destr_Eq b in
      if d = LeftToRight then (u,v) else (v,u)
    ) else if is_Not b && is_Eq (destr_Not b) then (
      let eq = destr_Not b in
      if d = LeftToRight then (eq,mk_False)
      else tacerror "%s: inequality can only be used from left to right" rn
    ) else (
      tacerror "%s: bad event, expected equality or inequality" rn
    )
  in
  let subst e = e_replace u v e in
  let evs = (L.map subst l |> L.rev)@[b]@(L.map subst r) in
  let new_se = { se with se_ev = mk_Land evs } in
  Rrw_ev(i,d), [ { ju with ju_se = new_se } ]

let ct_rw_ev i d = prove_by (r_rw_ev i d)

(* *** Move sampling from once-oracle to main.
 * ----------------------------------------------------------------------- *)

let r_move_main ((i,j,k) as opos_eq) vname ju =
  let se = ju.ju_se in
  match get_se_octxt se (i,j,k,Oishyb OHeq) with
  | LSamp(vs,d),seoc ->
    let vs_new = VarSym.mk vname vs.VarSym.ty in
    let subst e = e_replace (mk_V vs) (mk_V vs_new) e in
    let samp = GSamp(vs_new,d) in
    let sec =
      { sec_left  = samp::seoc.seoc_sec.sec_left;
        sec_right = map_gdef_exp subst seoc.seoc_sec.sec_right;
        sec_ev    = subst seoc.seoc_sec.sec_ev;
      }
    in
    let seoc =
      { seoc with
          seoc_sec = sec;
          seoc_cleft = L.map (map_lcmd_exp subst) seoc.seoc_cleft;
          seoc_cright = L.map (map_lcmd_exp subst) seoc.seoc_cright;
          seoc_return = subst seoc.seoc_return }
    in
    let se = set_se_octxt [] seoc in
    wf_se NoCheckDivZero se;
    Rmove_main opos_eq, [ { ju with ju_se = se } ]
  | _ ->
    assert false

let ct_move_main opos vname =
  prove_by (r_move_main opos vname)

(* ** Core rules: Bridging rules with small loss
 * ----------------------------------------------------------------------- *)

(* *** Sampling from excepted distribution.
 * ----------------------------------------------------------------------- *)

let r_except p es ju =
  let se = ju.ju_se in
  let len = L.length se.se_gdef in
  if not (p < len) && p >= 0 then
    tacerror "except: invalid position, %i not between 1 and %i" (p+1) len;
  match get_se_ctxt se p with
  | GSamp(_,(_,es')), _ when equal_list equal_expr es' es ->
    tacerror "except: identical exceptions already present"
  | GSamp(vs,(t,_)), sec ->
    let se = set_se_ctxt [ GSamp(vs,(t,es)) ] sec in
    wf_se NoCheckDivZero se;
    Rexc(p, es), [ {ju with ju_se = se } ]
  | _ ->
    tacerror "except: position given is not a sampling"

let ct_except p es = prove_by (r_except p es)

(* *** Sampling from excepted distribution for oracle.
 * ----------------------------------------------------------------------- *)

let r_except_oracle p es ju =
  let se = ju.ju_se in
  match get_se_octxt se p with
  | LSamp(_,(_,es')), _ when equal_list equal_expr es' es ->
    tacerror "except_oracle: identical exceptions already present"
  | LSamp(vs,(t,_)), seoc ->
    let se = set_se_octxt [LSamp(vs,(t,es))] seoc in
    Rexc_orcl(p,es), [ { ju with ju_se = se } ]
  | _ -> tacerror "except_oracle: position given is not a sampling"

let ct_except_oracle p es = prove_by (r_except_oracle p es)

(* ** Core rules: Weaken event.
 * ----------------------------------------------------------------------- *)

(* *** Perform case distinction on event.
 * ----------------------------------------------------------------------- *)

let conj_or_negation_included e ev =
  let norm = Norm.norm_expr_weak in
  let evs = L.map norm (destr_Land_nofail ev) in
  (L.mem (norm e) evs || L.mem (norm (mk_Not e)) evs)

let r_case_ev ?flip:(flip=false) ?allow_existing:(ae=false) e ju =
  let se = ju.ju_se in
  ensure_pr_Succ_or_Adv "case_ev" ju;
  let ev = se.se_ev in
  if not ae && conj_or_negation_included e ev then
    tacerror "case_ev: event or negation already in event";
  let rec add_conj ev e =
    (* FIXME: account for, e.g., e /\ (forall x, ...) *)
    if is_Quant ev then (
      let (q,bind,ev) = destr_Quant ev in
      mk_Quant q bind (add_conj ev e)
    ) else (
      mk_Land [ e; ev ]
    )
  in
  let ju1 =
    { ju with
      ju_se = { se with se_ev = add_conj se.se_ev e } }
  in
  let ju2 =
    { ju with
      ju_se = { se with se_ev = add_conj se.se_ev (mk_Not e) } }
  in
  Rcase_ev(flip,e), if flip then [ju2; ju1] else [ju1;ju2]

let ct_case_ev ?flip:(flip=false) ?allow_existing:(ae=false) e =
  prove_by (r_case_ev ~flip ~allow_existing:ae e)

(* *** Apply context to event
 * ----------------------------------------------------------------------- *)

let r_ctxt_ev i c ju =
  ensure_pr_Succ_or_Adv "ctxt_ev" ju;
  let se = ju.ju_se in
  let ev = se.se_ev in
  let evs = destr_Land_nofail ev in
  if i < 0 || i >= L.length evs then failwith "invalid event position";
  let l,b,r = Util.split_n i evs in
  let b =
    if is_Eq b then
      let (e1,e2) = destr_Eq b in
      mk_Eq (inst_ctxt c e1) (inst_ctxt c e2)
    else tacerror "ctxt_ev: bad event, expected equality"
  in
  let ev = mk_Land (L.rev_append l (b::r)) in
  let wfs = wf_gdef NoCheckDivZero (se.se_gdef) in
  wf_expr NoCheckDivZero wfs ev;
  let new_ju = { se with se_ev = ev } in
  Rctxt_ev(i,c), [ { ju with ju_se = new_ju } ]

let ct_ctxt_ev i c = prove_by (r_ctxt_ev i c)

(* *** Apply injective context to event
 * ----------------------------------------------------------------------- *)

let r_injective_ctxt_ev j c1 c2 ju =
  let se = ju.ju_se in
  let ev = se.se_ev in
  let evs = destr_Land_nofail ev in
  if j < 0 || j >= L.length evs then tacerror "Invalid index %i" j;
  let l,b,r = Util.split_n j evs in
  let b =
    let op,(e1,e2) =
      if is_Eq b then
        mk_Eq,destr_Eq b else
        if is_InEq b then
          mk_InEq,destr_Eq (destr_Not b) else
          tacerror "injective_ctxt_ev: bad event %a, expected \'=\' or \'<>\'" pp_expr b in

    ensure_bijection ~partial:true se c2 c1 (fst c1);
    op (inst_ctxt c1 e1) (inst_ctxt c1 e2) in
  let ev = mk_Land (L.rev_append l (b::r)) in
  let wfs = wf_gdef NoCheckDivZero (se.se_gdef) in
  wf_expr NoCheckDivZero wfs ev;
  let new_ju = { se with se_ev = ev } in
  Rinjective_ctxt_ev(j,c1,c2), [ { ju with ju_se = new_ju } ]

let ct_injective_ctxt_ev j c1 c2 = prove_by (r_injective_ctxt_ev j c1 c2)

(* *** Remove conjunct from event
 * ----------------------------------------------------------------------- *)

let r_remove_ev (rm:int list) ju =
  ensure_pr_Succ_or_Adv "ctxt_ev" ju;
  let se = ju.ju_se in
  let ev = se.se_ev in
  let quant, ev_body =
    if is_Quant ev then (
      let (q,bind,e) = destr_Quant ev in
      Some (q,bind), e
    ) else (
      None,ev
    )
  in
  let evs =
    destr_Land_nofail ev_body
    |> L.mapi (fun i e -> if L.mem i rm then None else Some e)
    |> cat_Some
  in
  let new_ev_expr = if evs = [] then mk_True else mk_Land evs in
  let new_ev =
    match quant with
    | Some (q, bind) -> mk_Quant q bind new_ev_expr
    | None           -> new_ev_expr
  in
  Rremove_ev rm, [ { ju with ju_se = { se with se_ev = new_ev } } ]

let ct_remove_ev rm = prove_by (r_remove_ev rm)

(* ** Core rules: Bound probability directly
 * ----------------------------------------------------------------------- *)

(* *** Admit proof obligation
 * ----------------------------------------------------------------------- *)

let r_admit s _g = Radmit s, []
let ct_admit s = prove_by (r_admit s)

(* *** Distinguishability judgments are symmetric
 * ----------------------------------------------------------------------- *)

let r_dist_sym ju =
  match ju.ju_pr with
  | Pr_Dist se' ->
    Rdist_sym, [ { ju_se = se'; ju_pr = Pr_Dist ju.ju_se } ]
  | _ ->
    tacerror "dist_sym: Dist judgment expected"

let ct_dist_sym = prove_by r_dist_sym

(* *** Equal experiments cannot be distinguished
 * ----------------------------------------------------------------------- *)

let r_dist_eq ju =
  match ju.ju_pr with
  | Pr_Dist se' ->
    check_convertible "dist_eq" true ju.ju_se se';
    Rdist_eq, []
  | _ ->
    tacerror "dist_eq: Dist judgment expected"

let ct_dist_eq = prove_by r_dist_eq

(* *** Bound false event
 * ----------------------------------------------------------------------- *)

let r_false_ev ju =
  ensure_pr_Succ_or_Adv "ctxt_ev" ju;
  if is_False ju.ju_se.se_ev
  then Rfalse_ev, []
  else tacerror "false_ev: event false expected"

let ct_false_ev = prove_by r_false_ev

(* *** Bound random independence
 * ----------------------------------------------------------------------- *)

let check_event r ev =
  if is_Quant ev
     then tacerror "indep: the event can not be quantified";
  let r = mk_V r in
  let rec aux i evs =
    match evs with
    | [] ->
      tacerror "indep: can not apply for variable %a and event@\  %a@\n"
        pp_expr r pp_expr ev
    | ev::evs ->
      let test_eq e1 e2 = equal_expr e1 r && not (Se.mem r (e_vars e2)) in
      let check_eq e1 e2 =
        if test_eq e1 e2 then
          Rrnd_indep(true, i)
        else if test_eq e2 e1 then
          Rrnd_indep(false,i)
        else raise Not_found
      in
      try
        if is_Eq ev then
          let e1, e2 = destr_Eq ev in
          check_eq e1 e2
        (*
        else if is_Exists ev then
          let e1,e2,_ = destr_Exists ev in
          check_eq e1 e2
        *)
        else aux (i+1) evs
      with Not_found -> aux (i+1) evs
  in
  aux 0 (destr_Land_nofail ev)

let r_random_indep ju =
  let se = ju.ju_se in
  match L.rev se.se_gdef with
  | GSamp(r,_)::_ ->
    if equal_ty r.VarSym.ty mk_Bool then ensure_pr_Adv "indep" ju;
    check_event r se.se_ev, []
  | _             -> tacerror "indep: the last instruction is not a random"

let ct_random_indep = prove_by r_random_indep

(* *** Apply computational assumption
 * ----------------------------------------------------------------------- *)

let pp_range fmt (i,j) =
  F.fprintf fmt "%i - %i" i j

let ensure_ranges_cover_gdef rn rngs0 pref_len gdef =
  let gdef_len = L.length gdef in
  let rec go covered_upto rngs =
    match rngs with
    | [] ->
      if covered_upto <> gdef_len then
        tacerror "%s: ranges %a cover only up to to line %i, must cover up to %i"
          rn
          (pp_list "," pp_range) rngs0
          covered_upto gdef_len
    | (i,j)::rngs ->
      if i = covered_upto then go (j + 1) rngs
      else
        tacerror "%s: start %i of range should be %i" rn i covered_upto
  in
  go pref_len rngs0

let ensure_res_lets rn vres cres =
  assert (L.length vres = L.length cres);
  L.iter2
    (fun vs c ->
      match c with
      | GLet(vs',_) when VarSym.equal vs' vs -> ()
      | _ -> 
        Format.eprintf "%a@." (pp_gcmd ~nonum:true) c;
        tacerror "%s: result binding not found for %a" rn VarSym.pp vs)
    vres cres

let assm_comp_valid_ranges rn assm acalls_ju rngs =
  let pref = assm.ac_prefix in
  let pref_len = L.length pref in
  let priv_vars = private_vars_comp assm in
  let rec go rngs acalls =
    match rngs, acalls with
    | [], [] -> ()
    | _::_, [] |  [], _::_ ->
      tacerror "%s: ranges and adversary calls do not match up" rn
    | (i,j)::rngs, (_,vres,e)::acalls ->
      let len = j - i + 1 in
      let len_res = L.length vres in
      let len_body = len - 1 - len_res in
      let acalls_ju = L.drop (i - pref_len) acalls_ju in
      let c_arg  = L.hd acalls_ju in
      let c_body = L.take len_body (L.drop 1 acalls_ju) in
      let c_res  = L.take len_res (L.drop (1 + len_body) acalls_ju) in
      let read = read_gcmds (c_body@c_res) in
      ensure_not_use rn read priv_vars (c_body@c_res);
      if not assm.ac_inf then ensure_ppt rn (c_body@c_res);
      ensure_res_lets rn vres c_res;
      (* check and replace argument for adversary call *)
      (match c_arg with
       | GLet (_, e_arg) when (equal_expr e_arg e) -> ()
       | GLet (_, e_arg) ->
         tacerror "%s: expected argument %a, got %a" rn
           pp_expr e_arg pp_expr e
       | _ ->
         tacerror "%s: range must start with let" rn);
      go rngs acalls
  in
  go rngs assm.ac_acalls

let r_assm_comp assm0 rngs ren ju =
  let rname = "assumption_computational" in
  let se = ju.ju_se in
  let assm = Assumption.inst_comp ren assm0 in
  (match assm.ac_type with
   | A_Adv  -> ensure_pr_Adv rname ju
   | A_Succ -> ensure_pr_Succ_or_Adv rname ju
  );
  let pref = assm.ac_prefix in
  let pref_len = L.length pref in
  let pref_ju = L.take pref_len se.se_gdef in
  let acalls_ju = L.drop pref_len se.se_gdef in
  ensure_ren_inj rname ren;
  ensure_gdef_eq rname pref pref_ju;
  ensure_event_eq rname se.se_ev assm.ac_event;
  ensure_ranges_cover_gdef rname rngs (L.length pref_ju) se.se_gdef;
  (* check that we can instantiate calls in assumption with remainder of ju *)
  assm_comp_valid_ranges rname assm acalls_ju rngs;
  Rassm_comp(rngs,ren,assm0), []

let ct_assm_comp assm ev_e subst = prove_by (r_assm_comp assm ev_e subst)

(* ** Core rules: Rules with computationally bounded loss
 * ----------------------------------------------------------------------- *)

(* *** Apply decisional assumption
 * ----------------------------------------------------------------------- *)

let gcmd_of_lcmd rn lcmd = 
  match lcmd with
  | LLet(x,e) -> GLet(x,e)
  | LMSet(h,e1,e2) -> GMSet(h,e1,e2)
  | LSamp(x,d) -> GSamp(x,d)
  | LBind  _ | LGuard _ ->
    tacerror "%s: cannot transalate oracle into main" rn
  
let gcmd_of_lcmds rn = L.map (gcmd_of_lcmd rn)

let assm_dec_valid_ranges rn dir assm acalls_ju (rngs:rng list) =
  let swap_dir = if dir = LeftToRight then id else Util.swap in
  let (pref,_) = swap_dir (assm.ad_prefix1,assm.ad_prefix2) in
  let pref_len = L.length pref in
  let priv_vars = private_vars_dec assm in

  let count_sym = OrclSym.H.create 10 in
  let check_counter o c counter = 
    match c, counter with
    | Once, Once -> 
      if OrclSym.H.mem count_sym o then
        tacerror "%s: to many call to oracle %a" rn OrclSym.pp o;
          OrclSym.H.add count_sym o ()
    | _, Once ->
      tacerror "%s: to many call to oracle %a" rn OrclSym.pp o
    | _, _ -> () in

  let init_subst x vs b1 b2 = 
    
    let ex = mk_V x in
        let s = 
          match vs with
          | []  -> Me.empty
          | [y] -> Me.add (mk_V y) ex Me.empty
          | vs  ->
            L.fold_lefti (fun s i y ->
                let ey = mk_V y and ep = mk_Proj i ex in
                Me.add ey ep s) Me.empty vs in
        let subst_e = e_subst s in
        map_obody_exp subst_e b1, map_obody_exp subst_e b2 in

  let check_main_body priv_vars vs body b1 b2 = 
        let x,e, body1 = 
          match body with
          | GLet(x,e):: body1 -> x,e, body1
          | _ -> tacerror "%s: invalid first instruction in oracle main body" rn
        in
        (* substitution of vs by the projection of x *)
        let (lc1,res1), (lc2,res2) = init_subst x vs b1 b2 in 
        (* Check that body is of the following form:
           let x = e in
           lc1;
           let z = res1 in 
        *)
        let gc1 = gcmd_of_lcmds rn lc1 in
        let hdb = L.take (L.length gc1) body1 in
        if not (equal_gdef gc1 hdb) then
          tacerror "%s: cannot reconize oracle body in main %a %a" rn
                   (pp_gdef ~nonum:true) gc1 
                   (pp_gdef ~nonum:true) hdb;
        let z = 
          match L.drop (L.length gc1) body1 with
          | [GLet(z, e)] when equal_expr res1 e -> z
          | [GLet(z, e)] -> tacerror "%s: cannot recognize oracle res in main,
          got %a, expected %a" rn pp_expr e pp_expr res1
          | [gc] -> tacerror "%s: cannot reconize oracle res in main, got gcmd
          %a" rn (pp_gcmd ~nonum:false) gc
          | _ -> tacerror "%s: cannot reconize oracle res in main" rn
        in
        let i = GLet(x,e) in
        let read = read_gcmd i in
        ensure_not_use rn read priv_vars [i];
        ensure_ppt rn [i];
        let priv_vars = Se.union (write_gcmds (i::gc1)) priv_vars in
        priv_vars, i :: (gcmd_of_lcmds rn lc2) @ [GLet(z,res2)] in

  let find_orcl ad_ac o = 
     try
       List.find (fun (o',_,_,_) -> OrclSym.equal o o') ad_ac.ad_ac_orcls
     with Not_found ->
       tacerror "%s: unknown oracle %a" rn OrclSym.pp o in

  let check_orcl_bodies ad_ac priv_vars info os = 
    let check_obody (oc,ores) rgns ocount = 
      let rec aux priv_vars len body rngs = 
        match rngs with
        | [] -> 
          let read = Se.union (read_lcmds body) (e_vars ores) in
          ensure_not_use_le rn read priv_vars body ores;
          ensure_ppt_le rn body ores;
          priv_vars, body
        | (i, j, o) :: rngs ->
          let (_, vs, obody, counter) = find_orcl ad_ac o in
          check_counter o ocount counter;
          let b1, b2 =  swap_dir obody in
          if i < len || j < i then
            tacerror "%s: bad oracle range %a" rn OrclSym.pp o;
          let (i, j) = i - len, j - len in
          let pre_body =  L.take i body in
          let body1 = L.take (j - i + 1) (L.drop i body) in
          let x,e,body1 = 
            match body1 with
            | LLet(x,e):: body1 -> x,e, body1
            | _ -> 
              tacerror "%s: invalid first instruction in oracle body" rn
          in
          let post_body = L.drop (j+1) body in

          let read = read_lcmds pre_body in
          ensure_not_use_l rn read priv_vars pre_body;
          ensure_ppt_l rn pre_body;
          (* Check that body can be see as an instance of oracle call *)
          
          let (lc1,res1), (lc2,res2) = init_subst x vs b1 b2 in 
          let hdb = L.take (L.length lc1) body1 in
          if not (equal_lcmds lc1 hdb) then
            tacerror "%s: cannot reconize oracle body %a should be %a" rn
              (pp_lcmds ~qual:Unqual) hdb
              (pp_lcmds ~qual:Unqual) lc1;

          let z = 
            match L.drop (L.length lc1) body1 with
            | [LLet(z, e)] when equal_expr res1 e -> z
            | [LLet(z, e)] -> tacerror "%s: cannot recognize oracle res in main,
            got %a, expected %a" rn pp_expr e pp_expr res1
            | _ -> tacerror "%s: cannot reconize oracle res in main" rn
          in
          let i = LLet(x,e) in
          let read = read_lcmd i in
          ensure_not_use_l rn read priv_vars [i];
          ensure_ppt_l rn [i];
          let priv_vars = Se.union (write_lcmds hdb) priv_vars in
          let body2 = i :: lc2 @ [LLet(z,res2)] in
          let priv_vars, post_body2 = 
            aux priv_vars (len + j + 1) post_body rngs in
          priv_vars, pre_body @ body2 @ post_body2 in
      let _, oc2 = aux priv_vars 0 oc rgns in
      (oc2, ores) in

    let check_odecl i (o,vs,od,ocount) = 
      let od = 
        match od with
        | Oreg obody ->
          Oreg (check_obody obody (info i Onothyb) ocount)
        | Ohyb ohybrid ->
          Ohyb {
              oh_less = 
                check_obody ohybrid.oh_less (info i (Oishyb OHless)) ocount;
              oh_eq = 
                check_obody ohybrid.oh_eq (info i (Oishyb OHeq)) Once;
              oh_greater =
                check_obody ohybrid.oh_greater (info i (Oishyb OHgreater)) ocount; }
      in
      (o,vs,od,ocount) in
    List.mapi check_odecl os in
 
  let rec do_orcl ad_ac priv_vars len body rng_os = 
    match rng_os with
    | [] -> 
      let read = read_gcmds body in
      ensure_not_use rn read priv_vars body;
      ensure_ppt rn body;
      Format.eprintf "end body @[<v>%a@]@." (pp_gdef ~nonum:false) body;
      priv_vars, body

    | RO_rng (i, j, o) :: rng_os ->
      let (_, vs, obody, counter) = 
        try
          List.find (fun (o',_,_,_) -> OrclSym.equal o o') ad_ac.ad_ac_orcls
        with Not_found ->
              tacerror "%s: unknown oracle %a" rn OrclSym.pp o in
      check_counter o Once counter;
      let b1, b2 =  swap_dir obody in
      if i < len || j < i then
        tacerror "%s: bad oracle range %a" rn OrclSym.pp o;
      let (i, j) = i - len, j - len in
      Format.printf "%i %i@." i j;
      Format.eprintf "body @[<v>%a@]@." (pp_gdef ~nonum:false) body;
      let pre_body =  L.take i body in
      Format.eprintf "pre body @[<v>%a@]@." (pp_gdef ~nonum:false) pre_body;
      let read = read_gcmds pre_body in
      ensure_not_use rn read priv_vars pre_body;
      ensure_ppt rn (pre_body);
      
      let bodyo = L.take (j - i + 1) (L.drop i body) in
      Format.eprintf "body @[<v>%a@]@." (pp_gdef ~nonum:false) body;
      let post_body = L.drop (j+1) body in
      Format.eprintf "post_body @[<v>%a@]@." (pp_gdef ~nonum:false) post_body;
      let priv_vars, body2 = check_main_body priv_vars vs bodyo b1 b2 in
      let priv_vars, post_body2 = 
        do_orcl ad_ac priv_vars (len + j + 1) post_body rng_os in
      priv_vars, pre_body @ body2 @ post_body2
    | RO_orcl (i, info) :: rng_os ->
      if i < len then
        tacerror "%s: bad oracle range" rn;
      let i = i - len in
      let pre_body = L.take i body in
      let (xs,a,e,os) = 
        match L.hd (L.drop i body) with
        | GCall(xs,a,e,os) -> (xs,a,e,os)
        | _ -> 
          tacerror "%s: range does not correspond to an adversary call" rn
      in
      let post_body = L.drop (i+1) body in
      let os2 = check_orcl_bodies ad_ac priv_vars info os in  
      let priv_vars, post_body2 = 
        do_orcl ad_ac priv_vars (len + i + 1) post_body rng_os in
      priv_vars, pre_body @ GCall(xs,a,e,os2) :: post_body2
  in

  let rec go len_all priv_vars rngs acalls acalls_new =
(*    Format.eprintf "len_all = %i    %i@." len_all (List.length acalls_ju); *)
    match rngs, acalls with
    | [], [] -> 
      if len_all <> (List.length acalls_ju + pref_len) then
          tacerror "%s: size of range and adversary calls do not match up;
          %i vs %i "  rn len_all (List.length acalls_ju + pref_len);
      acalls_new
    | r::rngs, ad_ac::acalls ->
      let vres = ad_ac.ad_ac_lv in
      let (e1,e2) = ad_ac.ad_ac_args in
      let e_old,e_new = swap_dir (e1,e2) in
      let i, j = r.r_start, r.r_end in
      if i <> len_all then
        tacerror "%s: invalid range instructions are skipped, (%i,%i) should start by %i" rn (i+1) (j+1) (len_all +1);
      let len = j - i + 1 in
      let len_res = L.length vres in
      let len_body = len - 1 - len_res in
      let acalls_ju = L.drop (i - pref_len) acalls_ju in
      let c_arg  = L.hd acalls_ju in
      let c_body = L.take len_body (L.drop 1 acalls_ju) in
      let c_res  = L.take len_res  (L.drop (1 + len_body) acalls_ju) in
      Format.eprintf "ADV : @[<v>%a@]@."
                     (pp_gdef ~nonum:true) (c_arg::c_body @ c_res); 
      (* Check that the body can be see as an adversary calling oracles *)
     
      let priv_vars, c_body2 = do_orcl ad_ac priv_vars (i + 1) c_body r.r_orcl in
      let read = read_gcmds c_res in
      ensure_not_use rn read priv_vars c_res;
      ensure_ppt rn c_res;
      (*if not assm.ad_inf then ensure_ppt rn (c_body@c_res);*)
      ensure_res_lets rn vres c_res;
      let v_arg =
        match c_arg with
        | GLet (v_arg, e_arg) when (equal_expr e_arg e_old) -> v_arg
        | GLet (_, e_arg) ->
          tacerror "%s: expected argument %a, got %a"
            rn pp_expr e_old pp_expr e_arg
        | _ -> tacerror "%s: expected let in first line of range %a" rn
                        (pp_gcmd ~nonum:true) c_arg
      in
      go (len_all + len) priv_vars rngs acalls
         (acalls_new@[GLet(v_arg,e_new)]@c_body2@c_res)
    | _, _ -> tacerror "%s: ranges and adversary calls do not match up" rn
  in
  go pref_len priv_vars rngs assm.ad_acalls []

let r_assm_dec dir ren rngs assm0 ju =
  let rn = "assumption_decisional" in
  let se = ju.ju_se in
  let swap_dir = if dir = LeftToRight then id else Util.swap in
  (* check that prefix of (renamed) assumption coincides with prefix of ju *)
  let assm = Assumption.inst_dec ren assm0 in
  let pref_old,pref_new = swap_dir (assm.ad_prefix1,assm.ad_prefix2) in
  let pref_old_len = L.length pref_old in
  let pref_ju = L.take pref_old_len se.se_gdef in
  let acalls_ju = L.drop pref_old_len se.se_gdef in
  ensure_ren_inj rn ren;
  ensure_gdef_eq rn pref_ju pref_old;
  (* check that event is equal to last returned variable *)
  begin match L.last acalls_ju with
    | (GLet(vs,_) | GCall([vs], _, _, _)) when 
          equal_expr se.se_ev (mk_V vs) -> ()
    | _                                             -> 
       tacerror "assm_dec: event %a must be equal to variable defined in last line" pp_expr se.se_ev
  end; 
  (* ensure_ranges_cover_gdef rn rngs (L.length pref_ju) se.se_gdef; *)
  (* check that we can instantiate calls in assumption with remainder of ju *)
  let acalls_ju_new = assm_dec_valid_ranges rn dir assm acalls_ju rngs in
  let se = { se with se_gdef = pref_new@acalls_ju_new } in
  Rassm_dec(rngs,dir,ren,assm0), [{ ju with ju_se = se }]

let ct_assm_dec dir ren rngs assm = prove_by (r_assm_dec dir ren rngs assm)

(* *** Add a new test to oracle.
 * ----------------------------------------------------------------------- *)

let r_add_test opos tnew asym fvs ju =
  let se = ju.ju_se in
  match get_se_octxt se opos with
  | LGuard(t), seoc ->
    assert (equal_ty tnew.e_ty mk_Bool);
    let destr_guard lcmd =
      match lcmd with
      | LGuard(e) -> e
      | _ -> tacerror "add_test: new test cannot be inserted after %a, %s"
               (pp_lcmd ~qual:Unqual) lcmd "preceeding commands must be tests"
    in
    let tests = L.map destr_guard (L.rev seoc.seoc_cleft) in
    let subst =
      L.fold_left2
        (fun s ov fv -> Me.add (mk_V ov) (mk_V fv) s)
        Me.empty seoc.seoc_oargs fvs
    in
    let seoc = { seoc with seoc_cleft = LGuard(tnew) :: seoc.seoc_cleft } in
    let seoc_bad =
      { seoc with
        seoc_asym = asym;
        seoc_avars = fvs;
        seoc_sec =
          { seoc.seoc_sec with
            sec_ev = e_subst subst (mk_Land (tests@[ t ; mk_Not tnew]));
            sec_right = [] } }
    in
    let ju1 = {ju_se = set_se_octxt [LGuard(t)] seoc_bad; ju_pr = Pr_Succ } in
    let ju2 = { ju with ju_se =  set_se_octxt [LGuard(t)] seoc } in
    Radd_test(opos, tnew, asym, fvs), [ ju1; ju2 ]
  | _ -> tacerror "add_test: given position is not a test"

let ct_add_test p tnew asym fvs = prove_by (r_add_test p tnew asym fvs)

(* *** Transitivity: bound distance to given intermediate game.
 * ----------------------------------------------------------------------- *)

let r_trans new_se ju =
  wf_se NoCheckDivZero new_se;
  let se = ju.ju_se in
  let ju1 = { ju_se = se; ju_pr = Pr_Dist new_se } in
  let ju2 = { ju_se = new_se; ju_pr = ju.ju_pr } in
  Rtrans, [ ju1; ju2 ]

let ct_trans new_se =
  prove_by (r_trans new_se)


(* ** Core rule: Hybrid argument.
 * ----------------------------------------------------------------------- *)

let rename_odef lcmds ret =
  let vmap = VarSym.H.create 134 in
  let add_mapping lcmd =
    match lcmd with
    | LLet(v,_) | LSamp(v,_) ->
      let id = v.VarSym.id in
      let new_v = VarSym.mk (Id.name id) v.VarSym.ty in
      VarSym.H.add vmap v new_v
    | LMSet(_,_,_)
    | LGuard(_) -> ()
    | LBind(_) -> assert false
  in
  L.iter add_mapping lcmds;
  let sigma v = try VarSym.H.find vmap v with Not_found -> v in
  (L.map (subst_v_lcmd sigma) lcmds, subst_v_expr sigma ret)

let r_hybrid gpos oidx new_lcmds new_eret ju =
  let se = ju.ju_se in
  let _, seoc = get_se_octxt_len se (gpos,oidx,0,Onothyb) 0 in
  let old_lcmds = seoc.seoc_cright in
  let old_ret = seoc.seoc_return in
  (* replace oracle definition in second judgment *)
  let ju2  =
    { ju with
      ju_se =
        set_se_octxt []
          { seoc with
            seoc_return = new_eret;
            seoc_cright = new_lcmds } }
  in
  let ev = ju.ju_se.se_ev in
  assert (not (is_Quant ev));
  let splitEv =
    let conj = destr_Land_nofail ev in
    conc_map
      (fun e ->
        if is_All e then (
          match destr_All e with
          | (vs,Olist.Olist o),e1 when OrclSym.equal o seoc.seoc_osym ->
            [e; e_subst (L.fold_left2
                           (fun m e1 e2 -> Me.add (mk_V e1) (mk_V e2) m)
                           Me.empty vs seoc.seoc_oargs) e1]
          | _ -> [e]
        ) else (
          [e]
        )
      )
      conj
  in
  (* use hybrid oracles in first judgment *)
  let seoc_left1 =
    { seoc with
      seoc_sec = { seoc.seoc_sec with sec_ev = mk_Land splitEv };
      seoc_obless    = Some (rename_odef new_lcmds new_eret);
      seoc_obeq      = None;
      seoc_cright    = old_lcmds;
      seoc_return    = old_ret;
      seoc_obgreater = Some (rename_odef old_lcmds old_ret); }
  in
  let seoc_left2 =
    { seoc_left1 with
      seoc_return = new_eret;
      seoc_cright = new_lcmds; }
  in
  let ju1 =
    { ju_se = set_se_octxt [] seoc_left1;
      ju_pr = Pr_Dist (set_se_octxt [] seoc_left2);
    }
  in
  Rhybrid, [ ju1; ju2 ]

let ct_hybrid gpos oidx lcmds eret =
  prove_by (r_hybrid gpos oidx lcmds eret)

(* ** Core rule: Guard.
 * ----------------------------------------------------------------------- *)

let r_guard opos tnew ju =
  let se = ju.ju_se in
  let seoc,t =
    match tnew with
    | None ->
      begin match get_se_octxt se opos with
      | (LGuard(t), seoc) -> seoc, t
      | _ -> tacerror "guard: given position is not a test"
      end
   | Some t ->
      snd (get_se_octxt_len se opos 0), t in

  assert (equal_ty t.e_ty mk_Bool);
  let destr_guard lcmd =
    match lcmd with
    | LGuard(e) -> e
    | _ -> tacerror "add_test: new test cannot be inserted after %a, %s"
      (pp_lcmd ~qual:Unqual) lcmd "preceeding commands must be tests"
  in
  let vs =
    List.map (fun v -> VarSym.mk (VarSym.to_string v) v.VarSym.ty) seoc.seoc_oargs
  in

  let tests = L.map destr_guard (L.rev seoc.seoc_cleft) in
  let subst =
    L.fold_left2
      (fun s ov fv -> Me.add (mk_V ov) (mk_V fv) s)
      Me.empty seoc.seoc_oargs vs
  in

  (* bad event *)
  let seoc_bad =
    { seoc with
      seoc_sec =
        { seoc.seoc_sec with
          sec_right = [];
          sec_ev = mk_Quant
                     Exists
                     (vs,Olist.Olist seoc.seoc_osym)
                     (e_subst subst (mk_Land (mk_Not t::tests)))
        }
    }
  in
  let i = if tnew = None then [] else [LGuard t] in
  let ju1 = {ju_se = set_se_octxt i seoc_bad; ju_pr = Pr_Succ } in
  let ju2 = {ju with ju_se = set_se_octxt i seoc } in
  Wf.wf_se NoCheckDivZero ju1.ju_se;
  Wf.wf_se NoCheckDivZero ju2.ju_se;
  Rguard(opos, tnew), [ ju1; ju2 ]

let ct_guard p tnew = prove_by (r_guard p tnew)

(* ** Core rules: Deal with existential quantifiers
 * ----------------------------------------------------------------------- *)

(* *** Guess rule.
 * ----------------------------------------------------------------------- *)

let r_guess asym fvs ju =
  let ev = ju.ju_se.se_ev in
  let (q,b,ev_expr) = destr_Quant ev in
  match q, b, ju.ju_pr with
  | Exists, (vs,_o), Pr_Succ ->
     if not(equal_ty (ty_prod_vs fvs) (ty_prod_vs vs)) then
       tacerror "guess : invalid variables types";
    let subst =
      L.fold_left2
        (fun s ov fv -> Me.add (mk_V ov) (mk_V fv) s)
        Me.empty vs fvs in
    let e = e_subst subst ev_expr in
    let ju1 = { ju with
      ju_se = {
        se_gdef = ju.ju_se.se_gdef @ [GCall(fvs,asym,mk_Tuple [], [])];
        se_ev = e } }
    in
    Wf.wf_se NoCheckDivZero ju1.ju_se;
    Rguess asym, [ ju1 ]

  | _ ->
    tacerror "guess: not a valid event"

let ct_guess asym fvs = prove_by (r_guess asym fvs)

(* *** Find rule.
 * ----------------------------------------------------------------------- *)

let r_find (bd,body) arg asym fvs ju =
  let ev = ju.ju_se.se_ev in
  let (q,b,ev_expr) = destr_Quant ev in
  match q, b, ju.ju_pr with
  | Exists, (vs,_o), Pr_Succ ->
    assert (equal_ty (ty_prod_vs fvs) (ty_prod_vs vs));
    (* check that body{bd <- arg} = (Event.expr ev) *)
    assert (equal_ty (ty_prod_vs bd) arg.e_ty);
    let subst_bd =
      L.fold_left2 (fun s v e -> Me.add (mk_V v) e s) Me.empty bd
        (if L.length bd > 1 then destr_Tuple_nofail arg else [arg])
    in
    let fv = e_vars body in
    let se_vs = List.fold_left (fun s v -> Se.add (mk_V v) s) Se.empty in
    let allowed = Se.union (se_vs vs) (se_vs bd) in
    if not (Se.subset fv allowed) then
      tacerror "find not a closed function: %a contains variables not in %a"
        pp_expr body (pp_list "," pp_expr) (Se.elements allowed);
    let e1 = e_subst subst_bd body in
    if not (equal_expr e1 ev_expr) then
      tacerror "find: invalid event in function : %a \nvs %a" pp_expr e1 pp_expr ev_expr;
    (* check that the function is PPT *)
    if not (is_ppt body) then
      tacerror "find: the function is not ppt";
    (* build the game *)
    let subst =
      L.fold_left2
        (fun s ov fv -> Me.add (mk_V ov) (mk_V fv) s)
        Me.empty vs fvs in
    let e = e_subst subst ev_expr in
    let ju1 = {ju with
      ju_se = {
        se_gdef = ju.ju_se.se_gdef @ [GCall(fvs,asym,arg, [])];
        se_ev = e} }
    in
    Wf.wf_se NoCheckDivZero ju1.ju_se;
    Rfind (asym, (bd,body)), [ ju1 ]

  | _ ->
    tacerror "find: not a valid event"

let ct_find f arg asym fvs = prove_by (r_find f arg asym fvs)

(* ** Core rules: Rules for random oracles
 * ----------------------------------------------------------------------- *)

(*
(** bad rule that replaces hash call with random sampling *)
let rbad which_bad p gen_vsx ju =
  (* fail_if_occur vsx ju "rbad"; FIXME : why is this needed ?*)
  let se = ju.ju_se in
  let p_ctxt =
    try get_se_ctxt se p
    with
      Failure s -> tacerror "Invalid position %i :\n%s" (p+1) s
  in
  match p_ctxt with
  | GLet(vs,e'), se_ctxt when is_H e' ->
    let h,e = destr_H e' in
    let vsx = gen_vsx e in
    if (Vsym.S.mem vsx (expr_vars e)) then
      tacerror "Error, var '%a' appears in expr '%a'" Vsym.pp vsx pp_exp e;
    if not (Fsym.is_ro h) then
      tacerror "Error, the function '%a' is not a random oracle" Fsym.pp h;
    if (Fsym.is_lkup h) then
      tacerror "Error, 'bad' rule cannot be applied to the oracle lookup '%a'" Fsym.pp h;

    let cmds = [ GSamp(vs, (e'.e_ty,[]) )] in
    (* ju1 is ju with a random sampling instead of the hash call *)
    let ju1 = {ju with ju_se = (set_se_ctxt cmds se_ctxt) } in

    (* Checking that h is only used here *)
    let all_other_hash_calls_args =
      Se.union
        (gdef_all_hash_args h se_ctxt.sec_left)
        (gdef_all_hash_args h se_ctxt.sec_right)
    in
     if (Se.mem e all_other_hash_calls_args) then
       tacerror "Error, there cannot be other '%a' calls querying the expression '%a'"
         Fsym.pp h pp_expr e;
     let create_ju = match which_bad with
       | UpToBad -> fun ei ->
         { ju_pr = Pr_Succ ;
           ju_se = { ju1.ju_se with se_ev = Event.mk
                                              (mk_Eq e ei) } }
       | CaseDist -> fun ei ->
         { ju_pr = Pr_Succ ;
           ju_se = { ju.ju_se with se_ev = Event.insert
                                             ~e:(mk_Eq e ei)
                                             se.se_ev}}
     in
     let check_other_hc_expr_eq_jus =
       Se.fold (fun ei jus -> (create_ju ei)::jus) all_other_hash_calls_args []
       |> List.rev
     in
     let bad_ev_expr = mk_Eq (mk_V vsx) e in
     let bad_ev_binding = ([vsx],Oracle.mk_RO(h)) in
     let bad_n,ju2 = match which_bad with
     (* ju2 is ju1 where event = bad_event + main_event when UpToBad,
                              or bad_event only when CaseDist *)
       | CaseDist ->
          let conj_ev = Event.insert
                          ~quant:Exists
                          ~binding:bad_ev_binding
                          ~e:bad_ev_expr
                          se.se_ev in
          2, {ju_pr = Pr_Succ; ju_se = {ju.ju_se with se_ev = conj_ev} }
       | UpToBad ->
          let bad_ev = Event.mk
                         ~quant:Exists
                         ~binding:bad_ev_binding
                         bad_ev_expr in
          1, {ju_pr = Pr_Succ; ju_se = {ju1.ju_se with se_ev = bad_ev} }
     in
     Rbad(bad_n,p,vsx), ju1::ju2::check_other_hc_expr_eq_jus
  | _ ->
    tacerror
      ("cannot apply 'bad' rule at pos %i\n<< 'let var = H(expr)\' required:"
       ^^">>\n(note that the 'abstract' rule can be used to fold a hash call into a variable).")
      (p+1)

let ct_bad which_bad p gen_vsx =
  prove_by (rbad which_bad p gen_vsx)

(** Replace hash call by map lookup (still needs some work) *)
let rcheck_hash_args opos gen_o_lkup ju =
  let se = ju.ju_se in
  let bad_position ?s () =
    let (i,j,k,_) = opos in
    tacerror "Invalid guard position (%i,%i,%i)\n%s"
             (i+1) (j+1) (k+1)
             (match s with Some s -> "<< " ^ s ^ " >>" | _ -> "")
  in
  let gctxt =
    try get_se_octxt se opos with Failure s -> bad_position ~s ()
  in
  match gctxt with
  | (LGuard(eq) as lguard), se_octxt ->
     if not (is_SomeQuant eq) then
       tacerror "Error, '%a' is not a quantified expression" pp_exp eq;
     let _,(vs,o),eq = ExprUtils.destr_Quant eq in
     let o =
       try Oracle.destr_as_Fsym_t o
       with
         Oracle.Destr_failure _ ->
         tacerror "Error, '%a' is not a random oracle" Oracle.pp o
     in
     let o_lkup = gen_o_lkup o in
     let ve,e =
       try ExprUtils.destr_Eq eq
       with
         ExprUtils.Destr_failure _ ->
           tacerror "Error, expected 'v = expr' expression, with v bound in L_%a" Fsym.pp o
     in
     if not (List.exists (fun v -> e_equal ve (mk_V v)) vs) then
       tacerror "Error, expected 'v = expr' expression, with v bound in L_%a" Fsym.pp o;
     let seoc_cright = se_octxt.seoc_cright in
     let to_lkup = function
       | (h,e') when (Fsym.equal h o && e_equal e e') -> o_lkup
       | (h,_) -> h
     in
     let seoc_cright = subst_lkup_lcmds to_lkup seoc_cright in
     let se_octxt = {se_octxt with seoc_cright} in
     Rcheck_hash_args opos,[{ju with ju_se = set_se_octxt [lguard] se_octxt}]
  | _ -> bad_position ()

let ct_check_hash_args opos gen_o_lkup =
  prove_by (rcheck_hash_args opos gen_o_lkup)

*)
