(* * Decisional and computational assumptions *)

(* ** Imports *)
open Abbrevs
open Util
open Game
open Expr
open ExprUtils
open Syms

let mk_log level = mk_logger "Core.Assumption" level "Assumption.ml"
let log_t  = mk_log Bolt.Level.TRACE
let _log_d = mk_log Bolt.Level.DEBUG

(* ** Decisional assumptions
 * ----------------------------------------------------------------------- *)

(* For simplicity, we restrict ourselves to assumptions to be of the form
     \verb!r1 <-$ D1; ...; rn <-$ Dn; (vs1) <- A1(e1); ...; (vsk) <- Ak(ek);!
   where 'Di' might be an excepted distribution [*].
   Then the right assumption has the form
     \verb!r1' <-$ D1'; ...; rm' <-$ Dm'; (vs1) <- A1(b1); ...; (vsk) <- Ak(bk);!

   Given a judgment 'G : ev', renaming 'ren' (bij. mapping from variables
   ri, vsi_j to variables), we rename the assumption using 'ren' and check
   that the first n lines of 'G' conincide with the samplings from the
   resulting assumption.

   The remainder of 'G' must have the following form:
   \begin{verbatim}
   ---
   let a1 = e1;
   C1;                          |
   let vs1_1 =  a1_1;           \  := D1
   ...;                         /
   let vs1_|vs1| =  a1_|vs1|;   |

   ...

   let ak = ek;
   Ck;                          |
   let vsk_1 = ak_1;            \  := Dk
   ...;                         /
   let vsk_|vsk| = ak_|vsk|;    |
   --

   where for all i in [k],
     vars(Di\sigma_i) \cap {r1,..,rn} = emptyset.

  \end{verbatim}
  To obtain the new game, we just replace the prefix and replace
     ei by bi.

  To obtain such a game, it is important that for all i, it holds that
    $vars(e_i) \subseteq \{r1,..,rn\} \cup vs_{earlier}$.
  To achieve this, we must perform let_abstract for args last, front to
  back, and ensure that we do not use other variables.

  [*] Some extensions like allowing let-bindings in assumptions might be
      very simple while allowing samplings in between the adversary calls
      might be more complicated. This would allow for adaptive sampling,
      i.e., using vsj in the excepted expressions.
*)


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

let pp_acall_dec fmt ad_ac =
  let pp_odef2 fmt (os, vs, (b1,b2), c) = 
    F.fprintf fmt "@[<v>%a(@[<hov 0>%a@])%a =@ %a@ %a@]"
      OrclSym.pp os
      (pp_list "," (VarSym.pp_qual ~qual:(Qual os))) vs
      pp_ocounter c 
      (pp_obody ~nonum:false os None) b1
      (pp_obody ~nonum:false os None) b2 in

  let pp_orcls fmt orcls = 
    if orcls <> [] then 
      F.fprintf fmt " with@\n%a" (pp_list ",@;" pp_odef2) orcls in
  
  F.fprintf fmt "(%a) <- %a(%a | %a)@\n%a"
    (pp_list "," VarSym.pp) ad_ac.ad_ac_lv 
     AdvSym.pp ad_ac.ad_ac_sym 
     pp_expr (fst ad_ac.ad_ac_args) pp_expr (snd ad_ac.ad_ac_args)
     pp_orcls ad_ac.ad_ac_orcls

let pp_assm_dec fmt ad =
  F.fprintf fmt "assumption %s:@\n" ad.ad_name;
  F.fprintf fmt "prefix left:@\n%a@\n"  (pp_gdef ~nonum:false) ad.ad_prefix1;
  F.fprintf fmt "prefix right:@\n%a@\n" (pp_gdef ~nonum:false) ad.ad_prefix2;
  F.fprintf fmt "adversary calls:@\n%a@\n" (pp_list "@\n" pp_acall_dec) ad.ad_acalls;
  F.fprintf fmt "symvars: %a@\n" (pp_list "; " (pp_list "," VarSym.pp)) ad.ad_symvars

let mk_assm_dec name inf gd1 gd2 symvars =
  ignore (Wf.wf_gdef Wf.NoCheckDivZero gd1);
  ignore (Wf.wf_gdef Wf.NoCheckDivZero gd2);
  let (pref1,suff1) = L.partition (function GCall _ -> false | _ -> true) gd1 in
  let (pref2,suff2) = L.partition (function GCall _ -> false | _ -> true) gd2 in
  let rec go acc acalls1 acalls2 =
    match acalls1, acalls2 with
    | [], [] ->
      L.rev acc
    | GCall(vres1,asym1,arg1,od1)::acalls1, GCall(vres2,asym2,arg2,od2)::acalls2 ->
      if not (AdvSym.equal asym1 asym2) then
        tacerror
          "adversary calls in decisional assumption must match up: %a vs %a"
          AdvSym.pp asym1 AdvSym.pp asym2;
      if not (equal_list VarSym.equal vres1 vres2) then
        tacerror "decisional assumption return variables must match up: %a vs %a"
          (pp_list "," VarSym.pp) vres1 (pp_list "," VarSym.pp) vres2;
      if List.length od1 <> List.length od2 then
        tacerror "decisional assumption: not the same number of oracles";
      let mk_orcl (o1,vs1,od1,c1) (o2,vs2,od2,c2) = 
        if not (OrclSym.equal o1 o2) then
          tacerror
             "oracle name calls in decisional assumption must match up: %a vs %a"
             OrclSym.pp o1 OrclSym.pp o2;
        if not (equal_list VarSym.equal vs1 vs2) then
          tacerror "oracle parameter in decisional assumption must match up: %a vs %a"
            (pp_list "," VarSym.pp) vs1 (pp_list "," VarSym.pp) vs2;
        if c1 <> c2 then 
          tacerror "oracle counter in decisional assumption must match up: %a vs %a"
            pp_ocounter c1 pp_ocounter c2;
        match od1, od2 with
        | Oreg (lc1,r1), Oreg (lc2,r2) ->
          if not (Type.equal_ty r1.e_ty r2.e_ty) then
            tacerror "oracles should return expressions with equal type: %a vs %a"
               pp_expr r1 pp_expr r2;
          (o1, vs1, ((lc1,r1), (lc2,r2)), c1)
            
        | _ -> 
          tacerror "hybrid oracle not supported in decisional assumption"
        in
      let ad_ac = {
        ad_ac_sym   = asym1;
        ad_ac_lv    = vres1;
        ad_ac_args  = (arg1, arg2);
        ad_ac_orcls = L.map2 mk_orcl od1 od2;  
        } in

      go (ad_ac::acc) acalls1 acalls2
    | _, _ ->
      tacerror "invalid decisional assumption"
  in
  let assm = {
    ad_name    = name;
    ad_inf     = inf;
    ad_prefix1 = pref1;
    ad_prefix2 = pref2;
    ad_acalls  = go [] suff1 suff2;
    ad_symvars = symvars }
  in
  assm
  
let needed_vars_dec dir assm =
  let toSym se =
    Se.fold (fun e s -> VarSym.S.add (destr_V e) s) se VarSym.S.empty
  in
  let w1 = toSym(write_gcmds assm.ad_prefix1) in
  let w2 = toSym(write_gcmds assm.ad_prefix2) in
  let diff = if dir = LeftToRight then VarSym.S.diff w2 w1 else VarSym.S.diff w1 w2 in
  VarSym.S.elements diff

let private_vars_dec assm =
  L.fold_left
    (fun vset cmd ->
      match cmd with GSamp(v,_) -> Se.add (mk_V v) vset | GLet(v,_) -> Se.add
      (mk_V v) vset | _ -> tacerror "bad
      gcmd: %a" (pp_gcmd ~nonum:false) cmd)
    Se.empty
    (assm.ad_prefix1@assm.ad_prefix2)
    
let inst_dec ren assm =
  (* FIXME: Not_found should be an error *)
  let ren_v vs = try VarSym.M.find vs ren with Not_found -> vs in
  let ren_e = Game.subst_v_expr ren_v in
  let ren_ob ob = Game.subst_v_obody ren_v ob in
  let ren_o (o, vs, (b1, b2), c) = 
    let vs' = List.map ren_v vs in
    (o, vs', (ren_ob b1, ren_ob b2), c) in
  let ren_acall ad_ac =
     {ad_ac_sym   = ad_ac.ad_ac_sym;
      ad_ac_lv    = L.map ren_v ad_ac.ad_ac_lv;
      ad_ac_args  = ren_e (fst ad_ac.ad_ac_args),
                    ren_e (snd ad_ac.ad_ac_args);
      ad_ac_orcls = List.map ren_o ad_ac.ad_ac_orcls;
     } in

  let subst_g = Game.subst_v_gdef ren_v in
  { ad_name     = assm.ad_name;
    ad_inf      = assm.ad_inf;
    ad_prefix1  = subst_g assm.ad_prefix1;
    ad_prefix2  = subst_g assm.ad_prefix2;
    ad_acalls   = L.map ren_acall assm.ad_acalls; 
    ad_symvars  = L.map (L.map ren_v) assm.ad_symvars;
  }

(* ** Computational assumptions
 * ----------------------------------------------------------------------- *)

type assm_type = A_Succ | A_Adv

let pp_atype fmt = function
  | A_Succ -> pp_string fmt "Succ"
  | A_Adv  -> pp_string fmt "Adv"

type assm_comp = {
  ac_name       : string;       (* name of assumption *)
  ac_inf        : bool;         (* information-theoretic assumption *)
  ac_type       : assm_type;
  ac_prefix     : gdef;         (* prefix of assumption *)
  ac_event      : ev;           (* event expression *)
  ac_acalls     : (AdvSym.t * VarSym.t list * expr) list;
   (* adversary calls: asym, returned variables, and argument *)
  ac_symvars    : vs list list; (* symmetric in given variables *)
}

let pp_acall_comp fmt (asym,vs1,args1) =
  F.fprintf fmt "(%a) <- %a(%a)@\n"
    (pp_list "," VarSym.pp) vs1 AdvSym.pp asym pp_expr args1

let pp_assm_comp fmt ac =
  F.fprintf fmt "assumption %s (%a):@\n" ac.ac_name pp_atype ac.ac_type;
  F.fprintf fmt "prefix left:@\n%a@\n"  (pp_gdef ~nonum:false) ac.ac_prefix;
  F.fprintf fmt "adversary calls:@\n%a@\n" (pp_list "@\n" pp_acall_comp) ac.ac_acalls;
  F.fprintf fmt "symvars: %a@\n" (pp_list "; " (pp_list "," VarSym.pp)) ac.ac_symvars

let mk_assm_comp name inf atype gd ev sym_vars =
  ignore (Wf.wf_se Wf.NoCheckDivZero { se_gdef = gd; se_ev = ev});
  let (pref,suff) = L.partition (function GCall _ -> false | _ -> true) gd in
  let rec go acc acalls =
    match acalls with
    | [] ->
      L.rev acc
    | GCall(vres,asym,arg,od)::acalls ->
      if not (od = []) then
        tacerror "computational assumption with oracles not supported yet";
      go ((asym,vres,arg)::acc) acalls
    | _ ->
      tacerror "invalid computational assumption"
  in
  let ac = {
    ac_name       = name;
    ac_inf        = inf;
    ac_type       = atype;
    ac_prefix     = pref;
    ac_event      = ev;
    ac_acalls     = go [] suff;
    ac_symvars    = sym_vars;
  }
  in
  log_t (lazy (fsprintf "comp. assm. defined:@\n@[<hov 4>  %a@]" pp_assm_comp ac));
  ac

let private_vars_comp assm =
  L.fold_left
    (fun vset cmd ->
      match cmd with GSamp(v,_) -> Se.add (mk_V v) vset | _ -> assert false)
    Se.empty
    assm.ac_prefix

let inst_comp ren assm =
  let ren_v (x:VarSym.t) = try VarSym.M.find x ren with Not_found -> x in
  let ren_acall (asym,vres,e) = (asym, L.map ren_v vres, subst_v_expr ren_v e) in
  let subst_g = Game.subst_v_gdef ren_v in
  { assm with
    ac_prefix     = subst_g assm.ac_prefix;
    ac_event      = subst_v_expr ren_v assm.ac_event;
    ac_acalls     = L.map ren_acall assm.ac_acalls;
    ac_symvars    = L.map (L.map ren_v) assm.ac_symvars;
  }

