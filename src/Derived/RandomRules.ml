(* * Derived rules for dealing with random samplings. *)

(* ** Imports and abbreviations *)
open Abbrevs
open Util
open Nondet
open Type
open Syms
open Expr
open ExprUtils
open Game
open GameUtils
open Rules
open CoreTypes
open NormField
open ParserUtil

module Ht = Hashtbl
module CR = CoreRules
module T  = Tactic
module PT = ParserTypes

let mk_log level = mk_logger "Derived.RandomRules" level "RandomRules.ml"
let log_t  = mk_log Bolt.Level.TRACE
let _log_d = mk_log Bolt.Level.DEBUG
let log_i  = mk_log Bolt.Level.INFO

(* ** Derived rule for random sampling
 * ------------------------------------------------------------------- *)

(** Parse given context: bound name overshadows name in game *)
let parse_ctxt ts sec ty (sv,se) =
  let vmap = vmap_of_globals sec.se_gdef in
  let v = VarSym.mk sv ty in
  Hashtbl.add vmap (Unqual,sv) v;
  (v,expr_of_parse_expr vmap ts Unqual se)


(** find subexpressions of [e] that might yield useful contexts *)
let useful_subexprs se rv mgen e =
  let re = mk_V rv in

  (* compute possible divisors of e: variables occuring in e that are
     not chosen by adversary, avars cannot be made non-zero usually  *)
  let evars = e_vars e in
  let avars =
    Se.of_list
      (conc_map (function GCall(vs,_,_,_) -> L.map mk_V vs | _ -> [])
         se.se_gdef)
  in
  let fac_candidates =
    Se.elements (Se.diff evars avars)
    |> L.map (fun e -> if is_G e.e_ty then mk_GLog e else e)
    |> L.filter (fun fe -> equal_ty fe.e_ty mk_Fq)
    |> L.sort_uniq compare_expr
    |> move_front is_GLog
  in

  (* compute [e'] such that [e = e'*d + c] and [e'] contains [rv],
     random sampling can simplify [e] to [r*div + c] without dividing by d *)
  let get_coeff d =
    log_t (lazy (fsprintf "trying factor_out=%a" pp_expr d));
    match polys_of_field_expr (CAS.norm id e) with
    | (fe, None) ->
      begin try
        let (g,_h) = factor_out d fe in
        let e' = exp_of_poly g in
        guard (not (equal_expr re e')) >>= fun _ ->
        guard (Se.mem re (e_vars e')) >>= fun _ ->
        log_t (lazy (fsprintf "@[<hov 2>transform expr=@[<hov 2>%a@]@ -> @[<hov 2>%a@]@\n%!@]"
                       pp_expr e pp_expr e'));
        ret e'
      with
        Not_found -> mempty
      end
    | _ -> mempty
  in

  (* if a generator [g1] is given, prefer coefficients of [g1], i.e., we
     want to simplify [g1^(r*a + b)] to [g1^r] rather than [g^r]. *)
  match mgen with
  | None    -> mplus (ret e) (msum (L.map get_coeff fac_candidates))
  | Some ge ->
    let lge = if is_G ge.e_ty then  mk_GLog ge else ge in
    let fac_candidates =
      L.filter (fun e -> not (equal_expr e lge)) fac_candidates
    in
    msum ((get_coeff lge)::(ret e)::(L.map get_coeff fac_candidates))

(** Compute useful contexts from occurences of random variable *)
let contexts se rv mgen =
  let re = mk_V rv in

  (* collect all expressions containing rv *)
  let es = ref [] in  (* we need order of occurence in game *)
  let add_subterms e =
    e_iter_ty_maximal mk_Fq
      (fun fe ->
        let maybe_add fe =
          if not (is_V fe) && Se.mem re (e_vars fe) && not (L.mem fe !es)
          then es := fe::!es
        in
        if is_Ifte fe
        then (let (_,e1,e2) = destr_Ifte fe in maybe_add e1; maybe_add e2)
        else maybe_add fe)
      e
  in
  iter_gdef_exp add_subterms se.se_gdef;
  add_subterms se.se_ev;
  mconcat (L.rev !es) >>= fun e ->
  log_t (lazy (fsprintf "@[<hov 2>possible expr=@ @[<hov 2>%a@]@]@\n%!" pp_expr e));

  (* find useful subexpressions of e (in the right order) *)
  useful_subexprs se rv mgen e

let contexts_xor se rv =
  let re = mk_V rv in

  (* collect all expressions containing rv *)
  let es = ref [] in  (* we need order of occurence in game *)
  let add_subterms e =
    e_iter
      (fun e ->
        if is_Xor e && Se.mem re (e_vars e) && not (L.mem e !es) then es := e::!es)
      e
  in
  iter_gdef_exp add_subterms se.se_gdef;
  add_subterms se.se_ev;
  !es

let check_tannot ts ty mty =
  match mty with
  | None -> ()
  | Some pty ->
    let ety = ty_of_parse_ty ts pty in
    if not (equal_ty ty ety) then
      tacerror "wrong type annotation: expected %a, got %a"
        pp_ty ty pp_ty ety


(** rnd tactic that tries out useful contexts for given random variable *)
let t_rnd_pos ts mctxt1 mctxt2 rv mgen i ju =
  let se = ju.ju_se in
  let rv_ty = rv.VarSym.ty in
  let deduc = DeducField.solve_mixed_type in
  let parse v_ty (sv,se') = parse_ctxt ts se v_ty (sv,se') in
  (match mctxt1, mctxt2 with
  | Some (sv1,mt1,se1), Some (sv2,mt2,se2) ->
    let v2_ty = rv_ty in
    check_tannot ts v2_ty mt2;
    let (v2,e2) = parse v2_ty (sv2,se2) in
    let v1_ty = e2.e_ty in
    check_tannot ts v1_ty mt1;
    let (v1,e1) = parse v1_ty (sv1,se1) in
    ret ((v1,e1),(v2,e2))
  | None, Some (sv2,mt2,se2) ->
    let v2_ty = rv_ty in
    check_tannot ts v2_ty mt2;
    let (v2,e2) = parse v2_ty (sv2,se2) in
    ret (deduc e2 v2,(v2,e2))
  | Some (sv1,mt1,se1), None ->
    let v1_ty = O.map_default (ty_of_parse_ty ts) rv_ty mt1  in
    let (v1,e1) = parse v1_ty (sv1,se1) in
    ret ((v1,e1), deduc e1 v1)
  | None, None ->
    let ctxts_fq =
      run (-1) (contexts se rv mgen)
      |> L.map NormUtils.norm_expr_nice
      |> L.unique ~eq:equal_expr
      |> L.filter (fun e -> VarSym.S.for_all (fun v -> v.VarSym.qual = Unqual) (vars_expr e))
      (* FIXME: for bycrush, we exclude contexts rv -> - rv *)
      |> L.filter (fun e -> (not (equal_expr (mk_FOpp (mk_V rv)) e)))
    in
    let ctxts = ctxts_fq @ contexts_xor se rv in
    log_i (lazy (fsprintf "context_num: %i v=%a %a" (L.length ctxts)
                   pp_expr (mk_V rv) (pp_list "," pp_expr) ctxts));
    let e2s =
      ctxts
      |> L.sort (fun e1 e2 -> compare_pair compare compare_expr (e_size e1,e1) (e_size e2,e2))
    in
    mconcat (L.map (fun e2 -> (rv,e2)) e2s) >>= fun (v2,e2) ->
    ret (deduc e2 v2, (v2,e2))
  ) >>= fun ((v1,e1),(v2,e2)) ->
  log_t (lazy (fsprintf (  "@[<hov 2>t_rnd_pos: trying@ @[<hov 2>%a@] -> @[<hov 2>%a@]@ "
                         ^^"with inverse@ @[<hov 2>%a@] -> @[<hov 2>%a@]")
                 VarSym.pp v1 pp_expr e1 VarSym.pp v2 pp_expr e2));
  try
    ignore (CR.r_rnd i (v1,e1) (v2,e2) ju);
    T.t_rnd i (v1,e1) (v2,e2) ju
  with
  (* try different strategies to prevent failures by applying other
     tactics beforehand *)
  | Invalid_rule s ->
    mfail (lazy s)
  | Wf.Wf_var_undef(vs,e,def_vars) ->
    let ls =
      lazy
        (fsprintf (  "@[<hov 2>t_rnd_pos: variable %a@ undefined"
                   ^^" in @[<hov 2>%a@],@ not in defined variables @[<hov 2>%a@]")
           VarSym.pp vs pp_expr e
           (pp_list "," VarSym.pp) (VarSym.S.elements def_vars)) in
    log_i ls;
    mfail ls
  | Wf.Wf_div_zero (ze::_ as es) ->
    let ls =
      lazy
        (fsprintf "t_rnd_pos: non-zero required for %a"
           (pp_list ",@," pp_expr) es)
    in
    log_i ls;
    let nz_in_ev () =
      let wfs = Wf.wf_gdef Wf.NoCheckDivZero se.se_gdef in
      try
        let test_ev =
          mk_Land [se.se_ev; mk_Eq (mk_FDiv mk_FOne ze) mk_FOne]
        in
        Wf.wf_expr Wf.CheckDivZero wfs test_ev;
        true
      with
        Wf.Wf_div_zero _ -> false
    in
    if not (Se.mem (mk_V rv) (read_gcmds se.se_gdef)) && nz_in_ev () then (
      (* try to apply (d=0)?1:d trick here:
         We assume c2 is of the form r*ze + a *)
      let gze = mk_Ifte (mk_Eq ze mk_FZ) mk_FOne ze in
      let re  = mk_V rv in
      let e2' =
        NormUtils.norm_expr_nice
          (e_replace re (mk_FMult [mk_FDiv re ze; gze]) e2)
      in
      let e1' = DeducField.solve_fq_vars_known e2' v2 in
      let simp_guard ju =
        let ev_idx = 0 in
        (RewriteRules.t_let_unfold (L.length ju.ju_se.se_gdef - 1) @>
         T.t_rw_ev ev_idx LeftToRight @>
         RewriteRules.t_subst 0 (mk_Ifte mk_False mk_FOne ze) ze None @>
         RewriteRules.t_norm_nounfold @>
         T.t_remove_ev [ev_idx]) ju
      in
      let discharge ju =
        SimpRules.t_simp true 20 ju
      in
      (T.t_rnd i (v2,e1') (v2,e2') @>
       T.t_case_ev ~allow_existing:true (mk_Eq ze mk_FZ) @>>
       [ discharge; simp_guard ]) ju
    ) else (
      mfail ls
    )

(** rnd tactic that tries all positions and contexts if none are given *)
let t_rnd_maybe ?i_rvars:(irvs=VarSym.S.empty) ts exact mi mctx1 mctx2 mgen ju =
  let se = ju.ju_se in

  (* try all sampling positions if none is given *)
  let samps = samplings se.se_gdef in
  (match mi with
  | Some i -> ret i
  | None   -> mconcat (L.map fst samps)
  ) >>= fun i ->
  let (rv,(_,es)) = L.assoc i samps in
  let vs = vars_dexc rv es in
  guard (not (VarSym.S.mem rv irvs)) >>= fun _ ->
  log_t (lazy "###############################");
  log_t (lazy (fsprintf "t_rnd_maybe %i\n%!" (i + 1)));
  log_t (lazy (fsprintf "sampling: %i, %a@\n%!" (i+1) VarSym.pp rv));

  (* move (if requested) and continue with fixed position *)
  let rnd i = t_rnd_pos ts mctx1 mctx2 rv mgen i in
  if exact then rnd i ju
  else
    (t_move_max ToEnd i vs @>= fun i ->
     t_move_others_max ToFront i @>= fun i ->
     rnd i)
    ju

(* ** Random rule in oracle
 * ----------------------------------------------------------------------- *)

(** Parse given context: bound name overshadows name in game *)
let parse_ctxt_oracle ts opos sec ty (sv,se) =
  let vmap = vmap_in_orcl sec opos in
  let _, seoc = get_se_octxt sec opos in
  let oname = Id.name seoc.seoc_osym.OrclSym.id in
  (* bound name overshadows names in game *)
  let v = VarSym.mk sv ty in
  Hashtbl.add vmap (Unqual,sv) v;
  (v,expr_of_parse_expr vmap ts (Qual oname) se)


(** [t_rnd_oracle_maybe] tries all useful contexts if none are given *)
let t_rnd_oracle_maybe ?i_rvars:(irvs=VarSym.S.empty) ts mopos mctx1 mctx2 ju =
  let se = ju.ju_se in
  let osamps = osamplings se.se_gdef in
  let deduc = DeducField.solve_mixed_type in
  (match mopos with
  | Some opos -> ret opos
  | None      -> mconcat (L.map fst osamps)
  ) >>= fun ((i,j,k,ootype) as op) ->
  let (rv,(rv_ty,_)) = L.assoc op osamps in
  let parse v_ty (sv,se') = parse_ctxt_oracle ts op se v_ty (sv,se') in
  guard (not (VarSym.S.mem rv irvs)) >>= fun _ ->
  log_t (lazy (fsprintf "###############################\n%!"));
  log_t (lazy (fsprintf "t_rnd_oracle_maybe (%i,%i,%i)\n%!" i j k));
  (match mctx1, mctx2 with
  | Some (sv1,mt1,se1), Some (sv2,mt2,se2) ->
    let v2_ty = rv_ty in
    check_tannot ts v2_ty mt2;
    let (v2,e2) = parse v2_ty (sv2,se2) in
    let v1_ty = e2.e_ty in
    check_tannot ts v1_ty mt1;
    let (v1,e1) = parse v1_ty (sv1,se1) in
    ret ((v1,e1),(v2,e2))
  | None, Some (sv2,mt2,se2) ->
    let v2_ty = rv_ty in
    check_tannot ts v2_ty mt2;
    let (v2,e2) = parse v2_ty (sv2,se2) in
    ret (deduc e2 v2,(v2,e2))
  | Some (sv1,mt1,se1), None ->
    let v1_ty = O.map_default (ty_of_parse_ty ts) rv_ty mt1  in
    let (v1,e1) = parse v1_ty (sv1,se1) in
    ret ((v1,e1), deduc e1 v1)
  | None, None ->
    let e2s =
      run (-1) (contexts se rv None) |> L.map NormUtils.norm_expr_nice |> L.sort_uniq compare_expr
    in
    mconcat (L.map (fun e2 -> (rv,e2)) e2s) >>= fun (v2,e2) ->
    ret (deduc e2 v2, (v2,e2))
    (* FIXME: for CS bycrush, we excluded contexts rv -> - rv *)
  ) >>= fun ((v1,e1),(v2,e2)) ->
  T.t_rnd_oracle (i,j,k,ootype) (v1,e1) (v2,e2) ju
